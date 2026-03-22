//! Utilities for encoding bytes/UTF-8 text into ring elements.
//!
//! This module provides two related but distinct encodings for turning a byte
//! string into a sequence of `RingElement`s with a given `modulus`:
//!
//! - Bit-packing (`encode_bytes` / `decode_bytes`):
//!   Packs the input bitstream into chunks of b = floor(log2(modulus)) bits.
//!   Every produced element satisfies value < 2^b <= modulus, so some residues
//!   are intentionally unused when the modulus is not a power of two.
//!   This format does not include the original byte length.
//!
//! - Length-delimited base-m transduction
//!   (`encode_bytes_base_m_len` / `decode_bytes_base_m_len`):
//!   Encodes the byte length and a fixed rANS state as base-modulus digits,
//!   then converts the byte stream into base-modulus payload digits using a
//!   uniform rANS transducer. Every produced digit satisfies digit < modulus,
//!   so it uses all residues. Decoding is length-delimited and ignores trailing
//!   elements.
//!
//! ## Target behavior (base-m-len variant)
//!
//! - Uses all residues: every emitted `RingElement` satisfies value < modulus,
//!   with no "[0, 2^b)" restriction.
//! - Near-linear time: amortized O(1) work per input byte, plus a constant-size
//!   header (2 * k digits for a fixed k determined by `modulus`).
//! - Same public API: the public `encode_bytes_base_m_len` /
//!   `decode_bytes_base_m_len` signatures and
//!   `encode_text_base_m_len` / `decode_text_base_m_len` behavior are unchanged.
//! - Padding tolerance: appending extra elements at the end (for example, block
//!   padding) does not affect decoding; the decoder stops after emitting the
//!   byte count from the length prefix.
//!
//! ## Design: uniform rANS as a radix transducer
//!
//! Treat each input byte as a uniform symbol (frequency = 1 over 256 symbols).
//! The symbol update is:
//!
//! - encode: x = x * 256 + byte
//! - decode: byte = x % 256; x = x / 256
//!
//! Renormalization uses base = modulus, so every emitted digit is a valid ring
//! residue (digit < modulus). The stream stores a fixed-size initial state
//! immediately after the length prefix so decoding can proceed FIFO
//! (left-to-right) and ignore any trailing padding.
//!
//! ## Future work
//!
//! Investigate non-uniform rANS as a radix transducer to incorporate empirical
//! byte distributions while retaining the base-modulus digit stream interface.
//!
//! The bitstream in `encode_bytes` is packed little-endian: earlier bytes
//! occupy lower bits of the internal buffer and are emitted first.
//!
//! Important limitations (bit-packing variant):
//!
//! - The encoding does not include the original byte length. For some parameter
//!   choices (notably when b > 8), decoding may yield extra trailing 0x00 bytes
//!   that come from zero-padding the final partial chunk. If you need exact
//!   round-trips, store the original length separately and truncate after
//!   decoding.
//! - Decoding assumes elements are in the canonical range produced by this
//!   module (each element value fits in b bits). If you modify elements via
//!   ring arithmetic, decoding will generally not recover the original bytes.
//!
//! # References (ANS / rANS)
//!
//! - J. Duda, "Asymmetric numeral systems: entropy coding combining speed of
//!   Huffman coding with compression rate of arithmetic coding",
//!   <https://arxiv.org/abs/1311.2540>
//! - F. Giesen, "rANS notes":
//!   <https://fgiesen.wordpress.com/2014/02/02/rans-notes/>
//! - F. Giesen, "rANS with static probability distributions":
//!   <https://fgiesen.wordpress.com/2014/02/18/rans-with-static-probability-distributions/>
//! - Y. Collet, "Finite State Entropy, a new breed of entropy coders" (FSE/tANS):
//!   <https://fastcompression.blogspot.com/2013/12/finite-state-entropy-new-breed-of.html>

use sym_adv_ring::RingElement;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Utf8EncodingType {
    LengthDelimitedBaseMTransduction,
    BitPacking,
}

enum Utf8EncodingTypeInner {
    LengthDelimitedBaseMTransduction {
        length_prefix_digits: usize,
        decoder_lower_bound: u64,
        encoder_threshold: u64,
    },
    BitPacking,
}

pub struct Utf8Encoding {
    modulus: u64,
    encoding_type: Utf8EncodingTypeInner,
}

impl Utf8Encoding {
    /// Builds an encoding configuration for the provided `modulus`.
    ///
    /// # Errors
    ///
    /// - Returns [`EncodingError::ModulusTooSmall`] if `modulus < 2`.
    /// - Returns [`EncodingError::DecodingError`] when base-m rANS parameters are
    ///   invalid for the provided `modulus`.
    pub fn try_from(modulus: u64, encoding_type: Utf8EncodingType) -> Result<Self, EncodingError> {
        if modulus < 2 {
            return Err(EncodingError::ModulusTooSmall);
        }

        Ok(Self {
            modulus,
            encoding_type: Self::build_inner_encoding_type(modulus, encoding_type)?,
        })
    }

    fn build_inner_encoding_type(
        modulus: u64,
        encoding_type: Utf8EncodingType,
    ) -> Result<Utf8EncodingTypeInner, EncodingError> {
        match encoding_type {
            Utf8EncodingType::LengthDelimitedBaseMTransduction => {
                let (decoder_lower_bound, encoder_threshold) = Self::rans_params(modulus)?;

                Ok(Utf8EncodingTypeInner::LengthDelimitedBaseMTransduction {
                    length_prefix_digits: Self::length_prefix_digits(modulus),
                    decoder_lower_bound,
                    encoder_threshold,
                })
            }
            Utf8EncodingType::BitPacking => Ok(Utf8EncodingTypeInner::BitPacking),
        }
    }
}

impl Utf8Encoding {
    /// Returns the fixed base-`modulus` digit count used for u64 prefixes.
    ///
    /// This computes the smallest `k` such that `modulus^k >= 2^64`. The
    /// length-delimited `*_base_m_len` format encodes both the byte length and the
    /// rANS state using exactly `k` base-`modulus` digits, which makes the stream
    /// layout self-delimiting (`length || state || payload`) without separators.
    ///
    /// Digits are interpreted little-endian (least significant digit first).
    ///
    /// # Math
    ///
    /// Let m = modulus (with m >= 2). We choose the minimal digit count k >= 0 such
    /// that every 64-bit value fits into k base-m digits:
    ///
    ///   k = min { k in N0 : m^k >= 2^64 }.
    ///
    /// Equivalently:
    ///
    ///   k = ceil( `log_m(2^64)` )
    ///     = ceil( log(2^64) / log(m) ).
    ///
    /// This guarantees that any x in [0, 2^64 - 1] can be represented using exactly
    /// k base-m digits (padding with leading zero digits as needed).
    ///
    /// # Complexity
    ///
    /// Runs in O(k) time and O(1) extra space, where k is the returned digit count
    /// (the number of times we multiply by `modulus` until reaching 2^64).
    ///
    /// In terms of `modulus = m` (m >= 2), k = `ceil(log_m(2^64))`, so the loop runs
    /// about ceil(64 / log2(m)) iterations (worst case at m = 2 gives k = 64).
    fn length_prefix_digits(modulus: u64) -> usize {
        let target: u128 = 1u128 << 64;
        let base: u128 = u128::from(modulus);
        let mut pow: u128 = 1;
        let mut k: usize = 0;
        while pow < target {
            pow = pow.saturating_mul(base);
            k += 1;
        }

        k
    }

    /// Chooses renormalization parameters for the uniform (256-symbol) rANS transducer.
    ///
    /// The `*_base_m_len` encoding treats bytes as symbols in a uniform 256-ary
    /// alphabet and produces payload digits in radix `modulus` (so every digit is
    /// `< modulus`). The internal state `x` is maintained in a `u64`.
    ///
    /// This function returns `(L, x_max)`:
    /// - `L` is a decoder lower bound (chosen as a multiple of 256),
    /// - `x_max = (L / 256) * modulus` is an encoder threshold.
    ///
    /// The encoder emits base-`modulus` digits while `x >= x_max` to ensure the
    /// update `x = x * 256 + byte` cannot overflow `u64`. The decoder performs the
    /// inverse operation by consuming digits while `x < L`.
    ///
    /// # Errors
    ///
    /// - Returns [`EncodingError::DecodingError`] if `modulus` is so large that no
    ///   valid `L >= 256` can be chosen while keeping the state in `u64`.
    fn rans_params(modulus: u64) -> Result<(u64, u64), EncodingError> {
        let max_l = u64::MAX / modulus;
        let l = (max_l / 256) * 256;
        if l < 256 {
            return Err(EncodingError::DecodingError(
                "Modulus too large for base-m-len encoding".to_string(),
            ));
        }

        let x_max_u128 = u128::from(l / 256) * u128::from(modulus);
        if x_max_u128 > u128::from(u64::MAX) {
            return Err(EncodingError::DecodingError(
                "Invalid rANS parameters".to_string(),
            ));
        }

        let x_max = u64::try_from(x_max_u128)
            .map_err(|_| EncodingError::DecodingError("Invalid rANS parameters".to_string()))?;
        Ok((l, x_max))
    }

    /// Encodes a `u64` as exactly `k` base-`modulus` digits (little-endian).
    ///
    /// Here `k = length_prefix_digits(modulus)`, so every `u64` fits. The returned
    /// vector always has length `k`; most-significant digits are `0` when `value` is
    /// small.
    fn encode_u64_base_m_fixed(&self, value: u64) -> Vec<u64> {
        let Utf8EncodingTypeInner::LengthDelimitedBaseMTransduction {
            length_prefix_digits,
            ..
        } = self.encoding_type
        else {
            unreachable!()
        };

        let mut digits = Vec::with_capacity(length_prefix_digits);
        let mut v = value;
        for _ in 0..length_prefix_digits {
            digits.push(v % self.modulus);
            v /= self.modulus;
        }

        digits
    }

    /// Decodes a fixed-width base-`modulus` digit sequence (little-endian) into a `u64`.
    ///
    /// Each digit must satisfy `digit < modulus`. The digit slice is typically of
    /// length `k = length_prefix_digits(modulus)`, as produced by
    /// [`encode_u64_base_m_fixed`].
    ///
    /// # Errors
    ///
    /// - Returns [`EncodingError::DecodingError`] if any digit is out of range or if
    ///   the decoded value does not fit in `u64`.
    fn decode_u64_base_m_fixed(&self, digits: &[u64]) -> Result<u64, EncodingError> {
        let mut value: u128 = 0;
        let mut pow: u128 = 1;
        let base: u128 = u128::from(self.modulus);
        for &d in digits {
            if d >= self.modulus {
                return Err(EncodingError::DecodingError(
                    "Invalid length prefix digit".to_string(),
                ));
            }
            value += u128::from(d) * pow;
            pow = pow.saturating_mul(base);
        }

        if value > u128::from(u64::MAX) {
            return Err(EncodingError::DecodingError(
                "Decoded length exceeds u64".to_string(),
            ));
        }

        u64::try_from(value)
            .map_err(|_| EncodingError::DecodingError("Decoded length exceeds u64".to_string()))
    }

    /// Uniform rANS encoder for bytes, emitting digits in radix `modulus`.
    ///
    /// Given `bytes`, this returns a pair `(state, stream_digits)` such that
    /// [`rans_decode_uniform_bytes_base_m`] can reconstruct the original bytes when
    /// provided with:
    /// - the original `len = bytes.len()`,
    /// - the returned `state` (encoded separately as fixed-width base-`modulus`
    ///   digits),
    /// - the returned `stream_digits` as the payload digit stream.
    ///
    /// Implementation details:
    /// - Symbols are bytes with a *uniform* distribution, so the rANS update reduces
    ///   to `x = x * 256 + byte`.
    /// - Renormalization emits digits in radix `modulus`, ensuring every output
    ///   digit is `< modulus` (i.e., all residues are available).
    /// - Bytes are processed in reverse order, as is standard for streaming rANS.
    ///
    fn rans_encode_uniform_bytes_base_m(&self, bytes: &[u8]) -> (u64, Vec<u64>) {
        let Utf8EncodingTypeInner::LengthDelimitedBaseMTransduction {
            decoder_lower_bound,
            encoder_threshold,
            ..
        } = self.encoding_type
        else {
            unreachable!()
        };

        let mut x = decoder_lower_bound;
        let mut stream_digits = Vec::new();

        for &b in bytes.iter().rev() {
            while x >= encoder_threshold {
                stream_digits.push(x % self.modulus);
                x /= self.modulus;
            }

            x = x * 256 + u64::from(b);
        }

        stream_digits.reverse();
        (x, stream_digits)
    }

    /// Uniform rANS decoder for bytes, consuming digits in radix `modulus`.
    ///
    /// This is the inverse of [`rans_encode_uniform_bytes_base_m`]. It reconstructs
    /// exactly `len` bytes from an initial `state` and a digit stream `stream`.
    ///
    /// In the uniform 256-symbol case, symbol extraction corresponds to:
    /// - decode: `byte = x % 256; x = x / 256`
    ///
    /// Only as many payload digits as necessary are consumed; any remaining trailing
    /// elements in `stream` are ignored. This makes the overall `*_base_m_len`
    /// decoding robust to zero-padding or garbage appended at the end.
    ///
    /// # Errors
    ///
    /// Returns [`EncodingError::DecodingError`] if:
    /// - `state` is invalid for the chosen parameters,
    /// - there are not enough payload digits to decode `len` bytes,
    /// - any payload digit is out of range (`>= modulus`), or
    /// - the reconstructed internal state would overflow `u64`.
    fn rans_decode_uniform_bytes_base_m(
        &self,
        len: usize,
        state: u64,
        stream: &[RingElement],
    ) -> Result<Vec<u8>, EncodingError> {
        let Utf8EncodingTypeInner::LengthDelimitedBaseMTransduction {
            decoder_lower_bound,
            ..
        } = self.encoding_type
        else {
            unreachable!()
        };

        if len == 0 {
            return Ok(Vec::new());
        }

        if state < decoder_lower_bound {
            return Err(EncodingError::DecodingError(
                "Invalid rANS state".to_string(),
            ));
        }

        let mut x = state;
        let mut out = Vec::with_capacity(len);
        let mut i = 0usize;

        for _ in 0..len {
            out.push(
                u8::try_from(x & u64::from(u8::MAX))
                    .expect("low 8 bits of the rANS state must fit in u8"),
            );
            x >>= 8;

            while x < decoder_lower_bound {
                let d = stream.get(i).ok_or_else(|| {
                    EncodingError::DecodingError("Not enough payload digits".to_string())
                })?;
                let dv = d.value();
                if dv >= self.modulus {
                    return Err(EncodingError::DecodingError(
                        "Invalid payload digit".to_string(),
                    ));
                }
                let new_x = u128::from(x) * u128::from(self.modulus) + u128::from(dv);
                if new_x > u128::from(u64::MAX) {
                    return Err(EncodingError::DecodingError(
                        "Invalid rANS state".to_string(),
                    ));
                }
                x = u64::try_from(new_x)
                    .map_err(|_| EncodingError::DecodingError("Invalid rANS state".to_string()))?;
                i += 1;
            }
        }

        Ok(out)
    }

    /// Encodes bytes into base-`modulus` digits with an embedded byte length.
    ///
    /// This encoding is **length-delimited** and **self-contained**: the output
    /// embeds the original byte length (as a fixed-width base-`modulus` prefix) and
    /// uses a uniform rANS transducer to convert the bytes into payload digits, all
    /// strictly `< modulus`.
    ///
    /// # Target behavior
    ///
    /// - **Uses all residues**: digits are only required to satisfy `value < modulus`
    ///   (there is no `"[0, 2^b)"` restriction as in [`encode_bytes`]).
    /// - **Near-linear time**: amortized O(1) work per input byte, plus a constant-size
    ///   header for the given modulus.
    /// - **Padding tolerance**: trailing elements do not affect decoding because the
    ///   decoded length is explicit.
    /// - **Same public API**: this preserves the existing function signature and
    ///   high-level behavior (but the on-wire representation is not backward compatible).
    ///
    /// # Wire format
    ///
    /// For `k = length_prefix_digits(modulus)`, the returned element sequence is:
    ///
    /// - `k` digits: `len` as a `u64` in base `modulus` (little-endian),
    /// - `k` digits: `state` as a `u64` in base `modulus` (little-endian),
    /// - `n` digits: payload stream digits produced by uniform rANS (each `< modulus`).
    ///
    /// The payload digit count `n` depends on `bytes.len()` and `modulus`.
    ///
    /// The rANS `state` is placed immediately after the length prefix so decoding can
    /// proceed FIFO (left-to-right): read `len`, read `state`, then consume as many
    /// payload digits as needed to emit exactly `len` bytes.
    ///
    /// # Decoding behavior
    ///
    /// [`decode_bytes_base_m_len`] uses the embedded `len` to decode exactly that
    /// many bytes and ignores any trailing elements beyond what is required. This
    /// makes the representation robust to padding or garbage appended at the end.
    ///
    /// # Complexity
    ///
    /// Near-linear in `bytes.len()` (amortized O(1) renormalization per byte),
    /// avoiding quadratic base-conversion of large payloads.
    ///
    /// # Compatibility
    ///
    /// This is **not** compatible with older `*_base_m_len` encodings that used a
    /// different payload conversion scheme.
    ///
    /// # Errors
    ///
    /// - Returns [`EncodingError::ModulusTooSmall`] if `modulus < 2`.
    /// - Returns [`EncodingError::DecodingError`] if the byte length does not fit in
    ///   `u64` or if valid rANS parameters cannot be chosen for the given modulus.
    pub fn encode_bytes_base_m_len(&self, bytes: &[u8]) -> Result<Vec<RingElement>, EncodingError> {
        let len_u64 = u64::try_from(bytes.len()).map_err(|_| {
            EncodingError::DecodingError("Input length does not fit in u64".to_string())
        })?;

        let mut result: Vec<RingElement> = Vec::new();

        let len_digits_le = self.encode_u64_base_m_fixed(len_u64);
        result.extend(
            len_digits_le
                .into_iter()
                .map(|d| RingElement::new(d, self.modulus)),
        );

        let (state, stream_digits) = self.rans_encode_uniform_bytes_base_m(bytes);

        let state_digits_le = self.encode_u64_base_m_fixed(state);
        result.extend(
            state_digits_le
                .into_iter()
                .map(|d| RingElement::new(d, self.modulus)),
        );

        result.extend(
            stream_digits
                .into_iter()
                .map(|d| RingElement::new(d, self.modulus)),
        );

        Ok(result)
    }

    /// Decodes bytes encoded by [`encode_bytes_base_m_len`].
    ///
    /// This parses the fixed-width base-`modulus` `len` prefix and `state`, then
    /// uses the uniform rANS decoder to reconstruct exactly `len` bytes.
    ///
    /// Any trailing elements after the consumed payload are ignored, so appending
    /// zero-padding or garbage does not change the decoded result.
    ///
    /// Decoding is FIFO: it reads the `len` prefix, then the fixed-width `state`, and
    /// then consumes only as many payload digits as needed to emit `len` bytes.
    ///
    /// # Errors
    ///
    /// - Returns [`EncodingError::DecodingError`] if the stream is malformed (not
    ///   enough prefix/payload digits, out-of-range digits, invalid state, or length
    ///   that does not fit in `usize`).
    pub fn decode_bytes_base_m_len(
        &self,
        elements: &[RingElement],
    ) -> Result<Vec<u8>, EncodingError> {
        let Utf8EncodingTypeInner::LengthDelimitedBaseMTransduction {
            length_prefix_digits,
            ..
        } = self.encoding_type
        else {
            unreachable!()
        };

        if elements.len() < length_prefix_digits {
            return Err(EncodingError::DecodingError(
                "Not enough elements for length prefix".to_string(),
            ));
        }

        let len_digits: Vec<u64> = elements[..length_prefix_digits]
            .iter()
            .map(RingElement::value)
            .collect();
        let len_u64 = self.decode_u64_base_m_fixed(&len_digits)?;
        let len_usize = usize::try_from(len_u64).map_err(|_| {
            EncodingError::DecodingError("Decoded length does not fit in usize".to_string())
        })?;

        if len_usize == 0 {
            return Ok(Vec::new());
        }

        if elements.len() < 2 * length_prefix_digits {
            return Err(EncodingError::DecodingError(
                "Not enough elements for rANS state".to_string(),
            ));
        }

        let state_digits: Vec<u64> = elements[length_prefix_digits..2 * length_prefix_digits]
            .iter()
            .map(RingElement::value)
            .collect();
        let state = self.decode_u64_base_m_fixed(&state_digits)?;

        let payload_stream = &elements[2 * length_prefix_digits..];
        self.rans_decode_uniform_bytes_base_m(len_usize, state, payload_stream)
    }

    /// Encodes a UTF-8 string using [`encode_bytes_base_m_len`].
    ///
    /// # Errors
    ///
    /// - Propagates any error returned by [`Self::encode_bytes_base_m_len`].
    pub fn encode_text_base_m_len(&self, text: &str) -> Result<Vec<RingElement>, EncodingError> {
        self.encode_bytes_base_m_len(text.as_bytes())
    }

    /// Decodes text encoded by [`encode_text_base_m_len`].
    ///
    /// This is [`decode_bytes_base_m_len`] followed by UTF-8 validation.
    ///
    /// # Errors
    ///
    /// - Returns [`EncodingError::DecodingError`] if the element stream is malformed
    ///   or the decoded bytes are not valid UTF-8.
    pub fn decode_text_base_m_len(
        &self,
        elements: &[RingElement],
    ) -> Result<String, EncodingError> {
        let bytes = self.decode_bytes_base_m_len(elements)?;
        String::from_utf8(bytes).map_err(|e| EncodingError::DecodingError(e.to_string()))
    }
}

impl Utf8Encoding {
    /// Computes how many payload bits can be stored per element for a given modulus.
    ///
    /// Returns `b = floor(log2(modulus))`. With this choice,
    /// every `b`-bit value is guaranteed to be `< modulus`, even when `modulus` is
    /// not a power of two.
    fn bits_per_element(&self) -> usize {
        usize::try_from(self.modulus.ilog2()).expect("u32 bit width must fit in usize")
    }

    /// Encodes a byte slice into a sequence of [`RingElement`]s.
    ///
    /// The input bytes are treated as a little-endian bitstream and packed into
    /// chunks of `b` bits, where `b = floor(log2(modulus))`. Each chunk becomes the
    /// `value` of a `RingElement` with the provided `modulus`.
    ///
    /// This encoding uses only values in the range `[0, 2^b)`, which is always a
    /// subset of the ring when `modulus` is not a power of two.
    ///
    /// # Notes
    ///
    /// - The output does not carry the original byte length. If the final chunk is
    ///   only partially filled, it is emitted with implicit zero-padding in the
    ///   high bits. For some moduli (notably when `b > 8`), this can cause decoding
    ///   to produce extra trailing `0x00` bytes unless you truncate to the original
    ///   length.
    #[must_use]
    pub fn encode_bytes(&self, bytes: &[u8]) -> Vec<RingElement> {
        let bits_per_elem = self.bits_per_element();

        let mut result = Vec::new();
        let mut bit_buffer: u64 = 0;
        let mut bits_in_buffer: usize = 0;

        for &byte in bytes {
            bit_buffer |= u64::from(byte) << bits_in_buffer;
            bits_in_buffer += 8;

            while bits_in_buffer >= bits_per_elem {
                let mask = (1u64 << bits_per_elem) - 1;
                let value = bit_buffer & mask;

                result.push(RingElement::new(value, self.modulus));

                bit_buffer >>= bits_per_elem;
                bits_in_buffer -= bits_per_elem;
            }
        }

        if bits_in_buffer > 0 {
            result.push(RingElement::new(bit_buffer, self.modulus));
        }

        result
    }

    /// Decodes a sequence of [`RingElement`]s back into bytes.
    ///
    /// This reconstructs the same little-endian bitstream produced by
    /// [`encode_bytes`], assuming `b = floor(log2(modulus))` bits of payload per
    /// element and emitting 8-bit bytes from the stream.
    ///
    /// # Notes
    ///
    /// - This function does not validate that the provided `modulus` matches the
    ///   modulus stored in each element; they must agree for meaningful results.
    /// - This function assumes each element value fits in `b` bits (i.e., it lies
    ///   in `[0, 2^b)`) as produced by [`encode_bytes`]. If elements were modified
    ///   (or originate elsewhere), higher bits can leak into the reconstructed byte
    ///   stream.
    /// - Because the encoding does not include the original length, decoding may
    ///   yield extra trailing `0x00` bytes for some parameter choices; truncate to
    ///   the known original length when exact recovery is required.
    ///
    /// # Panics
    ///
    /// Panics only if an internal invariant is violated and extracting the low
    /// 8 bits of the bit buffer fails to fit in a `u8`.
    #[must_use]
    pub fn decode_bytes(&self, elements: &[RingElement]) -> Vec<u8> {
        if elements.is_empty() {
            return Vec::new();
        }

        let bits_per_elem = self.bits_per_element();

        let mut result = Vec::new();
        let mut bit_buffer: u64 = 0;
        let mut bits_in_buffer: usize = 0;

        for elem in elements {
            bit_buffer |= elem.value() << bits_in_buffer;
            bits_in_buffer += bits_per_elem;

            while bits_in_buffer >= 8 {
                result.push(
                    u8::try_from(bit_buffer & u64::from(u8::MAX))
                        .expect("low 8 bits of the bit buffer must fit in u8"),
                );
                bit_buffer >>= 8;
                bits_in_buffer -= 8;
            }
        }

        result
    }

    /// Encodes a UTF-8 string as bytes using [`encode_bytes`].
    #[must_use]
    pub fn encode_text(&self, text: &str) -> Vec<RingElement> {
        self.encode_bytes(text.as_bytes())
    }

    /// Decodes elements into bytes with [`decode_bytes`] and interprets them as UTF-8.
    ///
    /// # Errors
    ///
    /// - Returns [`EncodingError::DecodingError`] if the decoded bytes are not
    ///   valid UTF-8.
    ///
    /// # Notes
    ///
    /// This encoding does not embed the original byte length. Depending on the
    /// modulus and upstream padding, the decoded byte stream may contain trailing
    /// `0x00` bytes, which are valid UTF-8 and will appear as `\0` characters in the
    /// returned string.
    pub fn decode_text(&self, elements: &[RingElement]) -> Result<String, EncodingError> {
        let bytes = self.decode_bytes(elements);
        String::from_utf8(bytes).map_err(|e| EncodingError::DecodingError(e.to_string()))
    }
}

/// Errors that can occur while encoding or decoding.
#[derive(Debug, Clone, thiserror::Error)]
pub enum EncodingError {
    /// The provided modulus is too small to encode any payload bits.
    #[error("Modulus too small for encoding")]
    ModulusTooSmall,
    /// Encoding/decoding failed due to malformed input or invalid UTF-8.
    #[error("Decoding error: {0}")]
    DecodingError(String),
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn test_text_roundtrip_mod_256() {
        let encoder = Utf8Encoding::try_from(256, Utf8EncodingType::BitPacking).unwrap();

        let text = "Hello, World!";
        let enc = encoder.encode_text(text);
        let dec = encoder.decode_text(&enc).unwrap();
        assert_eq!(dec, text);
    }

    proptest! {
        #[test]
        fn proptest_text_roundtrip_default(
            text in proptest::string::string_regex(r"[\s\S]{0,200000}").unwrap(),
            modulus in 2u64..=511,
        ) {
            let encoder = Utf8Encoding::try_from(modulus, Utf8EncodingType::BitPacking).unwrap();

            let enc = encoder.encode_text(&text);
            let dec = encoder.decode_text(&enc).unwrap();
            prop_assert_eq!(dec, text);
        }
    }

    #[test]
    fn test_bit_stream_roundtrip_small_modulus() {
        let encoder = Utf8Encoding::try_from(16, Utf8EncodingType::BitPacking).unwrap();

        let data = vec![0xFF, 0x00, 0xAB, 0xCD];
        let enc = encoder.encode_bytes(&data); // bits_per_elem = 4
        let dec = encoder.decode_bytes(&enc);
        assert_eq!(dec[..data.len()], data[..]);
    }

    #[test]
    fn test_empty() {
        let encoder = Utf8Encoding::try_from(16, Utf8EncodingType::BitPacking).unwrap();

        let enc = encoder.encode_bytes(&[]);
        let dec = encoder.decode_bytes(&enc);
        assert!(dec.is_empty());
    }

    #[test]
    fn test_modulus_too_small() {
        let encoder = Utf8Encoding::try_from(1, Utf8EncodingType::BitPacking);
        assert!(matches!(encoder, Err(EncodingError::ModulusTooSmall)));
    }

    #[test]
    fn test_base_m_len_roundtrip_bytes_various_moduli() {
        let data = vec![0x12, 0x00, 0x00, 0xFF, 0x00];
        let moduli = [2u64, 3, 13, 128, 257, 65535];
        for &m in &moduli {
            let encoder =
                Utf8Encoding::try_from(m, Utf8EncodingType::LengthDelimitedBaseMTransduction)
                    .unwrap();
            let enc = encoder.encode_bytes_base_m_len(&data).unwrap();
            assert!(enc.iter().all(|e| e.value() < m));
            let dec = encoder.decode_bytes_base_m_len(&enc).unwrap();
            assert_eq!(dec, data);
        }
    }

    #[test]
    fn test_base_m_len_zero_padding_invariance() {
        let data = vec![0x00, 0x00, 0x01, 0x02, 0x00, 0x00];

        let encoder =
            Utf8Encoding::try_from(257u64, Utf8EncodingType::LengthDelimitedBaseMTransduction)
                .unwrap();

        let enc = encoder.encode_bytes_base_m_len(&data).unwrap();
        let mut padded = enc;
        for _ in 0..17 {
            padded.push(RingElement::zero(257u64));
        }
        let dec = encoder.decode_bytes_base_m_len(&padded).unwrap();
        assert_eq!(dec, data);
    }

    #[test]
    fn test_base_m_len_trailing_garbage_ignored() {
        let data = vec![0x10, 0x20, 0x00, 0xFF, 0x01];
        let modulus = 257u64;

        let encoder =
            Utf8Encoding::try_from(modulus, Utf8EncodingType::LengthDelimitedBaseMTransduction)
                .unwrap();

        let mut enc = encoder.encode_bytes_base_m_len(&data).unwrap();
        enc.push(RingElement::new(1, modulus));
        enc.push(RingElement::new(200, modulus));
        enc.push(RingElement::new(256, modulus));
        let dec = encoder.decode_bytes_base_m_len(&enc).unwrap();
        assert_eq!(dec, data);
    }

    #[test]
    fn test_base_m_len_decode_empty_errors() {
        let encoder =
            Utf8Encoding::try_from(10, Utf8EncodingType::LengthDelimitedBaseMTransduction).unwrap();
        let res = encoder.decode_bytes_base_m_len(&[]);
        assert!(matches!(res, Err(EncodingError::DecodingError(_))));
    }

    #[test]
    fn test_base_m_len_text_roundtrip() {
        let text = "Hello\u{0000}\u{0000}";
        let encoder =
            Utf8Encoding::try_from(257, Utf8EncodingType::LengthDelimitedBaseMTransduction)
                .unwrap();
        let enc = encoder.encode_text_base_m_len(text).unwrap();
        let dec = encoder.decode_text_base_m_len(&enc).unwrap();
        assert_eq!(dec, text);
    }

    proptest! {
        #[test]
        fn proptest_text_roundtrip_with_base_m_len(
            text in proptest::string::string_regex(r"[\s\S]{0,200000}").unwrap(),
            modulus in 2u64..=400,
        ) {
            let encoder = Utf8Encoding::try_from(modulus, Utf8EncodingType::LengthDelimitedBaseMTransduction).unwrap();
            let enc = encoder.encode_text_base_m_len(&text).unwrap();
            let dec = encoder.decode_text_base_m_len(&enc).unwrap();
            prop_assert_eq!(dec, text);
        }
    }
}

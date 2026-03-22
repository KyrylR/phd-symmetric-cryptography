import EncodingProofs.BaseMLen.Payload
import Mathlib

/-!
End-to-end stream lemmas for the length-delimited base-`m` format.

This file combines the prefix, renormalization, and payload results to reason
about the externally visible wire format
`length || state || payload`. The main outcome is that decoding the encoded
stream recovers the original bytes, even when extra trailing digits are appended.
-/

namespace EncodingProofs.BaseMLen

namespace Params

/-- Length formula for the encoded stream. The header consists of two fixed-width
prefixes of size `p.lengthPrefixDigits`, followed by the variable-length payload.
This arithmetic description of the wire format is later used when proving that
the decoder has enough digits to read each header block. -/
theorem encode_header_length (p : Params) (bytes : ByteString) :
    (encode p bytes).length = 2 * p.lengthPrefixDigits + (encodePayload p bytes.1).2.length := by
  simp [encode, encodeFixedWidthNat_length, two_mul, Nat.add_comm, Nat.add_left_comm]

/-- Every digit emitted by `encode` is a valid base-`m` digit. This is immediate
from the type of the output list, but the theorem exists as the explicit
"valid residues" statement used by the paper and later reasoning. -/
theorem encode_digits_lt_modulus (p : Params) (bytes : ByteString) :
    ∀ d ∈ encode p bytes, d.1 < p.modulus := by
  intro d _hd
  exact d.2

/-- Taking the first `k = p.lengthPrefixDigits` digits from `encode p bytes ++ tail`
recovers exactly the encoded length prefix.

How the proof works: expand `encode` as `lenDigits ++ stateDigits ++ payload`,
observe that `lenDigits.length = k` by `encodeFixedWidthNat_length`, and then
apply `List.take_append_of_le_length`. This lemma matches the decoder's first
parsing step. -/
theorem encode_take_len (p : Params) (bytes : ByteString) (tail : List (Digit p.modulus)) :
    List.take p.lengthPrefixDigits (encode p bytes ++ tail) =
      encodeFixedWidthNat p p.lengthPrefixDigits bytes.1.length := by
  let k := p.lengthPrefixDigits
  let lenDigits := encodeFixedWidthNat p k bytes.1.length
  let state := (encodePayload p bytes.1).1
  let stateDigits := encodeFixedWidthNat p k state
  let payload := (encodePayload p bytes.1).2
  have hk : k ≤ lenDigits.length := by
    simp [k, lenDigits, encodeFixedWidthNat_length]
  have h :=
    List.take_append_of_le_length
      (l₁ := lenDigits) (l₂ := stateDigits ++ payload ++ tail) hk
  simp [encode, k, lenDigits, state, stateDigits, payload,
    encodeFixedWidthNat_length, List.append_assoc] at h ⊢

/-- Dropping the first header block leaves the encoded state prefix followed by
the payload and any extra suffix.

How the proof works: write `encode p bytes ++ tail` as
`lenDigits ++ (stateDigits ++ payload ++ tail)` and use
`List.drop_append_of_le_length` with `lenDigits.length = k`. This lemma matches
the decoder's transition from parsing the length prefix to parsing the state
prefix. -/
theorem encode_drop_len (p : Params) (bytes : ByteString) (tail : List (Digit p.modulus)) :
    List.drop p.lengthPrefixDigits (encode p bytes ++ tail) =
      encodeFixedWidthNat p p.lengthPrefixDigits (encodePayload p bytes.1).1 ++
        ((encodePayload p bytes.1).2 ++ tail) := by
  let k := p.lengthPrefixDigits
  let lenDigits := encodeFixedWidthNat p k bytes.1.length
  let state := (encodePayload p bytes.1).1
  let stateDigits := encodeFixedWidthNat p k state
  let payload := (encodePayload p bytes.1).2
  have hk : k ≤ lenDigits.length := by
    simp [k, lenDigits, encodeFixedWidthNat_length]
  have h :=
    List.drop_append_of_le_length
      (l₁ := lenDigits) (l₂ := stateDigits ++ payload ++ tail) hk
  simp [encode, k, lenDigits, state, stateDigits, payload,
    encodeFixedWidthNat_length, List.append_assoc] at h ⊢

/-- After dropping the length prefix, taking the next `k` digits recovers the
encoded state prefix.

How the proof works: first invoke `encode_drop_len`, then apply
`List.take_append_of_le_length` to the leading `stateDigits`, whose length is
again `k` by `encodeFixedWidthNat_length`. This is the list-level version of the
decoder's second header parse. -/
theorem encode_take_state (p : Params) (bytes : ByteString) (tail : List (Digit p.modulus)) :
    List.take p.lengthPrefixDigits (List.drop p.lengthPrefixDigits (encode p bytes ++ tail)) =
      encodeFixedWidthNat p p.lengthPrefixDigits (encodePayload p bytes.1).1 := by
  rw [encode_drop_len p bytes tail]
  let k := p.lengthPrefixDigits
  let state := (encodePayload p bytes.1).1
  let stateDigits := encodeFixedWidthNat p k state
  let payload := (encodePayload p bytes.1).2
  have hk : k ≤ stateDigits.length := by
    simp [k, stateDigits, encodeFixedWidthNat_length]
  have h :=
    List.take_append_of_le_length
      (l₁ := stateDigits) (l₂ := payload ++ tail) hk
  simp [k, state, stateDigits, payload, encodeFixedWidthNat_length] at h ⊢

/-- Dropping both fixed-width header blocks leaves exactly the payload followed
by any extra suffix.

How the proof works: rewrite `2 * k` as `k + k`, drop once using
`encode_drop_len`, drop a second time past `stateDigits`, and use
`stateDigits.length = k`. This lemma identifies the exact suffix that the
payload decoder receives after header parsing. -/
theorem encode_drop_header (p : Params) (bytes : ByteString) (tail : List (Digit p.modulus)) :
    List.drop (2 * p.lengthPrefixDigits) (encode p bytes ++ tail) =
      (encodePayload p bytes.1).2 ++ tail := by
  let k := p.lengthPrefixDigits
  let state := (encodePayload p bytes.1).1
  let stateDigits := encodeFixedWidthNat p k state
  let payload := (encodePayload p bytes.1).2
  have hk : k ≤ stateDigits.length := by
    simp [k, stateDigits, encodeFixedWidthNat_length]
  calc
    List.drop (2 * p.lengthPrefixDigits) (encode p bytes ++ tail)
        = List.drop (k + k) (encode p bytes ++ tail) := by
            simp [k, two_mul]
    _ = List.drop k (List.drop k (encode p bytes ++ tail)) := by
          rw [List.drop_drop]
    _ = List.drop k (stateDigits ++ (payload ++ tail)) := by
          rw [encode_drop_len p bytes tail]
    _ = payload ++ tail := by
          have h :=
            List.drop_append_of_le_length
              (l₁ := stateDigits) (l₂ := payload ++ tail) hk
          simp [k, stateDigits, payload, encodeFixedWidthNat_length] at h ⊢

/-- If the decoded length prefix is `0` and the input contains enough digits to
read that prefix, then the whole stream decodes to the empty byte string.

How the proof works: unfold `decode` and observe that, once the first prefix is
known to decode to `0`, the decoder returns immediately without reading the
state or payload parts. -/
theorem decode_zero_length_of_prefix (p : Params) {digits : List (Digit p.modulus)}
    (henough : ¬ digits.length < p.lengthPrefixDigits)
    (hprefix : p.decodePrefix? (digits.take p.lengthPrefixDigits) = some ⟨0, by simp [u64Bound]⟩) :
    decode p digits = .ok [] := by
  unfold Params.decode
  dsimp
  rw [if_neg henough, hprefix]
  simp

/-- Concrete zero-length stream lemma: an encoded zero length prefix followed by
any suffix decodes to `[]`.

How the proof works: use `decode_zero_length_of_prefix`; the needed prefix
equality comes from `decodePrefix?_encodeFixedWidthNat` specialized to value `0`,
and the `take` on the appended suffix is handled by `take_append_of_le_length`. -/
theorem decode_zero_length_prefix_append (p : Params) (tail : List (Digit p.modulus)) :
    decode p (encodeFixedWidthNat p p.lengthPrefixDigits 0 ++ tail) = .ok [] := by
  apply decode_zero_length_of_prefix p
  · simp [encodeFixedWidthNat_length]
  · let k := p.lengthPrefixDigits
    let lenDigits := encodeFixedWidthNat p k 0
    have hk : k ≤ lenDigits.length := by
      simp [k, lenDigits, encodeFixedWidthNat_length]
    have hTake : List.take k (lenDigits ++ tail) = lenDigits := by
      have h :=
        List.take_append_of_le_length
          (l₁ := lenDigits) (l₂ := tail) hk
      simp [k, lenDigits, encodeFixedWidthNat_length] at h ⊢
    rw [hTake]
    simpa [k, lenDigits] using
      (decodePrefix?_encodeFixedWidthNat p (value := 0) (by simp [u64Bound]))

/-- Main end-to-end stream roundtrip theorem with an arbitrary trailing suffix.
Decoding `encode p bytes ++ tail` recovers the original bytes and ignores the
extra suffix.

How the proof works:

* if the byte string is empty, the length prefix is `0`, so
  `decode_zero_length_prefix_append` applies directly;
* if the byte string is nonempty, first identify the parsed length prefix via
  `encode_take_len` and the state prefix via `encode_take_state`;
* use `decodePrefix?_encodeFixedWidthNat` for both prefixes;
* obtain the state validity bounds from `encodePayload_state_bounds`;
* identify the payload suffix with `encode_drop_header`;
* finish by `payload_roundtrip_with_suffix`.

This theorem is the exact formal statement of padding-tolerant end-to-end
correctness for the wire format. -/
theorem stream_roundtrip_with_suffix (p : Params) (bytes : ByteString)
    (tail : List (Digit p.modulus)) :
    decode p (encode p bytes ++ tail) = .ok bytes.1 := by
  cases' bytes with raw hraw
  cases raw with
  | nil =>
      let k := p.lengthPrefixDigits
      let stateDigits := encodeFixedWidthNat p k p.decoderLowerBound
      simpa [encode, encodePayload, k, stateDigits, List.append_assoc] using
        (decode_zero_length_prefix_append p (stateDigits ++ tail))
  | cons b bs =>
      let bytes : ByteString := ⟨b :: bs, hraw⟩
      let k := p.lengthPrefixDigits
      let lenDigits := encodeFixedWidthNat p k (List.length (b :: bs))
      let state := (encodePayload p (b :: bs)).1
      let stateDigits := encodeFixedWidthNat p k state
      let payload := (encodePayload p (b :: bs)).2
      have hlenPrefix :
          decodePrefix? p lenDigits =
            some ⟨List.length (b :: bs), hraw⟩ := by
        exact decodePrefix?_encodeFixedWidthNat p hraw
      have hstateLt : state < u64Bound := by
        exact encodePayload_state_lt_u64Bound p (b :: bs)
      have hstatePrefix :
          decodePrefix? p stateDigits = some ⟨state, hstateLt⟩ := by
        exact decodePrefix?_encodeFixedWidthNat p hstateLt
      have hstateValid : p.decoderLowerBound ≤ state := by
        exact (encodePayload_state_bounds p (b :: bs)).1
      have hEnough : ¬ (encode p bytes ++ tail).length < k := by
        simp [bytes, encode, k, encodeFixedWidthNat_length, List.length_append]
      have hEnoughStateArith :
          ¬ ((encode p bytes).length + tail.length - k < k) := by
        intro hlt
        simp [bytes, encode, k, encodeFixedWidthNat_length, List.length_append] at hlt
        omega
      have hStateNotInvalid : ¬ state < p.decoderLowerBound := by
        exact not_lt_of_ge hstateValid
      have hpayloadTail :
          decodePayload p (List.length (b :: bs)) state (payload ++ tail) = .ok (b :: bs, tail) := by
        simpa [payload, List.append_assoc] using payload_roundtrip_with_suffix p (b :: bs) tail
      have hpayloadTail' :
          p.decodePayload (bs.length + 1) state ((p.encodePayload bytes.1).2 ++ tail) =
            Except.ok (b :: bs, tail) := by
        simpa [bytes, payload] using hpayloadTail
      have hTakeState' :
          List.take k (stateDigits ++ (payload ++ tail)) = stateDigits := by
        simpa [bytes, k, state, stateDigits, payload, encode_drop_len p bytes tail] using
          encode_take_state p bytes tail
      unfold Params.decode
      dsimp [k]
      rw [if_neg hEnough]
      rw [encode_take_len p bytes tail, hlenPrefix]
      simp
      rw [encode_drop_len p bytes tail]
      rw [if_neg hEnoughStateArith]
      rw [hTakeState', hstatePrefix]
      simp [hStateNotInvalid]
      rw [encode_drop_header p bytes tail, hpayloadTail']

/-- Alias of `stream_roundtrip_with_suffix` under the decode/encode-oriented name
used by later statements and the paper text. -/
theorem decode_encode_append (p : Params) (bytes : ByteString) (tail : List (Digit p.modulus)) :
    decode p (encode p bytes ++ tail) = .ok bytes.1 := by
  simpa using stream_roundtrip_with_suffix p bytes tail

/-- Empty-suffix specialization of `stream_roundtrip_with_suffix`. This is the
closed end-to-end roundtrip theorem for a self-contained encoded stream. -/
theorem stream_roundtrip (p : Params) (bytes : ByteString) :
    decode p (encode p bytes) = .ok bytes.1 := by
  simpa using stream_roundtrip_with_suffix p bytes []

/-- Alias of `stream_roundtrip` under the decode/encode-oriented name used as the
final public correctness statement. -/
theorem decode_encode (p : Params) (bytes : ByteString) :
    decode p (encode p bytes) = .ok bytes.1 := by
  simpa using stream_roundtrip p bytes

end Params

end EncodingProofs.BaseMLen

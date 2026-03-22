#![allow(dead_code)]

use constriction::stream::{Decode, model::DefaultUniformModel, stack::DefaultAnsCoder};
use num_bigint::BigUint;
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::fmt;

pub const SHARED_COMPARISON_MODULI: [u64; 5] = [2, 3, 13, 65, 251];
pub const NATIVE_ONLY_MODULUS: u64 = 257;
pub const BYTE_CASES: [(usize, &str); 3] = [(32, "32b"), (1024, "1k"), (65_536, "64k")];
pub const TEXT_CASES: [(usize, &str); 2] = [(1024, "1k"), (65_536, "64k")];
pub const TEXT_SMOKE_MODULUS: u64 = 65;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BaselineError {
    InvalidModulus,
    ModulusTooLargeForBigUint,
    InputLengthDoesNotFitU64,
    DecodedLengthDoesNotFitUsize,
    NotEnoughLengthPrefixDigits,
    InvalidDigit,
    InvalidRadixDigits,
    PayloadExceedsDeclaredLength,
    InvalidAnsCompressed,
    InvalidAnsSymbol,
}

impl fmt::Display for BaselineError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match self {
            Self::InvalidModulus => "modulus must be at least 2",
            Self::ModulusTooLargeForBigUint => {
                "num-bigint radix conversion only supports moduli up to 256"
            }
            Self::InputLengthDoesNotFitU64 => "input length does not fit in u64",
            Self::DecodedLengthDoesNotFitUsize => "decoded length does not fit in usize",
            Self::NotEnoughLengthPrefixDigits => "not enough digits for the length prefix",
            Self::InvalidDigit => "digit is out of range for the selected modulus",
            Self::InvalidRadixDigits => "payload digits are invalid for the selected radix",
            Self::PayloadExceedsDeclaredLength => {
                "decoded payload exceeds the declared byte length"
            }
            Self::InvalidAnsCompressed => "ANS reference payload is not a valid compressed stream",
            Self::InvalidAnsSymbol => "ANS reference produced a symbol outside the byte range",
        };

        write!(f, "{message}")
    }
}

impl std::error::Error for BaselineError {}

pub fn random_bytes(len: usize, seed: u64) -> Vec<u8> {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut bytes = vec![0u8; len];
    rng.fill_bytes(&mut bytes);
    bytes
}

pub fn mixed_utf8_text(target_len: usize) -> String {
    let alphabet = ['A', ' ', 'é', 'Ж', '漢', '🙂'];
    let mut output = String::with_capacity(target_len);
    let mut index = 0usize;

    while output.len() < target_len {
        let remaining = target_len - output.len();
        let mut pushed = false;

        for offset in 0..alphabet.len() {
            let ch = alphabet[(index + offset) % alphabet.len()];
            if ch.len_utf8() <= remaining {
                output.push(ch);
                index = index.wrapping_add(1);
                pushed = true;
                break;
            }
        }

        if !pushed {
            output.push('a');
        }
    }

    output
}

pub fn encode_bytes_biguint_base_m_len(
    bytes: &[u8],
    modulus: u64,
) -> Result<Vec<u64>, BaselineError> {
    let radix = validate_biguint_modulus(modulus)?;
    let len_u64 =
        u64::try_from(bytes.len()).map_err(|_| BaselineError::InputLengthDoesNotFitU64)?;
    let mut encoded = encode_u64_base_m_fixed(len_u64, modulus);
    let payload_digits = BigUint::from_bytes_be(bytes).to_radix_le(radix);
    encoded.extend(payload_digits.into_iter().map(u64::from));
    Ok(encoded)
}

pub fn decode_bytes_biguint_base_m_len(
    digits: &[u64],
    modulus: u64,
) -> Result<Vec<u8>, BaselineError> {
    let radix = validate_biguint_modulus(modulus)?;
    let length_digits = length_prefix_digits(modulus);
    if digits.len() < length_digits {
        return Err(BaselineError::NotEnoughLengthPrefixDigits);
    }

    let len_u64 = decode_u64_base_m_fixed(&digits[..length_digits], modulus)?;
    let len = usize::try_from(len_u64).map_err(|_| BaselineError::DecodedLengthDoesNotFitUsize)?;
    if len == 0 {
        return Ok(Vec::new());
    }

    let payload_digits = digits[length_digits..]
        .iter()
        .map(|&digit| {
            if digit >= modulus {
                return Err(BaselineError::InvalidDigit);
            }

            u8::try_from(digit).map_err(|_| BaselineError::InvalidDigit)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let bigint =
        BigUint::from_radix_le(&payload_digits, radix).ok_or(BaselineError::InvalidRadixDigits)?;
    let bytes = bigint.to_bytes_be();
    if bytes.len() > len {
        return Err(BaselineError::PayloadExceedsDeclaredLength);
    }

    let mut restored = vec![0u8; len - bytes.len()];
    restored.extend(bytes);
    Ok(restored)
}

pub fn encode_bytes_constriction_ans(bytes: &[u8]) -> Result<Vec<u32>, BaselineError> {
    let mut ans = DefaultAnsCoder::new();
    let model = DefaultUniformModel::new(256);
    ans.encode_iid_symbols_reverse(bytes.iter().copied().map(usize::from), model)
        .map_err(|_| BaselineError::InvalidAnsCompressed)?;
    ans.into_compressed()
        .map_err(|_| BaselineError::InvalidAnsCompressed)
}

pub fn decode_bytes_constriction_ans(
    compressed: &[u32],
    len: usize,
) -> Result<Vec<u8>, BaselineError> {
    let mut ans = DefaultAnsCoder::from_compressed(compressed.to_vec())
        .map_err(|_| BaselineError::InvalidAnsCompressed)?;
    let model = DefaultUniformModel::new(256);

    ans.decode_iid_symbols(len, model)
        .map(|symbol| {
            let symbol = symbol.map_err(|_| BaselineError::InvalidAnsCompressed)?;
            u8::try_from(symbol).map_err(|_| BaselineError::InvalidAnsSymbol)
        })
        .collect()
}

fn validate_biguint_modulus(modulus: u64) -> Result<u32, BaselineError> {
    if modulus < 2 {
        return Err(BaselineError::InvalidModulus);
    }
    if modulus > 256 {
        return Err(BaselineError::ModulusTooLargeForBigUint);
    }

    u32::try_from(modulus).map_err(|_| BaselineError::ModulusTooLargeForBigUint)
}

fn length_prefix_digits(modulus: u64) -> usize {
    let target = 1u128 << 64;
    let base = u128::from(modulus);
    let mut pow = 1u128;
    let mut digits = 0usize;

    while pow < target {
        pow = pow.saturating_mul(base);
        digits += 1;
    }

    digits
}

fn encode_u64_base_m_fixed(value: u64, modulus: u64) -> Vec<u64> {
    let digits = length_prefix_digits(modulus);
    let mut remaining = value;
    let mut encoded = Vec::with_capacity(digits);

    for _ in 0..digits {
        encoded.push(remaining % modulus);
        remaining /= modulus;
    }

    encoded
}

fn decode_u64_base_m_fixed(digits: &[u64], modulus: u64) -> Result<u64, BaselineError> {
    let mut value = 0u128;
    let mut place = 1u128;
    let base = u128::from(modulus);

    for &digit in digits {
        if digit >= modulus {
            return Err(BaselineError::InvalidDigit);
        }

        value = value
            .checked_add(u128::from(digit) * place)
            .ok_or(BaselineError::InvalidDigit)?;
        place = place.checked_mul(base).ok_or(BaselineError::InvalidDigit)?;
    }

    u64::try_from(value).map_err(|_| BaselineError::InvalidDigit)
}

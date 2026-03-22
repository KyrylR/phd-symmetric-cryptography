/// Compute the greatest common divisor using Euclidean algorithm.
#[must_use]
pub fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// Extended Euclidean Algorithm.
/// Returns (gcd, x, y) such that ax + by = gcd(a, b).
#[must_use]
pub fn extended_gcd(left: i64, right: i64) -> (i64, i64, i64) {
    if right == 0 {
        (left, 1, 0)
    } else {
        let (gcd_value, left_coeff, right_coeff) = extended_gcd(right, left % right);
        (
            gcd_value,
            right_coeff,
            left_coeff - (left / right) * right_coeff,
        )
    }
}

fn extended_gcd_i128(left: i128, right: i128) -> (i128, i128, i128) {
    if right == 0 {
        (left, 1, 0)
    } else {
        let (gcd_value, left_coeff, right_coeff) = extended_gcd_i128(right, left % right);
        (
            gcd_value,
            right_coeff,
            left_coeff - (left / right) * right_coeff,
        )
    }
}

/// Compute multiplicative inverse of a modulo m.
/// Returns None if gcd(a, m) != 1.
#[must_use]
pub fn mod_inverse(value: u64, modulus: u64) -> Option<u64> {
    if modulus == 0 {
        return None;
    }

    let (gcd_value, inverse_coeff, _) = extended_gcd_i128(i128::from(value), i128::from(modulus));
    if gcd_value == 1 {
        let modulus_i128 = i128::from(modulus);
        let normalized = inverse_coeff.rem_euclid(modulus_i128);
        u64::try_from(normalized).ok()
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gcd_basic() {
        assert_eq!(gcd(48, 18), 6);
        assert_eq!(gcd(17, 13), 1);
        assert_eq!(gcd(100, 25), 25);
        assert_eq!(gcd(7, 0), 7);
        assert_eq!(gcd(0, 7), 7);
    }

    #[test]
    fn test_extended_gcd() {
        let (gcd_value, left_coeff, right_coeff) = extended_gcd(48, 18);
        assert_eq!(gcd_value, 6);
        assert_eq!(48 * left_coeff + 18 * right_coeff, 6);

        let (gcd_value, left_coeff, right_coeff) = extended_gcd(17, 13);
        assert_eq!(gcd_value, 1);
        assert_eq!(17 * left_coeff + 13 * right_coeff, 1);
    }

    #[test]
    fn test_mod_inverse() {
        assert_eq!(mod_inverse(3, 7), Some(5)); // 3 * 5 = 15 ≡ 1 (mod 7)
        assert_eq!(mod_inverse(5, 26), Some(21)); // 5 * 21 = 105 ≡ 1 (mod 26)
        assert_eq!(mod_inverse(2, 4), None); // gcd(2, 4) = 2 ≠ 1
        assert_eq!(mod_inverse(1, 100), Some(1));
    }
}

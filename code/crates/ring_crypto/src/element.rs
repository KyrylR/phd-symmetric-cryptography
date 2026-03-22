use crate::gcd::{gcd, mod_inverse};
use serde::{Deserialize, Serialize};
use std::ops::{Add, Mul, Neg, Sub};

/// Element of the ring `Z_m` (integers modulo m).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RingElement {
    value: u64,
    modulus: u64,
}

impl RingElement {
    /// Create a new ring element, automatically reducing modulo m.
    ///
    /// # Panics
    /// Panics if modulus is 0.
    #[must_use]
    pub fn new(value: u64, modulus: u64) -> Self {
        assert!(modulus > 0, "Modulus must be positive");
        Self {
            value: value % modulus,
            modulus,
        }
    }

    /// Create the zero element of `Z_m`.
    #[must_use]
    pub fn zero(modulus: u64) -> Self {
        Self::new(0, modulus)
    }

    /// Create the unit element (1) of `Z_m`.
    #[must_use]
    pub fn one(modulus: u64) -> Self {
        Self::new(1, modulus)
    }

    /// Get the underlying value.
    #[must_use]
    pub const fn value(&self) -> u64 {
        self.value
    }

    /// Get the modulus.
    #[must_use]
    pub const fn modulus(&self) -> u64 {
        self.modulus
    }

    /// Check if this element is a unit (has multiplicative inverse).
    /// An element a is a unit iff gcd(a, m) = 1.
    #[must_use]
    pub fn is_unit(&self) -> bool {
        self.value != 0 && gcd(self.value, self.modulus) == 1
    }

    /// Check if this element is a zero divisor.
    /// An element a ≠ 0 is a zero divisor iff gcd(a, m) > 1.
    #[must_use]
    pub fn is_zero_divisor(&self) -> bool {
        self.value != 0 && gcd(self.value, self.modulus) > 1
    }

    /// Check if this is the zero element.
    #[must_use]
    pub const fn is_zero(&self) -> bool {
        self.value == 0
    }

    /// Compute the multiplicative inverse if it exists.
    /// Returns None if gcd(value, modulus) != 1.
    #[must_use]
    pub fn inverse(&self) -> Option<Self> {
        mod_inverse(self.value, self.modulus).map(|inv| Self::new(inv, self.modulus))
    }

    fn reduce_modulo_u128(value: u128, modulus: u64) -> u64 {
        u64::try_from(value % u128::from(modulus))
            .expect("modular reduction of u128 by u64 modulus must fit in u64")
    }

    /// Scalar multiplication by a u64 value.
    #[must_use]
    pub fn scale(&self, scalar: u64) -> Self {
        let product = u128::from(self.value) * u128::from(scalar);
        Self::new(
            Self::reduce_modulo_u128(product, self.modulus),
            self.modulus,
        )
    }
}

impl Add for RingElement {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        assert_eq!(self.modulus, other.modulus, "Moduli must match");
        let sum = (u128::from(self.value) + u128::from(other.value)) % u128::from(self.modulus);
        Self {
            value: Self::reduce_modulo_u128(sum, self.modulus),
            modulus: self.modulus,
        }
    }
}

impl Sub for RingElement {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        assert_eq!(self.modulus, other.modulus, "Moduli must match");
        let value = if self.value >= other.value {
            self.value - other.value
        } else {
            self.modulus - (other.value - self.value)
        };
        Self {
            value,
            modulus: self.modulus,
        }
    }
}

impl Mul for RingElement {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        assert_eq!(self.modulus, other.modulus, "Moduli must match");
        let product = u128::from(self.value) * u128::from(other.value);
        Self {
            value: Self::reduce_modulo_u128(product, self.modulus),
            modulus: self.modulus,
        }
    }
}

impl Neg for RingElement {
    type Output = Self;

    fn neg(self) -> Self {
        if self.value == 0 {
            self
        } else {
            Self {
                value: self.modulus - self.value,
                modulus: self.modulus,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_reduces_modulo() {
        let e = RingElement::new(15, 7);
        assert_eq!(e.value(), 1); // 15 mod 7 = 1
    }

    #[test]
    fn test_addition() {
        let m = 26;
        let a = RingElement::new(15, m);
        let b = RingElement::new(20, m);
        assert_eq!((a + b).value(), 9); // (15 + 20) mod 26 = 9
    }

    #[test]
    fn test_subtraction() {
        let m = 26;
        let a = RingElement::new(10, m);
        let b = RingElement::new(15, m);
        assert_eq!((a - b).value(), 21); // (10 - 15 + 26) mod 26 = 21
    }

    #[test]
    fn test_multiplication() {
        let m = 26;
        let a = RingElement::new(15, m);
        let b = RingElement::new(20, m);
        assert_eq!((a * b).value(), 14); // (15 * 20) mod 26 = 14
    }

    #[test]
    fn test_negation() {
        let m = 26;
        let a = RingElement::new(10, m);
        assert_eq!((-a).value(), 16); // 26 - 10 = 16

        let zero = RingElement::zero(m);
        assert_eq!((-zero).value(), 0);
    }

    #[test]
    fn test_is_unit() {
        let m = 26;
        assert!(RingElement::new(5, m).is_unit()); // gcd(5, 26) = 1
        assert!(RingElement::new(7, m).is_unit()); // gcd(7, 26) = 1
        assert!(!RingElement::new(13, m).is_unit()); // gcd(13, 26) = 13
        assert!(!RingElement::new(0, m).is_unit()); // 0 is never a unit
    }

    #[test]
    fn test_is_zero_divisor() {
        let m = 26;
        assert!(RingElement::new(13, m).is_zero_divisor()); // gcd(13, 26) = 13
        assert!(RingElement::new(2, m).is_zero_divisor()); // gcd(2, 26) = 2
        assert!(!RingElement::new(5, m).is_zero_divisor()); // gcd(5, 26) = 1
        assert!(!RingElement::new(0, m).is_zero_divisor()); // 0 is not a zero divisor by definition
    }

    #[test]
    fn test_inverse() {
        let m = 26;
        let a = RingElement::new(5, m);
        let a_inv = a.inverse().expect("5 should be invertible mod 26");
        assert_eq!((a * a_inv).value(), 1);

        let b = RingElement::new(13, m);
        assert!(b.inverse().is_none()); // 13 is not invertible mod 26
    }

    #[test]
    fn test_large_modulus() {
        let m = u64::MAX / 2;
        let a = RingElement::new(m - 1, m);
        let b = RingElement::new(m - 1, m);
        let product = a * b;
        assert!(product.value() < m);
    }
}

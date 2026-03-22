use crate::element::RingElement;
use crate::error::RingError;
use serde::{Deserialize, Serialize};
use std::ops::{Add, Index, IndexMut, Neg, Sub};

/// Vector of ring elements over `Z_m`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RingVector {
    pub(crate) elements: Vec<RingElement>,
    pub(crate) modulus: u64,
}

impl RingVector {
    /// Create a new vector from a slice of ring elements.
    ///
    /// # Panics
    /// Panics if the vector is empty or elements have different moduli.
    #[must_use]
    pub fn new(elements: Vec<RingElement>) -> Self {
        Self::try_new(elements).expect("vector construction must succeed")
    }

    /// Try to create a new vector from ring elements.
    ///
    /// # Errors
    ///
    /// Returns [`RingError::DimensionMismatch`] if the vector is empty and
    /// [`RingError::ModulusMismatch`] if the elements do not share the same modulus.
    pub fn try_new(elements: Vec<RingElement>) -> Result<Self, RingError> {
        if elements.is_empty() {
            return Err(RingError::DimensionMismatch(
                "vector cannot be empty".to_string(),
            ));
        }

        let modulus = elements[0].modulus();
        if elements.iter().any(|element| element.modulus() != modulus) {
            return Err(RingError::ModulusMismatch(
                "all vector elements must have the same modulus".to_string(),
            ));
        }

        Ok(Self { elements, modulus })
    }

    /// Create a zero vector of given length.
    ///
    /// # Panics
    /// Panics if `len == 0`.
    #[must_use]
    pub fn zero(len: usize, modulus: u64) -> Self {
        assert!(len > 0, "Vector length must be positive");
        Self {
            elements: vec![RingElement::zero(modulus); len],
            modulus,
        }
    }

    /// Create a vector from raw values.
    #[must_use]
    pub fn from_values(values: &[u64], modulus: u64) -> Self {
        let elements: Vec<RingElement> = values
            .iter()
            .map(|&v| RingElement::new(v, modulus))
            .collect();
        Self::new(elements)
    }

    /// Get the length of the vector.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.elements.len()
    }

    /// Check if vector is empty.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Get the modulus.
    #[must_use]
    pub const fn modulus(&self) -> u64 {
        self.modulus
    }

    /// Get element at index.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    #[must_use]
    pub fn get(&self, index: usize) -> RingElement {
        self.elements[index]
    }

    /// Set element at index.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds or if `value` has a different modulus.
    pub fn set(&mut self, index: usize, value: RingElement) {
        assert_eq!(value.modulus(), self.modulus, "Modulus must match");
        self.elements[index] = value;
    }

    /// Return the underlying elements as a slice.
    #[must_use]
    pub fn elements(&self) -> &[RingElement] {
        &self.elements
    }

    /// Compute dot product with another vector.
    ///
    /// # Panics
    /// Panics if vectors have different lengths or different moduli.
    #[must_use]
    pub fn dot(&self, other: &Self) -> RingElement {
        assert_eq!(self.len(), other.len(), "Vectors must have same length");
        assert_eq!(self.modulus, other.modulus, "Moduli must match");

        self.elements
            .iter()
            .zip(other.elements.iter())
            .map(|(&a, &b)| a * b)
            .fold(RingElement::zero(self.modulus), |acc, x| acc + x)
    }

    /// Compute a checked dot product with another vector.
    ///
    /// # Errors
    ///
    /// Returns [`RingError::DimensionMismatch`] or [`RingError::ModulusMismatch`]
    /// when the operands are incompatible.
    pub fn try_dot(&self, other: &Self) -> Result<RingElement, RingError> {
        self.ensure_compatible(other)?;
        Ok(self.dot(other))
    }

    /// Scalar multiplication.
    ///
    /// # Panics
    /// Panics if `scalar` has a different modulus.
    #[must_use]
    pub fn scale(&self, scalar: RingElement) -> Self {
        assert_eq!(scalar.modulus(), self.modulus, "Modulus must match");
        Self {
            elements: self.elements.iter().map(|&e| e * scalar).collect(),
            modulus: self.modulus,
        }
    }

    /// Scale by a raw value.
    #[must_use]
    pub fn scale_by(&self, scalar: u64) -> Self {
        let s = RingElement::new(scalar, self.modulus);
        self.scale(s)
    }

    /// Compute a checked element-wise sum.
    ///
    /// # Errors
    ///
    /// Returns [`RingError::DimensionMismatch`] or [`RingError::ModulusMismatch`]
    /// when the operands are incompatible.
    pub fn try_add(&self, other: &Self) -> Result<Self, RingError> {
        self.ensure_compatible(other)?;
        Ok(self + other)
    }

    /// Compute a checked element-wise difference.
    ///
    /// # Errors
    ///
    /// Returns [`RingError::DimensionMismatch`] or [`RingError::ModulusMismatch`]
    /// when the operands are incompatible.
    pub fn try_sub(&self, other: &Self) -> Result<Self, RingError> {
        self.ensure_compatible(other)?;
        Ok(self - other)
    }

    /// Get iterator over elements.
    pub fn iter(&self) -> impl Iterator<Item = &RingElement> {
        self.elements.iter()
    }

    /// Get mutable iterator over elements.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut RingElement> {
        self.elements.iter_mut()
    }

    /// Convert to Vec of raw values.
    #[must_use]
    pub fn to_values(&self) -> Vec<u64> {
        self.elements
            .iter()
            .map(super::element::RingElement::value)
            .collect()
    }

    fn ensure_compatible(&self, other: &Self) -> Result<(), RingError> {
        if self.len() != other.len() {
            return Err(RingError::DimensionMismatch(format!(
                "expected matching vector lengths, got {} and {}",
                self.len(),
                other.len()
            )));
        }

        if self.modulus != other.modulus {
            return Err(RingError::ModulusMismatch(format!(
                "expected matching vector moduli, got {} and {}",
                self.modulus, other.modulus
            )));
        }

        Ok(())
    }
}

impl Add for RingVector {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        assert_eq!(self.len(), other.len(), "Vectors must have same length");
        assert_eq!(self.modulus, other.modulus, "Moduli must match");

        Self {
            elements: self
                .elements
                .into_iter()
                .zip(other.elements)
                .map(|(a, b)| a + b)
                .collect(),
            modulus: self.modulus,
        }
    }
}

impl<'b> Add<&'b RingVector> for &RingVector {
    type Output = RingVector;

    fn add(self, other: &'b RingVector) -> RingVector {
        assert_eq!(self.len(), other.len(), "Vectors must have same length");
        assert_eq!(self.modulus, other.modulus, "Moduli must match");

        RingVector {
            elements: self
                .elements
                .iter()
                .zip(other.elements.iter())
                .map(|(&a, &b)| a + b)
                .collect(),
            modulus: self.modulus,
        }
    }
}

impl Sub for RingVector {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        assert_eq!(self.len(), other.len(), "Vectors must have same length");
        assert_eq!(self.modulus, other.modulus, "Moduli must match");

        Self {
            elements: self
                .elements
                .into_iter()
                .zip(other.elements)
                .map(|(a, b)| a - b)
                .collect(),
            modulus: self.modulus,
        }
    }
}

impl<'b> Sub<&'b RingVector> for &RingVector {
    type Output = RingVector;

    fn sub(self, other: &'b RingVector) -> RingVector {
        assert_eq!(self.len(), other.len(), "Vectors must have same length");
        assert_eq!(self.modulus, other.modulus, "Moduli must match");

        RingVector {
            elements: self
                .elements
                .iter()
                .zip(other.elements.iter())
                .map(|(&a, &b)| a - b)
                .collect(),
            modulus: self.modulus,
        }
    }
}

impl Neg for RingVector {
    type Output = Self;

    fn neg(self) -> Self {
        Self {
            elements: self.elements.into_iter().map(|e| -e).collect(),
            modulus: self.modulus,
        }
    }
}

impl Index<usize> for RingVector {
    type Output = RingElement;

    fn index(&self, index: usize) -> &Self::Output {
        &self.elements[index]
    }
}

impl IndexMut<usize> for RingVector {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.elements[index]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vector_creation() {
        let v = RingVector::from_values(&[1, 2, 3], 7);
        assert_eq!(v.len(), 3);
        assert_eq!(v.modulus(), 7);
        assert_eq!(v[0].value(), 1);
        assert_eq!(v[1].value(), 2);
        assert_eq!(v[2].value(), 3);
    }

    #[test]
    fn test_zero_vector() {
        let v = RingVector::zero(5, 11);
        assert_eq!(v.len(), 5);
        for i in 0..5 {
            assert_eq!(v[i].value(), 0);
        }
    }

    #[test]
    fn test_vector_addition() {
        let a = RingVector::from_values(&[1, 2, 3], 7);
        let b = RingVector::from_values(&[4, 5, 6], 7);
        let c = a + b;
        assert_eq!(c.to_values(), vec![5, 0, 2]); // (1+4, 2+5, 3+6) mod 7
    }

    #[test]
    fn test_vector_subtraction() {
        let a = RingVector::from_values(&[1, 2, 3], 7);
        let b = RingVector::from_values(&[4, 5, 6], 7);
        let c = a - b;
        assert_eq!(c.to_values(), vec![4, 4, 4]); // (1-4+7, 2-5+7, 3-6+7) mod 7
    }

    #[test]
    fn test_dot_product() {
        let a = RingVector::from_values(&[1, 2, 3], 7);
        let b = RingVector::from_values(&[4, 5, 6], 7);
        let dot = a.dot(&b);
        // 1*4 + 2*5 + 3*6 = 4 + 10 + 18 = 32 mod 7 = 4
        assert_eq!(dot.value(), 4);
    }

    #[test]
    fn test_scalar_multiplication() {
        let v = RingVector::from_values(&[1, 2, 3], 7);
        let scaled = v.scale_by(3);
        assert_eq!(scaled.to_values(), vec![3, 6, 2]); // (3, 6, 9 mod 7)
    }

    #[test]
    fn test_negation() {
        let v = RingVector::from_values(&[1, 2, 3], 7);
        let neg_v = -v;
        assert_eq!(neg_v.to_values(), vec![6, 5, 4]); // (7-1, 7-2, 7-3)
    }
}

use crate::{RingElement, RingError, RingVector};
use serde::{Deserialize, Serialize};

/// Matrix of ring elements over `Z_m`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RingMatrix {
    rows: Vec<RingVector>,
    modulus: u64,
    cols: usize,
}

impl RingMatrix {
    /// Create a new matrix from rows of ring elements.
    ///
    /// # Panics
    ///
    /// Panics when the rows are empty, ragged, or use different moduli.
    #[must_use]
    pub fn new(rows: Vec<RingVector>) -> Self {
        Self::try_new(rows).expect("matrix construction must succeed")
    }

    /// Try to create a new matrix from rows of ring elements.
    ///
    /// # Errors
    ///
    /// Returns [`RingError::DimensionMismatch`] for an empty or ragged matrix and
    /// [`RingError::ModulusMismatch`] when the rows use different moduli.
    pub fn try_new(rows: Vec<RingVector>) -> Result<Self, RingError> {
        if rows.is_empty() {
            return Err(RingError::DimensionMismatch(
                "matrix cannot be empty".to_string(),
            ));
        }

        let cols = rows[0].len();
        if cols == 0 {
            return Err(RingError::DimensionMismatch(
                "matrix cannot have zero columns".to_string(),
            ));
        }

        let modulus = rows[0].modulus();
        for (index, row) in rows.iter().enumerate() {
            if row.len() != cols {
                return Err(RingError::DimensionMismatch(format!(
                    "row {} has length {}, expected {}",
                    index,
                    row.len(),
                    cols
                )));
            }
            if row.modulus() != modulus {
                return Err(RingError::ModulusMismatch(format!(
                    "row {} has modulus {}, expected {}",
                    index,
                    row.modulus(),
                    modulus
                )));
            }
        }

        Ok(Self {
            rows,
            modulus,
            cols,
        })
    }

    /// Create a zero matrix.
    ///
    /// # Panics
    ///
    /// Panics if `row_count == 0` or `col_count == 0`.
    #[must_use]
    pub fn zero(row_count: usize, col_count: usize, modulus: u64) -> Self {
        assert!(row_count > 0, "matrix must have at least one row");
        assert!(col_count > 0, "matrix must have at least one column");
        Self {
            rows: (0..row_count)
                .map(|_| RingVector::zero(col_count, modulus))
                .collect(),
            modulus,
            cols: col_count,
        }
    }

    /// Create a matrix from raw values.
    #[must_use]
    pub fn from_values(rows: &[Vec<u64>], modulus: u64) -> Self {
        let vectors = rows
            .iter()
            .map(|row| RingVector::from_values(row, modulus))
            .collect();
        Self::new(vectors)
    }

    /// Create the identity matrix of size `n`.
    ///
    /// # Panics
    ///
    /// Panics if `size == 0`.
    #[must_use]
    pub fn identity(size: usize, modulus: u64) -> Self {
        assert!(size > 0, "identity matrix size must be positive");
        let mut matrix = Self::zero(size, size, modulus);
        for index in 0..size {
            matrix.rows[index].elements[index] = RingElement::one(modulus);
        }
        matrix
    }

    /// Number of rows.
    #[must_use]
    pub const fn rows(&self) -> usize {
        self.rows.len()
    }

    /// Number of columns.
    #[must_use]
    pub const fn cols(&self) -> usize {
        self.cols
    }

    /// Modulus shared by all matrix entries.
    #[must_use]
    pub const fn modulus(&self) -> u64 {
        self.modulus
    }

    /// Borrow the matrix rows.
    #[must_use]
    pub fn row_vectors(&self) -> &[RingVector] {
        &self.rows
    }

    /// Borrow one row.
    #[must_use]
    pub fn row(&self, index: usize) -> &RingVector {
        &self.rows[index]
    }

    /// Get one entry.
    #[must_use]
    pub fn get(&self, row: usize, col: usize) -> RingElement {
        self.rows[row][col]
    }

    /// Set one entry.
    ///
    /// # Panics
    ///
    /// Panics if the index is out of bounds or the element modulus does not match
    /// the matrix modulus.
    pub fn set(&mut self, row: usize, col: usize, value: RingElement) {
        assert_eq!(value.modulus(), self.modulus, "Modulus must match");
        self.rows[row].elements[col] = value;
    }

    /// Convert to raw values.
    #[must_use]
    pub fn to_values(&self) -> Vec<Vec<u64>> {
        self.rows.iter().map(RingVector::to_values).collect()
    }

    /// Return the transpose of this matrix.
    #[must_use]
    pub fn transpose(&self) -> Self {
        let mut rows = Vec::with_capacity(self.cols);
        for col in 0..self.cols {
            let values = self.rows.iter().map(|row| row[col]).collect();
            rows.push(RingVector::new(values));
        }
        Self::new(rows)
    }

    /// Reorder columns according to `permutation`, where each new column `j`
    /// comes from old column `permutation[j]`.
    ///
    /// # Errors
    ///
    /// Returns [`RingError::DimensionMismatch`] when the permutation has the wrong
    /// length or contains duplicates/out-of-range indices.
    pub fn permute_columns(&self, permutation: &[usize]) -> Result<Self, RingError> {
        if permutation.len() != self.cols {
            return Err(RingError::DimensionMismatch(format!(
                "expected {} columns in permutation, got {}",
                self.cols,
                permutation.len()
            )));
        }

        let mut seen = vec![false; self.cols];
        for &column in permutation {
            if column >= self.cols || seen[column] {
                return Err(RingError::DimensionMismatch(
                    "permutation must contain each column index exactly once".to_string(),
                ));
            }
            seen[column] = true;
        }

        let rows = self
            .rows
            .iter()
            .map(|row| {
                let elements = permutation.iter().map(|&column| row[column]).collect();
                RingVector::new(elements)
            })
            .collect();
        Ok(Self::new(rows))
    }

    /// Select columns in the provided order.
    ///
    /// # Errors
    ///
    /// Returns [`RingError::DimensionMismatch`] when a requested column is out of range.
    pub fn select_columns(&self, columns: &[usize]) -> Result<Self, RingError> {
        if columns.is_empty() {
            return Err(RingError::DimensionMismatch(
                "column selection cannot be empty".to_string(),
            ));
        }

        for &column in columns {
            if column >= self.cols {
                return Err(RingError::DimensionMismatch(format!(
                    "column index {} is out of range for width {}",
                    column, self.cols
                )));
            }
        }

        let rows = self
            .rows
            .iter()
            .map(|row| {
                let elements = columns.iter().map(|&column| row[column]).collect();
                RingVector::new(elements)
            })
            .collect();
        Ok(Self::new(rows))
    }

    /// Multiply this matrix by a column vector.
    ///
    /// # Errors
    ///
    /// Returns [`RingError::DimensionMismatch`] or [`RingError::ModulusMismatch`]
    /// when the operands are incompatible.
    pub fn mul_vector(&self, vector: &RingVector) -> Result<RingVector, RingError> {
        if self.cols != vector.len() {
            return Err(RingError::DimensionMismatch(format!(
                "matrix has {} columns but vector has length {}",
                self.cols,
                vector.len()
            )));
        }
        if self.modulus != vector.modulus() {
            return Err(RingError::ModulusMismatch(format!(
                "matrix modulus {} does not match vector modulus {}",
                self.modulus,
                vector.modulus()
            )));
        }

        let entries = self
            .rows
            .iter()
            .map(|row| row.try_dot(vector))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(RingVector::new(entries))
    }

    /// Multiply a row vector by this matrix.
    ///
    /// # Errors
    ///
    /// Returns [`RingError::DimensionMismatch`] or [`RingError::ModulusMismatch`]
    /// when the operands are incompatible.
    pub fn left_mul_vector(&self, vector: &RingVector) -> Result<RingVector, RingError> {
        if self.rows() != vector.len() {
            return Err(RingError::DimensionMismatch(format!(
                "matrix has {} rows but vector has length {}",
                self.rows(),
                vector.len()
            )));
        }
        if self.modulus != vector.modulus() {
            return Err(RingError::ModulusMismatch(format!(
                "matrix modulus {} does not match vector modulus {}",
                self.modulus,
                vector.modulus()
            )));
        }

        self.transpose().mul_vector(vector)
    }

    /// Multiply this matrix by another matrix.
    ///
    /// # Errors
    ///
    /// Returns [`RingError::DimensionMismatch`] or [`RingError::ModulusMismatch`]
    /// when the operands are incompatible.
    pub fn try_mul(&self, other: &Self) -> Result<Self, RingError> {
        if self.cols != other.rows() {
            return Err(RingError::DimensionMismatch(format!(
                "left matrix has {} columns but right matrix has {} rows",
                self.cols,
                other.rows()
            )));
        }
        if self.modulus != other.modulus {
            return Err(RingError::ModulusMismatch(format!(
                "left matrix modulus {} does not match right matrix modulus {}",
                self.modulus, other.modulus
            )));
        }

        let mut rows = Vec::with_capacity(self.rows());
        let other_t = other.transpose();
        for row in &self.rows {
            let entries = other_t
                .rows
                .iter()
                .map(|column| row.try_dot(column))
                .collect::<Result<Vec<_>, _>>()?;
            rows.push(RingVector::new(entries));
        }

        Ok(Self::new(rows))
    }

    /// Compute the inverse of a square matrix with Gauss-Jordan elimination.
    ///
    /// # Errors
    ///
    /// Returns [`RingError::DimensionMismatch`] if the matrix is not square and
    /// [`RingError::SingularMatrix`] if no invertible pivot can be found.
    pub fn inverse(&self) -> Result<Self, RingError> {
        if self.rows() != self.cols {
            return Err(RingError::DimensionMismatch(format!(
                "matrix must be square, got {}x{}",
                self.rows(),
                self.cols
            )));
        }

        let size = self.rows();
        let modulus = self.modulus;
        let mut left: Vec<Vec<RingElement>> =
            self.rows.iter().map(|row| row.elements.clone()).collect();
        let mut right: Vec<Vec<RingElement>> = Self::identity(size, modulus)
            .rows
            .into_iter()
            .map(|row| row.elements)
            .collect();

        for pivot_index in 0..size {
            let pivot_row =
                (pivot_index..size).find(|&row| left[row][pivot_index].inverse().is_some());
            let Some(pivot_row) = pivot_row else {
                return Err(RingError::SingularMatrix(modulus));
            };

            if pivot_row != pivot_index {
                left.swap(pivot_index, pivot_row);
                right.swap(pivot_index, pivot_row);
            }

            let inverse_pivot = left[pivot_index][pivot_index]
                .inverse()
                .ok_or(RingError::SingularMatrix(modulus))?;
            for column in 0..size {
                left[pivot_index][column] = left[pivot_index][column] * inverse_pivot;
                right[pivot_index][column] = right[pivot_index][column] * inverse_pivot;
            }

            for row in 0..size {
                if row == pivot_index {
                    continue;
                }

                let factor = left[row][pivot_index];
                if factor.is_zero() {
                    continue;
                }

                for column in 0..size {
                    left[row][column] = left[row][column] - (factor * left[pivot_index][column]);
                    right[row][column] = right[row][column] - (factor * right[pivot_index][column]);
                }
            }
        }

        let rows = right.into_iter().map(RingVector::new).collect();
        Ok(Self::new(rows))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_identity_matrix() {
        let matrix = RingMatrix::identity(3, 11);
        assert_eq!(
            matrix.to_values(),
            vec![vec![1, 0, 0], vec![0, 1, 0], vec![0, 0, 1]]
        );
    }

    #[test]
    fn test_matrix_vector_mul() {
        let matrix = RingMatrix::from_values(&[vec![1, 2], vec![3, 4]], 11);
        let vector = RingVector::from_values(&[5, 6], 11);
        assert_eq!(matrix.mul_vector(&vector).unwrap().to_values(), vec![6, 6]);
    }

    #[test]
    fn test_matrix_mul() {
        let left = RingMatrix::from_values(&[vec![1, 2], vec![3, 4]], 11);
        let right = RingMatrix::from_values(&[vec![5, 6], vec![7, 8]], 11);
        assert_eq!(
            left.try_mul(&right).unwrap().to_values(),
            vec![vec![8, 0], vec![10, 6]]
        );
    }

    #[test]
    fn test_matrix_inverse() {
        let matrix = RingMatrix::from_values(&[vec![2, 1], vec![5, 3]], 11);
        let inverse = matrix.inverse().unwrap();
        let product = matrix.try_mul(&inverse).unwrap();
        assert_eq!(product.to_values(), vec![vec![1, 0], vec![0, 1]]);
    }

    #[test]
    fn test_permute_columns() {
        let matrix = RingMatrix::from_values(&[vec![1, 2, 3], vec![4, 5, 6]], 13);
        assert_eq!(
            matrix.permute_columns(&[2, 0, 1]).unwrap().to_values(),
            vec![vec![3, 1, 2], vec![6, 4, 5]]
        );
    }
}

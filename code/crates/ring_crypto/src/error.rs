#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum RingError {
    #[error("invalid modulus {0}; expected a value greater than 1")]
    InvalidModulus(u64),
    #[error("dimension mismatch: {0}")]
    DimensionMismatch(String),
    #[error("modulus mismatch: {0}")]
    ModulusMismatch(String),
    #[error("matrix is singular over modulus {0}")]
    SingularMatrix(u64),
}

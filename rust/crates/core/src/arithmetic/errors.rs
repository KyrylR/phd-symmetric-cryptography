use std::fmt;
use std::error::Error;

#[derive(Debug)]
pub enum RingError {
    ZeroModulo,
}

impl fmt::Display for RingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroModulo => f.write_str("ring modulo must be nonzero"),
        }
    }
}

impl Error for RingError {}

//! TBD

use super::errors::RingError;

pub(crate) struct Ring {
    modulo: u64,
}

pub(crate) struct RingItem(u64);

impl Ring {
    pub(crate) fn new(modulo: u64) -> Result<Self, RingError> {
        if modulo == 0 {
            return Err(RingError::ZeroModulo);
        }

        Ok(Self { modulo })
    }
}
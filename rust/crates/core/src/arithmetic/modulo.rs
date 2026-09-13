//! TBD

pub(crate) struct Ring {
    modulo: u64
}

pub(crate) struct RingItem(u64);

impl Ring {
    pub(crate) fn new(modulo: u64) -> Self {
        Self { modulo }
    }
}
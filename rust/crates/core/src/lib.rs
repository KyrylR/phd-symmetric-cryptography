//! TBD
//!
//! # Upstream proof limitations
//!
//! The Aeneas revision used in this project is `6852e6474ec508930acba4df79977b3483a10d10`, selected by Hax 0.4.0.
//!
//! Known model limitations remain at:
//! - [`Slice.lean:367`](https://github.com/cryspen/aeneas/blob/6852e6474ec508930acba4df79977b3483a10d10/backends/lean/Aeneas/Std/Slice.lean#L367): unchecked slice access is opaque.
//! - [`Slice.lean:590`](https://github.com/cryspen/aeneas/blob/6852e6474ec508930acba4df79977b3483a10d10/backends/lean/Aeneas/Std/Slice.lean#L590): indexed unchecked access returns an undefined-operation error.
//! - [`StringIter.lean:17`](https://github.com/cryspen/aeneas/blob/6852e6474ec508930acba4df79977b3483a10d10/backends/lean/Aeneas/Std/StringIter.lean#L17): character iterator collection is opaque.
//!
//! This work would do its best effort to highlight which parts of the formal proofs are affected.

pub mod arithmetic;

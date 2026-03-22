# `sym-adv-ring`

`sym-adv-ring` provides the modular arithmetic primitives shared by the thesis
codebase.

It includes:

- `RingElement` arithmetic over `Z_m`
- `RingVector` and `RingMatrix` helpers
- greatest-common-divisor utilities and modular inversion

The crate is the algebraic foundation used by `sym-adv-encoding`.

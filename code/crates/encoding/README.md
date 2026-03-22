# `sym-adv-encoding`

`sym-adv-encoding` provides byte and UTF-8 encoders that map payloads into
`sym_adv_ring::RingElement` values over `Z_m`.

The crate currently ships two encoding strategies:

- fixed-width bit packing for compact canonical residue streams
- length-delimited base-`m` transduction for self-delimiting payload recovery

The repository also contains a companion Lean 4 formalization for the
length-delimited base-`m` construction in `lean/encoding-dr-1`.

That formalization proves:

- fixed-width base-`m` prefix encoding and decoding are inverse on `u64` values
- whole-stream recovery for the deployed `length || state || payload` format
- trailing residue padding does not change the decoded byte string
- every emitted symbol is a valid residue `< modulus`

It does not prove Rust implementation equivalence, allocator behavior, or the
bit-packing encoder/decoder path.

# All commands should be run with Nix environment

extract:
    cd rust/crates/core && hax-lean

lean: extract
    cd rust/crates/core/proofs/lean && lake build

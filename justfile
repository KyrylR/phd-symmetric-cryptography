# All commands should be run with Nix environment

check:
    cargo fmt --manifest-path rust/Cargo.toml --all -- --check
    cargo build --manifest-path rust/Cargo.toml --workspace --all-targets --all-features --locked
    cargo test --manifest-path rust/Cargo.toml --workspace --all-targets --all-features --locked
    cargo test --manifest-path rust/Cargo.toml --workspace --doc --all-features --locked
    cargo clippy --manifest-path rust/Cargo.toml --workspace --all-targets --all-features --locked
    cargo doc --manifest-path rust/Cargo.toml --workspace --all-features --no-deps --locked
    just lean

fix:
    cargo clippy --manifest-path rust/Cargo.toml --workspace --all-targets --all-features --locked --fix --allow-dirty --allow-staged
    cargo fmt --manifest-path rust/Cargo.toml --all

extract:
    cd rust/crates/core && hax-lean

lean: extract
    cd rust/crates/core/proofs/lean && lake build

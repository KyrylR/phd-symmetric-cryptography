# Rust-to-Lean tooling

From the repository root on Apple Silicon macOS:

```sh
nix develop
just lean
```

For a single run, use `nix develop --command just lean`. `just extract`
regenerates Lean without building it. First use needs network access to download
the pinned Rust toolchain, extractors, and Lean dependencies.

The project flake uses public, pinned dependencies. It does not import a private
Nix configuration. `flake.lock` pins nixpkgs; the flake pins Hax 0.4.0 and checks
its archive hash. `rust/rust-toolchain.toml` selects the compiler and components.
`rust/hax.toml` pins Charon, Aeneas, Lean, and the Hax Lean library.

The environment provides `hax-lean`. It prepares a standard-library cache keyed
by Rust nightly and platform, then passes that cache explicitly to Charon.
Repeated runs reuse it. Old Hax binary overrides are ignored. Ordinary Miri
commands use a different cache and cannot replace this one.

Lean source and dependency pins live under `rust/crates/core/proofs/lean`.
After changing only handwritten Lean, run `lake build` there inside the Nix
environment. A successful build is not a correspondence proof.

Upgrade Hax, its extractor bundle, the Rust toolchain, and the Lean pins together.
Check extraction and Lean compilation with an empty cache before accepting an
upgrade. Other operating systems are not configured yet.

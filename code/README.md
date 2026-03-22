# Code Workspace

This workspace contains the Rust implementation work for the thesis codebase.

## Crates

- `sym-adv-ring`: reusable arithmetic over `Z_m`, including ring elements,
  vectors, matrices, and modular matrix inversion.
- `sym-adv-encoding`: UTF-8 and byte encoders for mapping payloads into ring
  elements.

## Run Tests

From the repository root:

```bash
./scripts/check-crates.sh
```

Run only the `sym-adv-encoding` tests:

```bash
cd code
cargo test -p sym-adv-encoding
```

## Format And Lint

Format the entire workspace:

```bash
cd code
cargo fmt --all
```

Run the strict clippy gate used for this workspace:

```bash
cd code
cargo clippy --all-targets --all-features -- -D warnings -D clippy::all -D clippy::pedantic -D clippy::nursery -D clippy::cargo -A clippy::multiple_crate_versions
```

Apply automated clippy fixes where possible:

```bash
cd code
cargo clippy --all-targets --all-features --fix --allow-dirty --allow-staged -- -D warnings -D clippy::all -D clippy::pedantic -D clippy::nursery -D clippy::cargo -A clippy::multiple_crate_versions
```

## Release Flow

Preview the next release without changing Git state:

```bash
./scripts/release-crates.sh patch --dry-run
```

Create a real signed release commit and tag:

```bash
./scripts/release-crates.sh patch
```

The release script requires:

- a clean git working tree with an existing `HEAD`
- `git config user.signingkey ...`
- `git config gpg.format ssh` when the signing key is an SSH key

## Trusted Publishing Bootstrap

Trusted publishing on crates.io is a one-time bootstrap:

1. Push the repository changes so the GitHub Actions workflows exist on GitHub.
2. Run the signed release flow locally.
3. Publish the first tagged release manually:

```bash
cd code
cargo publish -p sym-adv-ring
cargo publish -p sym-adv-encoding
```

4. Register `.github/workflows/publish-crates.yml` as the trusted publisher for
   both crates on crates.io, using the `crates-io-publish` GitHub environment.
5. Set the GitHub repository variable
   `CRATES_IO_TRUSTED_PUBLISHING_ENABLED=true`.

#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
workspace_dir="$repo_root/code"

step() {
    printf '\n==> %s\n' "$1"
}

read_workspace_version() {
    awk '
        /^\[workspace\.package\]/ { in_section = 1; next }
        /^\[/ { in_section = 0 }
        in_section && $1 == "version" {
            gsub(/"/, "", $3)
            print $3
            exit
        }
    ' "$workspace_dir/Cargo.toml"
}

crate_version_exists() {
    local crate_name="$1"
    local version="$2"

    curl --silent --show-error --fail \
        "https://crates.io/api/v1/crates/${crate_name}/${version}" \
        >/dev/null 2>&1
}

cd "$workspace_dir"

step "cargo fmt --all --check"
cargo fmt --all --check

step "cargo clippy --workspace --all-targets --all-features"
cargo clippy --workspace --all-targets --all-features --locked -- \
    -D warnings \
    -D clippy::all \
    -D clippy::pedantic \
    -D clippy::nursery \
    -D clippy::cargo \
    -A clippy::multiple_crate_versions

step "cargo test -p sym-adv-ring"
cargo test -p sym-adv-ring --locked

step "cargo test -p sym-adv-encoding"
cargo test -p sym-adv-encoding --locked

step "cargo bench -p sym-adv-encoding --bench base_m_len --no-run"
cargo bench -p sym-adv-encoding --bench base_m_len --no-run --locked

step "cargo publish --dry-run -p sym-adv-ring"
cargo publish --dry-run -p sym-adv-ring --locked --allow-dirty

workspace_version="$(read_workspace_version)"
if crate_version_exists sym-adv-ring "$workspace_version"; then
    step "cargo publish --dry-run -p sym-adv-encoding"
    cargo publish --dry-run -p sym-adv-encoding --locked --allow-dirty
else
    step "cargo package --list -p sym-adv-encoding"
    printf 'sym-adv-ring %s is not on crates.io yet; using package-shape verification for sym-adv-encoding\n' \
        "$workspace_version"
    cargo package -p sym-adv-encoding --allow-dirty --list >/dev/null
fi

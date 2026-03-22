#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
workspace_manifest="$repo_root/code/Cargo.toml"
workspace_dir="$repo_root/code"

usage() {
    cat <<'EOF'
Usage: ./scripts/release-crates.sh patch|minor|major [--dry-run]

Creates a signed release commit and signed annotated tag for the sym-adv crates.
EOF
}

die() {
    printf 'error: %s\n' "$1" >&2
    exit 1
}

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
    ' "$workspace_manifest"
}

bump_version() {
    local current="$1"
    local kind="$2"
    local major minor patch

    IFS=. read -r major minor patch <<<"$current"
    [[ "$major" =~ ^[0-9]+$ && "$minor" =~ ^[0-9]+$ && "$patch" =~ ^[0-9]+$ ]] \
        || die "workspace version must be semantic version x.y.z"

    case "$kind" in
        patch)
            patch=$((patch + 1))
            ;;
        minor)
            minor=$((minor + 1))
            patch=0
            ;;
        major)
            major=$((major + 1))
            minor=0
            patch=0
            ;;
        *)
            die "release kind must be one of: patch, minor, major"
            ;;
    esac

    printf '%s.%s.%s\n' "$major" "$minor" "$patch"
}

require_clean_git_state() {
    git -C "$repo_root" rev-parse --verify HEAD >/dev/null 2>&1 \
        || die "release requires an existing HEAD commit"

    if [[ -n "$(git -C "$repo_root" status --porcelain --untracked-files=all)" ]]; then
        die "release requires a clean working tree"
    fi
}

require_signing_configuration() {
    local signing_key gpg_format

    signing_key="$(git -C "$repo_root" config --get user.signingkey || true)"
    gpg_format="$(git -C "$repo_root" config --get gpg.format || true)"

    [[ -n "$signing_key" ]] || die "git user.signingkey is not configured"

    case "$signing_key" in
        *.pub|ssh-*)
            [[ "$gpg_format" == "ssh" ]] \
                || die "git signing key looks like SSH; set `git config gpg.format ssh`"
            ;;
    esac
}

update_workspace_version() {
    local new_version="$1"

    NEW_VERSION="$new_version" perl -0pi -e '
        s/(\[workspace\.package\][\s\S]*?\nversion = ")([^"]+)(")/$1.$ENV{NEW_VERSION}.$3/e;
    ' "$workspace_manifest"

    NEW_VERSION="$new_version" perl -0pi -e '
        s/(sym-adv-ring = \{ version = "=)([^"]+)(", path = "crates\/ring_crypto" \})/$1.$ENV{NEW_VERSION}.$3/e;
    ' "$workspace_manifest"
}

main() {
    local release_kind dry_run current_version next_version tag_name commit_message branch_name

    [[ $# -ge 1 && $# -le 2 ]] || {
        usage
        exit 1
    }

    if [[ "${1:-}" == "--help" || "${1:-}" == "-h" ]]; then
        usage
        exit 0
    fi

    release_kind="$1"
    dry_run="false"

    if [[ $# -eq 2 ]]; then
        [[ "$2" == "--dry-run" ]] || die "only optional flag supported is --dry-run"
        dry_run="true"
    fi

    require_clean_git_state
    require_signing_configuration

    branch_name="$(git -C "$repo_root" symbolic-ref --quiet --short HEAD 2>/dev/null || true)"
    [[ -n "$branch_name" ]] || die "release requires a checked out branch"

    current_version="$(read_workspace_version)"
    [[ -n "$current_version" ]] || die "failed to read workspace version"

    next_version="$(bump_version "$current_version" "$release_kind")"
    tag_name="sym-adv-v${next_version}"
    commit_message="release: sym-adv v${next_version}"

    git -C "$repo_root" rev-parse --verify "refs/tags/${tag_name}" >/dev/null 2>&1 \
        && die "tag ${tag_name} already exists"

    step "running release checks on ${current_version}"
    "$repo_root/scripts/check-crates.sh"

    if [[ "$dry_run" == "true" ]]; then
        printf '\nDry run only. Planned release:\n'
        printf '  current version: %s\n' "$current_version"
        printf '  next version:    %s\n' "$next_version"
        printf '  commit message:  %s\n' "$commit_message"
        printf '  tag name:        %s\n' "$tag_name"
        printf '  push target:     origin %s and %s\n' "$branch_name" "$tag_name"
        exit 0
    fi

    step "bumping workspace version to ${next_version}"
    update_workspace_version "$next_version"

    if [[ "$(read_workspace_version)" != "$next_version" ]]; then
        die "version bump did not update code/Cargo.toml as expected"
    fi

    step "refreshing Cargo.lock"
    (cd "$workspace_dir" && cargo check --workspace >/dev/null)

    step "rerunning release checks on ${next_version}"
    "$repo_root/scripts/check-crates.sh"

    step "creating signed release commit"
    git -C "$repo_root" add code/Cargo.toml code/Cargo.lock
    git -C "$repo_root" commit -S -m "$commit_message"

    step "creating signed annotated tag ${tag_name}"
    git -C "$repo_root" tag -s "$tag_name" -m "$tag_name"

    if [[ "$(git -C "$repo_root" rev-parse "${tag_name}^{}")" != "$(git -C "$repo_root" rev-parse HEAD)" ]]; then
        die "tag ${tag_name} does not point to the release commit"
    fi

    step "pushing branch ${branch_name}"
    git -C "$repo_root" push origin "$branch_name"

    step "pushing tag ${tag_name}"
    git -C "$repo_root" push origin "$tag_name"
}

main "$@"

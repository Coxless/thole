#!/usr/bin/env bash
# The checks of the project, shared by CI (.github/workflows/ci.yml) and the
# workshop actions (.workshop/dev.yaml). Change them here, nowhere else.
#
# Usage: scripts/check.sh <rust|python|lean|oracle|package|all>...
set -euo pipefail
cd "$(dirname "$0")/.."

check_rust() {
    cargo fmt --all --check
    cargo clippy --workspace --all-targets --all-features --locked -- -D warnings
    cargo test --all-features --locked
    cargo test --no-default-features --locked
    RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --all-features --locked
    scripts/check-pure-rust.sh
}

# Rebuilds the bindings, then runs the Python tests of every area.
check_python() {
    cd bindings/python
    uv sync --locked --reinstall-package thole
    uv run pytest
}

check_lean() {
    lake build
    if grep -rnw --include='*.lean' sorry crates oracle; then
        echo "error: sorry found in the Lean proofs" >&2
        return 1
    fi
}

# Checks the results of the Rust code against the Lean definitions. Needs both
# toolchains: Lean builds the oracle executable, and the Rust tests run it.
check_oracle() {
    lake build thole-oracle
    cargo test -p thole-oracle --locked
}

# Verifies that the crates can be packaged for crates.io. Nothing is uploaded.
check_package() {
    cargo publish --workspace --dry-run --locked
}

if [[ $# -eq 0 ]]; then
    echo "usage: $0 <rust|python|lean|oracle|package|all>..." >&2
    exit 2
fi
for target in "$@"; do
    case "$target" in
        rust | python | lean | oracle | package) (check_"$target") ;;
        all) for t in rust python lean oracle package; do (check_"$t"); done ;;
        *)
            echo "unknown check: $target" >&2
            exit 2
            ;;
    esac
done

#!/usr/bin/env bash
# Publishes the crates of the workspace to crates.io, dependencies first.
#
# Unlike `cargo publish --workspace`, a run can be repeated and survives the
# rate limit of crates.io:
# - A crate whose version is already on crates.io is skipped, so running the
#   script again after a failure publishes only what is missing.
# - crates.io limits how many new crate names an account may create in a short
#   time. When it answers 429, the script waits and tries the same crate again.
#
# Usage: scripts/publish-crates.sh [--dry-run]
#   --dry-run  list what would be published; upload nothing
#
# Environment:
#   CARGO_REGISTRY_TOKEN  crates.io API token (read by cargo)
#   PUBLISH_RETRY_WAIT    seconds to wait after a 429 (default 600)
#   PUBLISH_MAX_ATTEMPTS  attempts per crate (default 7)
set -euo pipefail
cd "$(dirname "$0")/.."

dry_run=false
case "${1-}" in
    '') ;;
    --dry-run) dry_run=true ;;
    *)
        echo "usage: $0 [--dry-run]" >&2
        exit 2
        ;;
esac

retry_wait=${PUBLISH_RETRY_WAIT:-600}
max_attempts=${PUBLISH_MAX_ATTEMPTS:-7}
# crates.io rejects requests without a user agent that identifies the caller.
user_agent='thole-release (https://github.com/Coxless/thole)'

# "name version" of every publishable workspace member, dependencies first.
crates=$(cargo metadata --format-version 1 --no-deps | python3 -c '
import graphlib, json, sys
packages = {
    p["name"]: p
    for p in json.load(sys.stdin)["packages"]
    if p["publish"] != []  # `publish = false` is reported as an empty list
}
graph = {
    name: {d["name"] for d in p["dependencies"] if d["name"] in packages}
    for name, p in packages.items()
}
for name in graphlib.TopologicalSorter(graph).static_order():
    print(name, packages[name]["version"])
')

# Succeeds if the given version of the crate is on crates.io.
is_published() {
    local status
    status=$(curl -sS -o /dev/null -w '%{http_code}' -A "$user_agent" \
        "https://crates.io/api/v1/crates/$1/$2")
    case "$status" in
        200) return 0 ;;
        404) return 1 ;;
        *)
            echo "error: crates.io answered $status for $1 $2" >&2
            exit 1
            ;;
    esac
}

publish() {
    local name=$1 log attempt
    log=$(mktemp)
    for ((attempt = 1; attempt <= max_attempts; attempt++)); do
        if cargo publish -p "$name" --locked 2>&1 </dev/null | tee "$log"; then
            return 0
        fi
        if ! grep -q 'status 429' "$log"; then
            return 1
        fi
        echo "rate limited by crates.io; waiting ${retry_wait}s (attempt $attempt of $max_attempts)"
        sleep "$retry_wait"
    done
    echo "error: $name is still rate limited after $max_attempts attempts" >&2
    return 1
}

while read -r name version; do
    if is_published "$name" "$version"; then
        echo "skip     $name $version (already on crates.io)"
    elif $dry_run; then
        echo "publish  $name $version (dry run)"
    else
        echo "publish  $name $version"
        publish "$name"
    fi
done <<<"$crates"

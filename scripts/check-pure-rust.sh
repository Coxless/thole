#!/usr/bin/env bash
# Fails if a computational crate depends on a `-sys` crate, on any crate that
# links a native library, or on the Python bindings (CONCEPT.md section 3.1).
# thole-py itself is excluded: it links against libpython by design.
set -euo pipefail
cd "$(dirname "$0")/.."

deps=$(cargo tree --workspace --exclude thole-py --edges normal,build --prefix none --format '{p}' |
    awk '{print $1}' | sort -u)

# Names of all packages in the lockfile that declare a `links` key.
native=$(cargo metadata --format-version 1 | python3 -c '
import json, sys
for p in json.load(sys.stdin)["packages"]:
    if p.get("links"):
        print(p["name"])
' | sort -u)

bad=$(
    grep -E -- '-sys$' <<<"$deps" || true
    grep -Fx 'thole-py' <<<"$deps" || true
    comm -12 <(echo "$deps") <(echo "$native")
)

if [[ -n "$bad" ]]; then
    echo "pure Rust check failed; forbidden dependencies:" >&2
    sort -u <<<"$bad" | sed 's/^/  /' >&2
    exit 1
fi
echo "pure Rust check passed"

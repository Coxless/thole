# thole

Pure Rust, no C/Fortran: scientific computing with every algorithm implemented from scratch.

A family of scientific computing crates written in pure Rust. It does not rely on external computation engines such as BLAS or LAPACK: every numerical algorithm is implemented from scratch. Everything is callable from Python. The algorithms are also defined in Lean 4: their mathematical properties are proved there, and the results of the Rust code are checked against those definitions.

**Status: early development.** Bisection is complete. Brent's method lacks one of its two oracle checks, the comparison with the Lean definitions. The principles and the roadmap are in [CONCEPT.md](CONCEPT.md).

```rust
use thole::roots::{Options, bisect};

let root = bisect(|x| x * x - 2.0, 0.0, 2.0, &Options::default())?;
assert!((root.x - 2.0_f64.sqrt()).abs() < 1e-11);
```

```python
from thole.roots import bisect

root = bisect(lambda x: x * x - 2, 0, 2)
assert abs(root.x - 2**0.5) < 1e-11
```

## Layout

| Path | Contents |
|---|---|
| `crates/thole` | Facade that re-exports the other crates |
| `crates/thole-core` | Shared parts: scalar traits, error types, tolerances |
| `crates/thole-roots` | Root finding |
| `crates/thole-quad` | Numerical integration |
| `crates/thole-linalg` | Matrix types, LU decomposition and so on |
| `crates/thole-ode` | Ordinary differential equations |
| `bindings/python` | The Python package `thole` (PyO3 + maturin) |
| `oracle` | The Lean oracle and the tests that check the Rust results against it. Not published |

Each area keeps its Lean definitions and proofs in `crates/<crate>/lean/`, its Python tests in `crates/<crate>/python/` and its notebooks in `crates/<crate>/notebooks/`, next to the Rust code in `src/`.

| Area | Algorithm | Lean proofs | Oracle checks |
|---|---|---|---|
| `thole-roots` | Bisection: `thole::roots::bisect`, `thole.roots.bisect` | [`Bisection.lean`](crates/thole-roots/lean/Thole/Roots/Bisection.lean): the bracket always contains a root; error at most `(b - a) / 2 ^ (n + 1)` after `n` steps; guarantee of the stopping criterion; convergence. | [`Roots.lean`](oracle/lean/Thole/Oracle/Roots.lean): the same outcome, step count and bracket as the Lean definitions where `f64` arithmetic is exact; the proved properties up to rounding for any finite input. |
| `thole-roots` | Brent's method: `thole::roots::brent`, `thole.roots.brent` | [`Brent.lean`](crates/thole-roots/lean/Thole/Roots/Brent.lean): a root always lies between the approximation and the point of opposite sign; guarantee of the stopping criterion; the iteration stops, after at most `2 * (b - a) / t` steps for a tolerance of at least `t`. | [`Roots.lean`](oracle/lean/Thole/Oracle/Roots.lean): the proved properties up to rounding for any finite input. The comparison with the Lean definitions is still to come: an interpolation step is never exact in `f64`. |

## Development

The development environment is provided by [Canonical Workshop](https://ubuntu.com/workshop/docs/). Rust, Python (uv) and Lean (elan) exist only inside the workshop; nothing needs to be installed on the host.

```sh
workshop launch          # first time only: build and start the environment
workshop start           # resume it if it is stopped
workshop run -- setup    # fetch dependencies, create the Python environment, fetch Lean and Mathlib (about 8 GB under .lake/)

workshop run -- test     # cargo test (arguments are passed through)
workshop run -- fmt      # cargo fmt
workshop run -- check    # everything CI runs
workshop run -- check rust     # or: python, lean, oracle, package
workshop run -- notebook # JupyterLab with Python and Rust kernels

workshop exec -- cargo <args>   # one-off command
workshop shell                  # open a shell inside
workshop refresh                # after changing base / sdks / hooks under .workshop/
```

### The oracle

Each algorithm is defined once in Lean, over any ordered field (`crates/<crate>/lean/.../Defs.lean`). The theorems are about that definition over the real numbers. The same definition runs over the rational numbers, with exact arithmetic, in the executable `thole-oracle`, and the tests in `oracle/tests/` use it to judge what the Rust code returns: they draw polynomials and arguments at random, call the Rust function, and send the call and its result to the oracle.

```sh
workshop run -- check oracle                    # build the oracle and run the tests
workshop exec -- cargo test -p thole-oracle     # the tests alone, once `lake build` has run
```

The oracle is a separate process and exists only for these tests. The published crates contain Rust only and do not depend on it. `cargo test` at the root does not run these tests, so it needs no Lean.

A failing input is written to `oracle/tests/<area>.proptest-regressions`. Commit that file: the input is tried first from then on.

### Notebooks

The notebooks in `crates/<crate>/notebooks/` exercise an algorithm by hand, from Python and from Rust: reference values, the quantities the Lean theorems predict, failures and edge cases. They complement the tests and are not run by CI.

`workshop run -- notebook` starts JupyterLab inside the workshop and prints the URL to open from the host. The Python kernel uses `thole` rebuilt from the working tree; the Rust kernel ([evcxr](https://github.com/evcxr/evcxr)) is installed the first time, which takes a few minutes. After changing the Rust code, restart the action for the Python kernel, or run the `:dep` cell again in a Rust notebook.

Notebooks are committed without outputs: clear them before committing (Edit > Clear Outputs of All Cells).

### Branches and CI

The repository follows [GitHub flow](https://docs.github.com/en/get-started/using-github/github-flow). `main` is the only long-lived branch and is always releasable.

1. Create a short-lived branch from the latest `main`, one per change.
2. Push it and open a pull request against `main`, as a draft if it is not ready.
3. Merge once the `ci` check passes. The branch is deleted on merge.

`main` is protected: changes reach it only through a pull request, the `ci` check must pass, and the branch must be up to date with `main` before it is merged.

CI runs on pull requests only: once when one is opened, and once for every push to its branch after that. A branch with no open pull request is not checked, so open the pull request early or run `workshop run -- check`. It runs only the jobs whose files have changed (Rust, Python, Lean, and the oracle when either Rust or Lean has), and all of them call `scripts/check.sh`, the same script as `workshop run -- check`.

### Releasing

The crates and the Python package share one version, set in the root `Cargo.toml` (`workspace.package.version` and the `workspace.dependencies` entries).

1. Bump the version on a branch and merge it into `main` through a pull request, like any other change.
2. Tag the resulting commit on `main` `v<version>` and push the tag.

The `Release` workflow then runs every check, builds the Linux wheels (x86_64 and aarch64) and the sdist, publishes the crates to crates.io and the package to PyPI, and creates a GitHub release. Running the workflow by hand from the Actions tab does everything except the uploads.

The crates are published by `scripts/publish-crates.sh`, one at a time and dependencies first. It skips a crate whose version is already on crates.io, and when crates.io limits how many new crates may be created in a short time it waits and tries again. A release that adds many crates therefore takes longer but does not fail, and if the job does fail, running it again publishes only what is missing. `scripts/publish-crates.sh --dry-run` lists what would be published.

## License

Licensed under either of [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE), at your option.

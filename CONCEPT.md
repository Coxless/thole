# thole concept

A family of scientific computing crates written in pure Rust.

- Status: early development (created 2026-10-11)
- Role of this document: the reference to return to when a design or implementation question has no obvious answer. When a decision changes, update this document first.

## 1. Name

A **thole** (thole pin) is the pivot that holds an oar and transfers the rower's force to the boat.

- It stands for a foundation that other computations rest on.
- In archaic English and in Scots, "thole" is also a verb meaning "to endure, to bear patiently". That fits the long road of writing everything ourselves.
- Rowing is a human-powered sport with no engine. That matches the policy of not relying on external computation engines such as BLAS and LAPACK.

The name alone does not say that the project is pure Rust, so the first line of the README and of every crates.io description must say "pure Rust, no C/Fortran".

## 2. Motivation

The project exists because we want to build it, not because there is demand for it.

- To understand numerical algorithms by implementing them by hand.
- To have a computing library whose internals can be followed in Rust all the way down.

From this motivation, the priorities for any trade-off are:

1. Correctness
2. Code that can be read and understood
3. An API that is easy to use
4. Speed

Speed can be improved later. Correctness and readability are hard to add afterwards.

## 3. Principles

### 3.1 Pure Rust only

- Do not link against C or Fortran code or libraries (BLAS, LAPACK, FFTW, HDF5 and so on).
- No `-sys` crate in the dependency tree.
- `cargo add` is enough to build. No C compiler or gfortran is required.

This principle applies to the computational crates (everything under `crates/`). The Python bindings (`bindings/python`) link against libpython and are exempt. In return, the computational crates must never depend on the bindings.

### 3.2 Implement the numerical algorithms ourselves

- Do not delegate computation to other pure Rust crates either (faer, nalgebra, ndarray, rustfft and so on).
- Keep dependencies to a minimum. Which dependencies are allowed is an open question (section 9).
- Consulting existing implementations and the literature is fine. Cite what was consulted in a code comment or in the documentation.

### 3.3 Finish small pieces

- Bring one area to a state where its tests and documentation are complete before moving on to the next.
- Build foundations such as the matrix type from the features that are actually needed. Do not build ahead of need.

An area is "finished" when all four of these exist:

1. The Rust implementation and its reference-value tests
2. Documentation
3. Python bindings and their tests (3.4)
4. Lean proofs of the mathematical properties (3.5). If a property is left unproved, the documentation says why.

### 3.4 Everything is callable from Python

- Every public Rust function and type has a corresponding Python API. No public feature exists in Rust only.
- The bindings live in a single crate, `bindings/python` (PyO3 + maturin), distributed as the Python package `thole`.
- The Python tests of an area, and the scripts that generate its reference values, live next to the Rust code in `crates/<crate>/python/`.
- The bindings are a thin conversion layer. They contain no computational logic.
- The Python API follows Python conventions (exceptions, keyword arguments). API compatibility with SciPy or NumPy is not a goal (section 4).

### 3.5 Mathematical rigor through Lean

- For each algorithm, the mathematical properties it relies on (convergence, error bounds, order, existence and uniqueness of a factorization, and so on) are formalized and proved in Lean 4. The proofs are checked by `lake build`.
- The Rust documentation names the corresponding theorem, and the Lean side names the corresponding Rust function.
- The proofs of a crate live next to its Rust code, in `crates/<crate>/lean/`. An algorithm is defined as a function on the real numbers, written to follow the structure of the Rust code step by step, and the theorems are stated about that definition.
- The proofs build on Mathlib. Its release tag in `lakefile.toml` and the Lean version in `lean-toolchain` are upgraded together.
- Mathlib is a dependency of the proofs only. It does not affect the Rust crates or 3.2.

Be clear about what Lean does and does not guarantee.

- Guaranteed: the mathematical properties of the algorithm as defined over the real numbers.
- Not guaranteed: that the Rust code matches that definition, and the effect of floating-point rounding.

The part that is not guaranteed is covered by reference-value tests and hard-input tests (section 7). Verifying the Rust code itself in Lean (with Aeneas or a similar tool) is an open question (section 9).

### 3.6 English only

- Everything in the repository is written in English: code, comments, documentation, commit messages, issues.
- The project is meant to be used worldwide.

## 4. Non-goals

- Competing on speed with existing libraries (at least in the early stages).
- API compatibility with SciPy or NumPy.
- GPU support.
- Machine learning frameworks, DataFrames, plotting.

## 5. Layout

Everything is in one repository, split into several crates with a Cargo workspace. The unit of organization is the area: one directory per area holds its Rust code, its Lean proofs and its Python tests side by side.

```
thole/
├── Cargo.toml            # Cargo workspace
├── lakefile.toml         # Lake package: one Lean library per crate
├── CONCEPT.md
├── crates/
│   ├── thole-core/       # shared parts: scalar traits, error types, tolerances
│   ├── thole-roots/      # root finding
│   │   ├── src/          #   Rust implementation
│   │   ├── lean/         #   Lean proofs (module namespace Thole.Roots)
│   │   └── python/       #   Python tests and reference-value generators
│   ├── thole-quad/       # numerical integration
│   ├── thole-linalg/     # matrix types, LU decomposition and so on
│   ├── thole-ode/        # ordinary differential equations
│   └── thole/            # facade that re-exports the other crates
├── bindings/
│   └── python/           # thole-py: the Python package `thole`, built with PyO3
├── scripts/              # checks shared by CI and local development
└── .workshop/            # development environment definition (section 8)
```

Adding an area means adding one directory under `crates/`, one `[[lean_lib]]` entry in `lakefile.toml`, one feature in the facade crate, and one module in the bindings.

- Crate names follow the pattern `thole-<area>`.
- Users pick the areas they need through feature flags of the facade crate `thole`. Depending on an individual crate directly also works.
- The Rust side of the bindings stays in the single crate `bindings/python`, with one module per area. Putting PyO3 code into the area crates would break 3.1, and one crate gives one wheel.
- The `lean/` and `python/` directories are excluded from the packages published to crates.io.
- `thole-py` is a workspace member but is not in `default-members`. `cargo build` and `cargo test` at the root work without Python.
- Benchmarks and examples go into each crate's `benches/` and `examples/` when the first algorithm is implemented.
- The crate split above is an initial proposal. Revisit it as the implementation progresses.

## 6. What to build first

Proceed in the following order (initial proposal). Every stage must meet all four points of 3.3 before the next one starts.

### Stage 1: root finding and numerical integration (one variable)

- Root finding: bisection, Brent's method, Newton's method
- Numerical integration: Gauss-Legendre, adaptive Gauss-Kronrod

No matrix type is needed, so work can start right away. This stage settles the following five conventions for the whole library.

- How functions (closures) are accepted
- How tolerances and iteration limits are specified
- How failures are reported (error types)
- How the API appears in Python (how Python callables are accepted, how errors map to exceptions)
- The granularity of the Lean formalization (what is stated as a theorem, and how it maps to the Rust code)

The shared parts that come out of this go into `thole-core`.

Decided with bisection, the first algorithm:

- **Functions**: taken as `impl FnMut(f64) -> f64`. The scalar type is fixed to `f64` until the scalar traits of stage 2 exist.
- **Tolerances**: `thole_core::Tolerance` has an absolute and a relative part; an error is accepted when it is at most `abs + rel * |x|`. It has no default. Each area has an `Options` struct (tolerance, iteration limit) that implements `Default`, passed by reference as the last argument.
- **Failures**: every fallible function returns `Result`. Each area has one `#[non_exhaustive]` `Error` enum whose variants carry the values needed to understand the failure. Invalid input is an error, never a panic. A NaN returned by the user's function is an error.
- **Python**: one submodule per area (`thole.roots`). Options become keyword-only arguments, with `None` meaning the Rust default. Invalid input raises `ValueError`; a failure to converge raises the area's `ConvergenceError`, a `RuntimeError`. An exception raised by the user's function propagates unchanged. Results are read-only objects.
- **Lean**: the iteration is defined over the real numbers with one definition per step of the Rust loop. The Rust documentation lists the theorems under a `# Proofs` heading, and the Lean file header has a table that maps definitions to Rust code. Where Rust must deviate for floating-point reasons (sign comparison instead of a product, an overflow-free midpoint), the Rust comment says so.
- **Tests that tie the two together**: where a Lean theorem predicts an exact quantity (the number of steps for a given tolerance, the width of the bracket), a Rust test checks that quantity.

### Stage 2: core and dense matrix basics

- Scalar traits (f32 and f64 first)
- `Matrix` and `Vector` types with basic operations (addition, subtraction, matrix product, transpose)

Keep this to the minimum that lets the LU decomposition of stage 3 be written.

### Stage 3: LU decomposition and linear systems

- LU decomposition with partial pivoting
- `solve`, determinant, inverse

This is where the usability of the matrix type is tested. Go back and fix stage 2 if needed.

### Stage 4: ordinary differential equations (explicit methods)

- RK4
- Adaptive-step Dormand-Prince 5(4)

### Candidates after that

Cholesky decomposition, QR decomposition, eigenvalues, SVD, interpolation, special functions, optimization, statistics, FFT, sparse matrices, PDEs. The order will be decided from the experience gained up to stage 4.

## 7. Quality policy

- **Reference-value tests**: every algorithm has tests that compare against an analytic solution or against values produced by a trusted implementation (SciPy, LAPACK and so on). How the reference values were generated is recorded too.
- **Hard-input tests**: include ill-conditioned matrices, nearly singular problems, problems that do not converge, and the like.
- **One definition of the checks**: `scripts/check.sh` is run both by CI and by `workshop run -- check`. CI runs only the checks whose files have changed.
- **Pure Rust check**: CI verifies that no `-sys` crate is in the dependency tree of the computational crates (`scripts/check-pure-rust.sh`).
- **Python tests**: every Python API has pytest tests. They use the same reference values as the Rust side.
- **Lean check**: `lake build` must pass in CI. Nothing containing `sorry` is merged into main.
- **Documentation**: every public function documents what it computes, the algorithm used, its preconditions, when it fails, and the corresponding Lean theorem.
- **Benchmarks**: provided to know the speed gap to existing libraries. Winning is not the goal.

## 8. Development environment

The development environment is provided by [Canonical Workshop](https://ubuntu.com/workshop/docs/) (LXD system containers). It is defined in `.workshop/dev.yaml`. Rust, Python and Lean exist only inside the workshop and are not installed on the host.

| Purpose | Source | Version pinned in |
|---|---|---|
| Rust | `rust` SDK (rustup) | `rust-toolchain.toml` |
| Python | `uv` SDK | `bindings/python/pyproject.toml` and `uv.lock` |
| Lean | in-project SDK `.workshop/elan/` (elan) | `lean-toolchain` |

The workshop also installs `build-essential`. Rust invokes `cc` as its linker; no C code is compiled. This does not conflict with 3.1.

## 9. Open questions

When one is decided, move it from this section to the section it belongs to.

| Item | Options and notes |
|---|---|
| Allowed dependencies | Standard library only, or allow foundational crates such as `num-traits`? Treating development-only dependencies for tests and benchmarks (`criterion`, `proptest` and so on) as a separate category seems practical. |
| `unsafe` | Forbid it entirely (`#![forbid(unsafe_code)]`), or allow it only where performance requires it, such as SIMD? |
| License | MIT OR Apache-2.0, the Rust convention, is in place provisionally. Confirm before publishing. |
| Supported Rust version (MSRV) | Follow the latest stable, or fix a lower bound? At present `rust-toolchain.toml` just says `stable`. |
| `no_std` | Support it from the start, or later? |
| Matrix type design | Sizes in the type or not, how to separate owned data from views, row-major or column-major. To be decided in stage 2. |
| Complex numbers | When to implement them ourselves. Should the scalar traits be designed with complex numbers in mind from the start? |
| Passing arrays to and from Python | Start with lists only, accept the buffer protocol, or support NumPy (adding the `numpy` crate as a dependency)? To be decided in stage 2. |
| Cost of calling Python functions | Root finding and integration call a Python function from Rust repeatedly, which is slow. Accepted for now. |
| Verifying the Rust code | Use a tool such as Aeneas that translates Rust to Lean? Decide after checking how well it handles floating point and closures. |
| Floating-point error | Treat rounding error bounds in Lean, or cover them with tests only? |
| GitHub repository name | The user name `thole` is already taken, so it cannot be used as an organization name. Use another name such as `thole-rs`, or keep the repository under a personal account. |
| Reserving names on crates.io and PyPI | `thole` was unregistered on both as of 2026-10-11. Reserve it early. |

## 10. Reference: similar existing projects

Their goals differ, so they are not seen as competitors, but their designs are useful references.

- **peroxide**: many areas in a single crate. Has its own matrix type and uses BLAS/LAPACK for some features.
- **SciRS2**: a workspace of crates aiming at SciPy compatibility.
- **russell**: one crate per area.
- **faer**: pure Rust linear algebra. A reference for implementing dense matrix decompositions.

What sets thole apart: pure Rust and own implementations as founding principles, understanding ahead of speed, everything callable from Python, and mathematical properties proved in Lean.

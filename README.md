# thole

Pure Rust, no C/Fortran: scientific computing with every algorithm implemented from scratch.

A family of scientific computing crates written in pure Rust. It does not rely on external computation engines such as BLAS or LAPACK: every numerical algorithm is implemented from scratch. Everything is callable from Python, and the mathematical properties of the algorithms are proved in Lean 4.

**Status: concept stage.** Nothing is usable yet. The principles and the roadmap are in [CONCEPT.md](CONCEPT.md).

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
| `lean` | Lean 4 proofs |

## Development

The development environment is provided by [Canonical Workshop](https://ubuntu.com/workshop/docs/). Rust, Python (uv) and Lean (elan) exist only inside the workshop; nothing needs to be installed on the host.

```sh
workshop launch          # first time only: build and start the environment
workshop start           # resume it if it is stopped
workshop run -- setup    # fetch dependencies, create the Python environment, fetch Lean

workshop run -- test     # cargo test (arguments are passed through)
workshop run -- lint     # rustfmt check, clippy, rustdoc, pure Rust check
workshop run -- fmt      # cargo fmt
workshop run -- py       # rebuild the Python bindings and run pytest
workshop run -- lean     # lake build and the sorry check
workshop run -- check    # everything CI runs

workshop exec -- cargo <args>   # one-off command
workshop shell                  # open a shell inside
workshop refresh                # after changing base / sdks / hooks under .workshop/
```

## License

Licensed under either of [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE), at your option.

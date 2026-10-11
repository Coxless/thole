# thole proofs

Lean 4 proofs of the mathematical properties that the thole algorithms rely on. What they guarantee, and what they do not, is stated in section 3.5 of [CONCEPT.md](../CONCEPT.md).

```sh
workshop run -- lean
```

- Each area gets a file `Thole/<Area>.lean`, imported from `Thole.lean` (`Thole/Roots.lean` for `thole-roots`).
- The doc comment of a theorem names the corresponding Rust function.
- Mathlib is not a dependency yet. Add it to `lakefile.toml` when the first proof is written.

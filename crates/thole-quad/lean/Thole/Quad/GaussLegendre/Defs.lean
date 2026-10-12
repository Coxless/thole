/-
Gauss-Legendre quadrature: the executable specification.

Rust counterpart: `thole_quad::GaussLegendre` in
`../../../../src/gauss_legendre.rs`.

| Lean             | Rust                                                  |
|------------------|-------------------------------------------------------|
| `legendreStep`   | one step of the recurrence in `legendre`              |
| `legendrePair`   | `(p0, p1)` at the end of `legendre`                   |
| `legendre`       | `P_n(x)`, the first value that `legendre` returns     |
| `legendreDeriv`  | `P_n'(x)`, the second value that `legendre` returns   |
| `gaussWeight`    | `weight`                                              |
| `gaussNodeStep`  | one Newton step for a node in `GaussLegendre::new`    |
| `ruleSum`        | the sum in `GaussLegendre::integrate`                 |
| `rule`           | `GaussLegendre::integrate`                            |

`legendrePair x n` is `(P_{n-1}(x), P_n(x))`, with `P_{-1} = 0`, so that the
recurrence starts at `n = 0`. The Rust code starts at `n = 1`, from
`(P_0, P_1) = (1, x)`, which is the same.

The initial guesses of the nodes, and the number of Newton steps, are not
part of these definitions: they decide how fast the nodes are found, not what
they are. The oracle checks the nodes against `legendre`
(`oracle/lean/Thole/Oracle/Quad.lean`), and runs the exact sequence of
operations of the Rust code, initial guesses included, in a model of `f64`
arithmetic (`oracle/lean/Thole/Oracle/GaussLegendre.lean`).

The definitions are written over any linearly ordered field:
`../GaussLegendre.lean` proves their properties over `ℝ`.
-/
import Thole.Roots.Newton.Defs

namespace Thole.Quad

variable {α : Type*} [Field α] [LinearOrder α]

/-- One step of the three-term recurrence of the Legendre polynomials: from
`(P_{k-1}(x), P_k(x))` to `(P_k(x), P_{k+1}(x))`, by
`(k + 1) P_{k+1} = (2k + 1) x P_k - k P_{k-1}`. -/
def legendreStep (x : α) (k : ℕ) (p : α × α) : α × α :=
  (p.2, ((2 * (k : α) + 1) * x * p.2 - (k : α) * p.1) / ((k : α) + 1))

/-- `(P_{n-1}(x), P_n(x))`, with `P_{-1} = 0` and `P_0 = 1`. -/
def legendrePair (x : α) : ℕ → α × α
  | 0 => (0, 1)
  | n + 1 => legendreStep x n (legendrePair x n)

/-- The Legendre polynomial `P_n` at `x`. -/
def legendre (n : ℕ) (x : α) : α :=
  (legendrePair x n).2

/-- The derivative of `P_n` at `x`, for `x ≠ ±1`, by
`P_n' = n (x P_n - P_{n-1}) / (x^2 - 1)`. -/
def legendreDeriv (n : ℕ) (x : α) : α :=
  (n : α) * (x * (legendrePair x n).2 - (legendrePair x n).1) / (x * x - 1)

/-- The Gauss-Legendre weight of a node `x`: `2 / ((1 - x^2) P_n'(x)^2)`. -/
def gaussWeight (n : ℕ) (x : α) : α :=
  2 / ((1 - x * x) * legendreDeriv n x * legendreDeriv n x)

/-- One Newton step towards a root of `P_n`, as `GaussLegendre::new` takes
it. -/
def gaussNodeStep (n : ℕ) (x : α) : α :=
  Thole.Roots.newtonStep (legendre n) (legendreDeriv n) x

/-- `Σ w_i f(x_i)` over the nodes `xs` and the weights `ws`, summed in order
from the first node. -/
def ruleSum (xs ws : List α) (f : α → α) : α :=
  (xs.zip ws).foldl (fun acc p => acc + p.2 * f p.1) 0

/-- The rule with nodes `xs` and weights `ws` on `[-1, 1]`, applied to `f` on
`[a, b]` through the affine map `x ↦ c + h x`, with `c = a / 2 + b / 2` the
midpoint and `h = b / 2 - a / 2` the half-length. -/
def rule (xs ws : List α) (f : α → α) (a b : α) : α :=
  (b / 2 - a / 2) * ruleSum xs ws (fun x => f (a / 2 + b / 2 + (b / 2 - a / 2) * x))

end Thole.Quad

"""Generates the reference values used by the Rust and Python tests.

The roots are computed with mpmath at 50 significant digits and rounded to the
nearest f64. Run from the repository root:

    workshop exec -- uv run --no-project --with mpmath==1.3.0 --with scipy==1.18.1 \
        python crates/thole-roots/python/reference_values.py

and copy the output into `tests/bisection.rs`, `tests/brent.rs` and
`python/test_bisect.py`.

For Brent's method, the result and the number of function evaluations of
`scipy.optimize.brentq` are printed too. The functions of that part use only
`+`, `-` and `*`, so that they have the same values in Python and in Rust.
"""

from mpmath import cos, exp, findroot, mp
from scipy.optimize import brentq

mp.dps = 50

PROBLEMS = [
    ("x^3 - x - 2 on [1, 2]", lambda x: x**3 - x - 2, (1, 2)),
    ("cos(x) - x on [0, 1]", lambda x: cos(x) - x, (0, 1)),
    ("x * exp(x) - 1 on [0, 1]", lambda x: x * exp(x) - 1, (0, 1)),
]

for name, f, bracket in PROBLEMS:
    root = findroot(f, bracket, solver="anderson", tol=mp.mpf(10) ** -45)
    assert bracket[0] < root < bracket[1]
    assert abs(f(root)) < mp.mpf(10) ** -40
    print(f"{name}: {float(root)!r}")

BRENT_PROBLEMS = [
    ("x^3 - x - 2 on [1, 2]", lambda x: x * x * x - x - 2.0, (1.0, 2.0)),
    ("x^2 - 2 on [0, 2]", lambda x: x * x - 2.0, (0.0, 2.0)),
    (
        "-1 for x < 0.7, 1e-3 from there on, on [0, 1]",
        lambda x: -1.0 if x < 0.7 else 1e-3,
        (0.0, 1.0),
    ),
]

for name, f, bracket in BRENT_PROBLEMS:
    x, result = brentq(f, *bracket, full_output=True)
    print(f"brentq, {name}: {x!r}, {result.function_calls} evaluations")

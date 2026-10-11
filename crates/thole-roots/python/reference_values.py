"""Generates the reference roots used by the Rust and Python tests.

The roots are computed with mpmath at 50 significant digits and rounded to the
nearest f64. Run from the repository root:

    workshop exec -- uv run --no-project --with mpmath==1.3.0 \
        python crates/thole-roots/python/reference_values.py

and copy the output into `tests/bisection.rs` and `python/test_bisect.py`.
"""

from mpmath import cos, exp, findroot, mp

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

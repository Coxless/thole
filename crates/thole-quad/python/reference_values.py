"""Generates the reference values used by the Rust and Python tests.

The integrals are computed with mpmath at 50 significant digits and rounded to
the nearest f64. Run from the repository root:

    workshop exec -- uv run --no-project --with mpmath==1.3.0 --with scipy==1.18.1 \
        python crates/thole-quad/python/reference_values.py

and copy the output into `tests/gauss_legendre.rs`, `tests/gauss_kronrod.rs`,
`python/test_gauss_legendre.py` and `python/test_gauss_kronrod.py`.

For the Gauss-Legendre rule, the nodes and weights of
`scipy.special.roots_legendre` are compared with those of mpmath too, to show
how close an independent implementation gets.
"""

from mpmath import atan, cos, exp, log, mp, mpf, pi, quad, sin, sqrt
from scipy.special import roots_legendre

mp.dps = 50

PROBLEMS = [
    ("exp(x) on [0, 1]", exp, (0, 1)),
    ("sin(x) on [0, pi]", sin, (0, pi)),
    ("1 / (1 + x^2) on [0, 1]", lambda x: 1 / (1 + x * x), (0, 1)),
    ("sqrt(x) on [0, 1]", sqrt, (0, 1)),
    ("-log(x) on [0, 1]", lambda x: -log(x), (0, 1)),
    ("|x - 1/3| on [-1, 1]", lambda x: abs(x - mpf(1) / 3), (-1, mpf(1) / 3, 1)),
    ("1 / (1e-4 + (x - 0.3)^2) on [0, 1]", lambda x: 1 / (mpf("1e-4") + (x - mpf("0.3")) ** 2), (0, mpf("0.3"), 1)),
    ("cos(30 x) on [0, 1]", lambda x: cos(30 * x), (0, 1)),
    ("exp(-x^2) on [-5, 5]", lambda x: exp(-x * x), (-5, 5)),
]

for name, f, points in PROBLEMS:
    value = quad(f, points)
    print(f"{name}: {float(value)!r}")

# Closed forms of some of the above, as a check of mpmath.
assert abs(quad(lambda x: 1 / (mpf("1e-4") + (x - mpf("0.3")) ** 2), (0, mpf("0.3"), 1))
           - 100 * (atan(70) + atan(30))) < mpf(10) ** -40

# The nodes and weights of the Gauss-Legendre rule with 20 points: the roots of
# P_20 and 2 / ((1 - x^2) P_20'(x)^2), the positive half, largest first.
n = 20
nodes = sorted(mp.polyroots(mp.taylor(lambda t: mp.legendre(n, t), 0, n)[::-1],
                            maxsteps=500, extraprec=500), reverse=True)[: n // 2]
weights = [2 / ((1 - x * x) * mp.diff(lambda t: mp.legendre(n, t), x) ** 2) for x in nodes]
print(f"Gauss-Legendre {n} nodes: {[float(x) for x in nodes]}")
print(f"Gauss-Legendre {n} weights: {[float(w) for w in weights]}")

# How close SciPy gets, in units of the spacing of f64 values near 1.
x, w = roots_legendre(n)
node_error = max(abs(mpf(float(a)) - b) for a, b in zip(sorted(x, reverse=True), nodes))
print(f"roots_legendre({n}): largest node error {float(node_error / mpf(2) ** -53):.2f} units of 2^-53")

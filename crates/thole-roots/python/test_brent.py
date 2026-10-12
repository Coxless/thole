"""Tests of `thole.roots.brent`. They mirror `tests/brent.rs`."""

import math
import sys

import pytest

from thole.roots import ConvergenceError, Root, bisect, brent

XTOL = 2e-12
RTOL = 4 * sys.float_info.epsilon


def within_default_tolerance(x, expected):
    return abs(x - expected) <= XTOL + RTOL * abs(x)


# Roots computed with mpmath at 50 digits by `reference_values.py`.
@pytest.mark.parametrize(
    ("f", "a", "b", "expected"),
    [
        (lambda x: x**3 - x - 2, 1.0, 2.0, 1.5213797068045676),
        (lambda x: math.cos(x) - x, 0.0, 1.0, 0.7390851332151607),
        (lambda x: x * math.exp(x) - 1, 0.0, 1.0, 0.5671432904097838),
    ],
)
def test_matches_mpmath_reference_roots(f, a, b, expected):
    assert within_default_tolerance(brent(f, a, b).x, expected)


# Results of `scipy.optimize.brentq` printed by `reference_values.py`: the
# root and the number of function evaluations.
@pytest.mark.parametrize(
    ("f", "a", "b", "x", "evaluations"),
    [
        (lambda x: x * x * x - x - 2.0, 1.0, 2.0, 1.5213797068045676, 9),
        (lambda x: x * x - 2.0, 0.0, 2.0, 1.4142135623731364, 9),
        (lambda x: -1.0 if x < 0.7 else 1e-3, 0.0, 1.0, 0.7000000000005636, 62),
    ],
)
def test_matches_scipy_brentq(f, a, b, x, evaluations):
    calls = []

    def counted(t):
        calls.append(t)
        return f(t)

    root = brent(counted, a, b)
    assert root.x == x
    assert len(calls) == evaluations == root.iterations + 2


def test_matches_analytic_roots():
    assert within_default_tolerance(brent(lambda x: x * x - 2, 0, 2).x, math.sqrt(2))
    assert within_default_tolerance(brent(math.cos, 0, 2).x, math.pi / 2)


def test_takes_fewer_steps_than_bisection():
    def f(x):
        return x**3 - x - 2

    assert 3 * brent(f, 1.0, 2.0).iterations <= bisect(f, 1.0, 2.0).iterations


def test_result_fields():
    # The secant through the ends of the bracket is the function itself, so
    # the first step lands on the root.
    root = brent(lambda x: 2 * x - 1, 0.0, 4.0)
    assert isinstance(root, Root)
    assert (root.x, root.lo, root.hi, root.iterations) == (0.5, 0.5, 4.0, 1)
    assert repr(root) == "Root(x=0.5, lo=0.5, hi=4.0, iterations=1)"

    f = lambda x: x * x - 2  # noqa: E731
    root = brent(f, 0.0, 2.0, xtol=1e-3, rtol=0.0)
    assert 0.0 <= root.lo <= math.sqrt(2) <= root.hi <= 2.0
    assert root.x in (root.lo, root.hi)
    assert abs(root.x - math.sqrt(2)) <= 1e-3
    assert f(root.lo) <= 0 <= f(root.hi)


def test_root_at_an_endpoint_takes_no_step():
    root = brent(lambda x: x - 1, 1.0, 3.0)
    assert (root.x, root.iterations) == (1.0, 0)
    assert repr(root) == "Root(x=1.0, lo=1.0, hi=3.0, iterations=0)"


def test_result_is_read_only():
    root = brent(lambda x: x, -1.0, 1.0)
    with pytest.raises(AttributeError):
        root.x = 1.0


def test_options_are_keyword_only():
    with pytest.raises(TypeError):
        brent(lambda x: x, -1.0, 1.0, 1e-3)


@pytest.mark.parametrize(
    ("a", "b"),
    [(1.0, -1.0), (math.nan, 1.0), (-math.inf, 1.0), (-1.0, math.inf)],
)
def test_invalid_bracket(a, b):
    with pytest.raises(ValueError, match="invalid bracket"):
        brent(lambda x: x, a, b)


def test_invalid_tolerance():
    with pytest.raises(ValueError, match="invalid tolerance"):
        brent(lambda x: x, -1.0, 1.0, xtol=-1e-9)
    with pytest.raises(ValueError, match="invalid tolerance"):
        brent(lambda x: x, -1.0, 1.0, rtol=math.nan)


def test_no_sign_change():
    with pytest.raises(ValueError, match="no sign change"):
        brent(lambda x: x * x + 1, -1.0, 2.0)


def test_nan_function_value():
    with pytest.raises(ValueError, match="returned NaN at x = 0"):
        brent(lambda x: math.nan, 0.0, 1.0)
    with pytest.raises(ValueError, match="returned NaN at x = "):
        brent(lambda x: math.nan if 0.0 < x < 1.0 else x - 0.3, 0.0, 1.0)


def test_iteration_limit():
    with pytest.raises(ConvergenceError, match="after 3 iterations"):
        brent(lambda x: x * x - 2, 0.0, 2.0, max_iter=3)


def test_exception_in_callback_propagates():
    def f(x):
        if 0.0 < x < 1.0:
            raise KeyError("boom")
        return x - 0.3

    with pytest.raises(KeyError, match="boom"):
        brent(f, 0.0, 1.0)


def test_non_numeric_return_value():
    with pytest.raises(TypeError):
        brent(lambda x: "not a number", 0.0, 1.0)


def test_accepts_ints_and_callable_objects():
    class Shifted:
        def __call__(self, x):
            return x - 1

    assert within_default_tolerance(brent(Shifted(), 0, 3).x, 1.0)

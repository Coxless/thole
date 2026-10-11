"""Tests of `thole.roots.bisect`. They mirror `tests/bisection.rs`."""

import math
import sys

import pytest

from thole.roots import ConvergenceError, Root, bisect

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
    assert within_default_tolerance(bisect(f, a, b).x, expected)


def test_matches_analytic_roots():
    assert within_default_tolerance(bisect(lambda x: x * x - 2, 0, 2).x, math.sqrt(2))
    assert within_default_tolerance(bisect(math.cos, 0, 2).x, math.pi / 2)


def test_result_fields():
    root = bisect(lambda x: x - 0.3, 0.0, 1.0, xtol=1e-3, rtol=0.0)
    assert isinstance(root, Root)
    # 1 / 2^10 <= 1e-3 < 1 / 2^9
    assert root.iterations == 9
    assert root.hi - root.lo == 1 / 2**9
    assert root.lo <= 0.3 <= root.hi
    assert root.x == (root.lo + root.hi) / 2
    assert repr(root) == "Root(x=0.2998046875, lo=0.298828125, hi=0.30078125, iterations=9)"
    assert repr(bisect(lambda x: x, -1.0, 1.0, xtol=1.0)) == "Root(x=0.0, lo=-1.0, hi=1.0, iterations=0)"


def test_result_is_read_only():
    root = bisect(lambda x: x, -1.0, 1.0)
    with pytest.raises(AttributeError):
        root.x = 1.0


def test_options_are_keyword_only():
    with pytest.raises(TypeError):
        bisect(lambda x: x, -1.0, 1.0, 1e-3)


@pytest.mark.parametrize(
    ("a", "b"),
    [(1.0, -1.0), (math.nan, 1.0), (-math.inf, 1.0), (-1.0, math.inf)],
)
def test_invalid_bracket(a, b):
    with pytest.raises(ValueError, match="invalid bracket"):
        bisect(lambda x: x, a, b)


def test_invalid_tolerance():
    with pytest.raises(ValueError, match="invalid tolerance"):
        bisect(lambda x: x, -1.0, 1.0, xtol=-1e-9)
    with pytest.raises(ValueError, match="invalid tolerance"):
        bisect(lambda x: x, -1.0, 1.0, rtol=math.nan)


def test_no_sign_change():
    with pytest.raises(ValueError, match="no sign change"):
        bisect(lambda x: x * x + 1, -1.0, 2.0)


def test_nan_function_value():
    with pytest.raises(ValueError, match="returned NaN at x = 0.5"):
        bisect(lambda x: math.nan if x == 0.5 else x - 0.3, 0.0, 1.0)


def test_iteration_limit():
    with pytest.raises(ConvergenceError, match="after 5 iterations"):
        bisect(lambda x: x - 0.3, 0.0, 1.0, max_iter=5)
    assert issubclass(ConvergenceError, RuntimeError)


def test_exception_in_callback_propagates():
    def f(x):
        if x == 0.5:
            raise KeyError("boom")
        return x - 0.3

    with pytest.raises(KeyError, match="boom"):
        bisect(f, 0.0, 1.0)


def test_non_numeric_return_value():
    with pytest.raises(TypeError):
        bisect(lambda x: "not a number", 0.0, 1.0)


def test_accepts_ints_and_callable_objects():
    class Shifted:
        def __call__(self, x):
            return x - 1

    assert within_default_tolerance(bisect(Shifted(), 0, 3).x, 1.0)

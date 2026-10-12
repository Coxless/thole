"""Tests of `thole.roots.newton`. They mirror `tests/newton.rs`."""

import math
import sys

import pytest

from thole.roots import ConvergenceError, NewtonRoot, newton

XTOL = 2e-12
RTOL = 4 * sys.float_info.epsilon


def within_default_tolerance(x, expected):
    return abs(x - expected) <= XTOL + RTOL * abs(x)


# Roots computed with mpmath at 50 digits by `reference_values.py`.
@pytest.mark.parametrize(
    ("f", "fprime", "x0", "expected"),
    [
        (lambda x: x**3 - x - 2, lambda x: 3 * x**2 - 1, 1.5, 1.5213797068045676),
        (lambda x: math.cos(x) - x, lambda x: -math.sin(x) - 1, 0.5, 0.7390851332151607),
        (lambda x: x * math.exp(x) - 1, lambda x: (x + 1) * math.exp(x), 0.5, 0.5671432904097838),
    ],
)
def test_matches_mpmath_reference_roots(f, fprime, x0, expected):
    assert within_default_tolerance(newton(f, fprime, x0).x, expected)


# Results of `scipy.optimize.newton` with `tol=1.48e-8` printed by
# `reference_values.py`: the root and the number of steps.
@pytest.mark.parametrize(
    ("f", "fprime", "x0", "x", "iterations"),
    [
        (lambda x: x * x * x - x - 2.0, lambda x: 3.0 * x * x - 1.0, 1.5, 1.5213797068045676, 4),
        (lambda x: x * x - 2.0, lambda x: 2.0 * x, 1.0, 1.4142135623730951, 5),
        (lambda x: x * x - 2.0, lambda x: 2.0 * x, 1000.0, 1.4142135623730951, 14),
    ],
)
def test_matches_scipy_newton(f, fprime, x0, x, iterations):
    root = newton(f, fprime, x0, xtol=1.48e-8, rtol=0.0)
    assert (root.x, root.iterations) == (x, iterations)


def test_matches_analytic_roots():
    assert within_default_tolerance(newton(lambda x: x * x - 2, lambda x: 2 * x, 1).x, math.sqrt(2))
    assert within_default_tolerance(newton(math.cos, lambda x: -math.sin(x), 1.0).x, math.pi / 2)


def test_result_fields():
    root = newton(lambda x: 2 * x - 1, lambda x: 2.0, 4.0)
    assert isinstance(root, NewtonRoot)
    assert (root.x, root.step, root.iterations) == (0.5, 3.5, 1)
    assert repr(root) == "NewtonRoot(x=0.5, step=3.5, iterations=1)"
    root = newton(lambda x: x - 1, lambda x: 1.0, 1.0)
    assert repr(root) == "NewtonRoot(x=1.0, step=0.0, iterations=0)"


def test_error_is_within_the_last_step():
    for t in [0.5, 0.1, 1e-2, 1e-3, 1e-6]:
        root = newton(lambda x: x * x - 2, lambda x: 2 * x, 2.0, xtol=t, rtol=0.0)
        assert abs(root.step) <= t
        assert abs(root.x - math.sqrt(2)) <= abs(root.step)


def test_result_is_read_only():
    root = newton(lambda x: x, lambda x: 1.0, 1.0)
    with pytest.raises(AttributeError):
        root.x = 1.0


def test_options_are_keyword_only():
    with pytest.raises(TypeError):
        newton(lambda x: x, lambda x: 1.0, 1.0, 1e-3)


@pytest.mark.parametrize("x0", [math.nan, math.inf, -math.inf])
def test_invalid_starting_point(x0):
    with pytest.raises(ValueError, match="invalid starting point"):
        newton(lambda x: x, lambda x: 1.0, x0)


def test_invalid_tolerance():
    with pytest.raises(ValueError, match="invalid tolerance"):
        newton(lambda x: x, lambda x: 1.0, 1.0, xtol=-1e-9)


def test_nan_values():
    with pytest.raises(ValueError, match="function returned NaN at x = 0.5"):
        newton(lambda x: math.nan, lambda x: 1.0, 0.5)
    with pytest.raises(ValueError, match="derivative returned NaN at x = 0.5"):
        newton(lambda x: x - 1, lambda x: math.nan, 0.5)


def test_zero_derivative():
    with pytest.raises(ConvergenceError, match="derivative is zero at x = 0"):
        newton(lambda x: x * x - 2, lambda x: 2 * x, 0.0)


def test_non_finite_step():
    with pytest.raises(ConvergenceError, match="not finite"):
        newton(lambda x: 1.0, lambda x: 1e-310, 0.0)


def test_iteration_limit():
    # The classic cycle between 0 and 1.
    with pytest.raises(ConvergenceError, match="after 100 iterations"):
        newton(lambda x: x**3 - 2 * x + 2, lambda x: 3 * x**2 - 2, 0.0)
    assert issubclass(ConvergenceError, RuntimeError)


@pytest.mark.parametrize("which", ["f", "fprime"])
def test_exception_in_callback_propagates(which):
    def boom(x):
        raise KeyError("boom")

    f = boom if which == "f" else (lambda x: x - 1)
    fprime = boom if which == "fprime" else (lambda x: 1.0)
    with pytest.raises(KeyError, match="boom"):
        newton(f, fprime, 3.0)


def test_non_numeric_return_value():
    with pytest.raises(TypeError):
        newton(lambda x: "not a number", lambda x: 1.0, 1.0)


def test_accepts_ints_and_callable_objects():
    class Shifted:
        def __call__(self, x):
            return x - 1

    assert within_default_tolerance(newton(Shifted(), lambda x: 1, 3).x, 1.0)

"""Tests of `thole.quad.gauss_kronrod`. They mirror `tests/gauss_kronrod.rs`."""

import math

import pytest

from thole.quad import ConvergenceError, Integral, gauss_kronrod, gauss_kronrod_rule

ATOL = RTOL = 1.49e-8

# Integrals computed with mpmath at 50 digits by `reference_values.py`.
PROBLEMS = [
    (math.exp, 0.0, 1.0, 1.7182818284590453),
    (math.sin, 0.0, math.pi, 2.0),
    (lambda x: 1 / (1 + x * x), 0.0, 1.0, 0.7853981633974483),
    (math.sqrt, 0.0, 1.0, 0.6666666666666666),
    (lambda x: -math.log(x), 0.0, 1.0, 1.0),
    (lambda x: abs(x - 1 / 3), -1.0, 1.0, 1.1111111111111112),
    (lambda x: 1 / (1e-4 + (x - 0.3) ** 2), 0.0, 1.0, 309.3986915124149),
    (lambda x: math.cos(30 * x), 0.0, 1.0, -0.03293438746976206),
    (lambda x: math.exp(-x * x), -5.0, 5.0, 1.772453850902791),
]


@pytest.mark.parametrize(("f", "a", "b", "expected"), PROBLEMS)
def test_matches_mpmath_reference_integrals(f, a, b, expected):
    integral = gauss_kronrod(f, a, b)
    assert abs(integral.value - expected) <= ATOL + RTOL * abs(expected)
    assert integral.error <= ATOL + RTOL * abs(integral.value)


@pytest.mark.parametrize(("f", "a", "b", "expected"), PROBLEMS)
def test_reaches_full_precision(f, a, b, expected):
    integral = gauss_kronrod(f, a, b, atol=1e-14, rtol=1e-14, max_subintervals=1000)
    assert abs(integral.value - expected) <= 1e-13 * max(abs(expected), 1)


def test_result_fields():
    integral = gauss_kronrod(math.exp, 0.0, 1.0)
    assert isinstance(integral, Integral)
    assert (integral.subintervals, integral.evaluations) == (1, 15)
    empty = gauss_kronrod(math.exp, 2.0, 2.0)
    assert repr(empty) == "Integral(value=0.0, error=0.0, subintervals=1, evaluations=15)"


def test_counts_function_evaluations():
    calls = []

    def f(x):
        calls.append(x)
        return math.sqrt(x)

    integral = gauss_kronrod(f, 0.0, 1.0)
    assert integral.subintervals > 1
    assert len(calls) == integral.evaluations == 15 * (2 * integral.subintervals - 1)


def test_result_is_read_only():
    integral = gauss_kronrod(math.exp, 0.0, 1.0)
    with pytest.raises(AttributeError):
        integral.value = 1.0


def test_options_are_keyword_only():
    with pytest.raises(TypeError):
        gauss_kronrod(math.exp, 0.0, 1.0, 1e-3)


def test_invalid_arguments():
    with pytest.raises(ValueError, match="invalid interval"):
        gauss_kronrod(math.exp, 0.0, math.inf)
    with pytest.raises(ValueError, match="invalid tolerance"):
        gauss_kronrod(math.exp, 0.0, 1.0, atol=-1.0)
    with pytest.raises(ValueError, match="invalid limit"):
        gauss_kronrod(math.exp, 0.0, 1.0, max_subintervals=0)


def test_non_finite_values():
    with pytest.raises(ValueError, match="returned inf at x = 0"):
        gauss_kronrod(lambda x: 1 / x if x else math.inf, -1.0, 1.0)


def test_subinterval_limit():
    with pytest.raises(ConvergenceError, match="with 3 subintervals"):
        gauss_kronrod(math.sqrt, 0.0, 1.0, atol=1e-14, rtol=0.0, max_subintervals=3)
    assert issubclass(ConvergenceError, RuntimeError)


def test_exception_in_callback_propagates():
    def f(x):
        if x > 0.5:
            raise KeyError("boom")
        return x

    with pytest.raises(KeyError, match="boom"):
        gauss_kronrod(f, 0.0, 1.0)


def test_non_numeric_return_value():
    with pytest.raises(TypeError):
        gauss_kronrod(lambda x: "not a number", 0.0, 1.0)


def test_the_rules_are_exact_for_their_degrees():
    nodes, kronrod, gauss = gauss_kronrod_rule()
    assert len(nodes) == len(kronrod) == len(gauss) == 15
    assert nodes == sorted(nodes)
    for k in range(23):
        exact = 2 / (k + 1) if k % 2 == 0 else 0.0
        assert abs(sum(w * x**k for x, w in zip(nodes, kronrod)) - exact) <= 1e-15
        if k <= 13:
            assert abs(sum(w * x**k for x, w in zip(nodes, gauss)) - exact) <= 1e-15

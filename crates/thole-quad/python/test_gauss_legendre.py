"""Tests of `thole.quad.GaussLegendre` and `thole.quad.gauss_legendre`. They mirror `tests/gauss_legendre.rs`."""

import math

import pytest

from thole.quad import GaussLegendre, gauss_legendre


def units(x, y):
    """`|x - y|` in units of 2^-53, the spacing of floats just below 1."""
    return abs(x - y) / 2**-53


# The positive half of the 20-point rule from the largest node, computed with
# mpmath at 50 digits by `reference_values.py`.
NODES_20 = [
    0.9931285991850949, 0.9639719272779138, 0.912234428251326, 0.8391169718222188,
    0.7463319064601508, 0.636053680726515, 0.5108670019508271, 0.37370608871541955,
    0.22778585114164507, 0.07652652113349734,
]
WEIGHTS_20 = [
    0.017614007139152118, 0.04060142980038694, 0.06267204833410907, 0.08327674157670475,
    0.10193011981724044, 0.11819453196151841, 0.13168863844917664, 0.14209610931838204,
    0.14917298647260374, 0.15275338713072584,
]


def test_matches_mpmath_nodes_and_weights():
    rule = GaussLegendre(20)
    for i in range(10):
        assert units(rule.nodes[19 - i], NODES_20[i]) <= 1
        assert units(rule.weights[19 - i], WEIGHTS_20[i]) <= 4


def test_matches_closed_forms():
    rule = GaussLegendre(3)
    assert rule.order == 3
    for x, expected in zip(rule.nodes, [-math.sqrt(0.6), 0.0, math.sqrt(0.6)]):
        assert units(x, expected) <= 2
    for w, expected in zip(rule.weights, [5 / 9, 8 / 9, 5 / 9]):
        assert units(w, expected) <= 4


# Integrals computed with mpmath at 50 digits by `reference_values.py`.
@pytest.mark.parametrize(
    ("f", "a", "b", "expected"),
    [
        (math.exp, 0.0, 1.0, 1.7182818284590453),
        (math.sin, 0.0, math.pi, 2.0),
        (lambda x: 1 / (1 + x * x), 0.0, 1.0, 0.7853981633974483),
        (lambda x: math.cos(30 * x), 0.0, 1.0, -0.03293438746976206),
        (lambda x: math.exp(-x * x), -5.0, 5.0, 1.772453850902791),
    ],
)
def test_matches_mpmath_reference_integrals(f, a, b, expected):
    assert abs(gauss_legendre(f, a, b, 40) - expected) <= 1e-14 * max(abs(expected), 1)


@pytest.mark.parametrize("n", [1, 2, 5, 9])
def test_exact_for_polynomials_of_degree_2n_minus_1(n):
    rule = GaussLegendre(n)
    for degree in range(2 * n):
        exact = (2.0 ** (degree + 1) - (-3.0) ** (degree + 1)) / (degree + 1)
        value = rule.integrate(lambda x: x**degree, -3.0, 2.0)
        assert abs(value - exact) <= 1e-14 * 3.0**degree * 5


def test_symmetric_and_sorted():
    rule = GaussLegendre(101)
    x, w = rule.nodes, rule.weights
    assert x == sorted(x)
    assert x == [-t for t in reversed(x)]
    assert w == list(reversed(w))
    assert abs(sum(w) - 2) <= 1e-14


def test_rule_is_read_only():
    rule = GaussLegendre(3)
    with pytest.raises(AttributeError):
        rule.nodes = [0.0]
    assert repr(rule) == "GaussLegendre(3)"


def test_reversed_interval():
    assert gauss_legendre(math.exp, 1.0, 0.0, 5) == -gauss_legendre(math.exp, 0.0, 1.0, 5)


def test_zero_points():
    with pytest.raises(ValueError, match="invalid number of points 0"):
        GaussLegendre(0)
    with pytest.raises(ValueError, match="invalid number of points 0"):
        gauss_legendre(math.exp, 0.0, 1.0, 0)


@pytest.mark.parametrize(("a", "b"), [(math.nan, 1.0), (0.0, math.inf)])
def test_invalid_interval(a, b):
    with pytest.raises(ValueError, match="invalid interval"):
        gauss_legendre(math.exp, a, b, 3)


def test_non_finite_values():
    with pytest.raises(ValueError, match="returned inf at x = 0"):
        gauss_legendre(lambda x: math.inf if x == 0 else x, -1.0, 1.0, 3)
    with pytest.raises(ValueError, match="returned NaN"):
        gauss_legendre(lambda x: math.nan, -1.0, 1.0, 3)


def test_exception_in_callback_propagates():
    def f(x):
        raise KeyError("boom")

    with pytest.raises(KeyError, match="boom"):
        GaussLegendre(4).integrate(f, 0.0, 1.0)


def test_accepts_ints_and_callable_objects():
    class Square:
        def __call__(self, x):
            return x * x

    assert abs(gauss_legendre(Square(), 0, 3, 2) - 9) <= 1e-14

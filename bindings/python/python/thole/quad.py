"""Numerical integration: approximating the integral of a function of one variable over a finite interval."""

from ._thole import quad as _quad

ConvergenceError = _quad.ConvergenceError
GaussLegendre = _quad.GaussLegendre
Integral = _quad.Integral
gauss_kronrod = _quad.gauss_kronrod
gauss_legendre = _quad.gauss_legendre

__all__ = ["ConvergenceError", "GaussLegendre", "Integral", "gauss_kronrod", "gauss_legendre"]

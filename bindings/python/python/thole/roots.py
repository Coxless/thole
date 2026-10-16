"""Root finding: solving ``f(x) = 0`` for a function of one variable."""

from ._thole import roots as _roots

ConvergenceError = _roots.ConvergenceError
NewtonRoot = _roots.NewtonRoot
Root = _roots.Root
bisect = _roots.bisect
brent = _roots.brent
newton = _roots.newton

__all__ = ["ConvergenceError", "NewtonRoot", "Root", "bisect", "brent", "newton"]

"""Root finding: solving ``f(x) = 0`` for a function of one variable."""

from ._thole import roots as _roots

ConvergenceError = _roots.ConvergenceError
Root = _roots.Root
bisect = _roots.bisect

__all__ = ["ConvergenceError", "Root", "bisect"]

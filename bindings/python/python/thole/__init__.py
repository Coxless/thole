"""Pure Rust, no C/Fortran: scientific computing with every algorithm implemented from scratch."""

from . import quad, roots
from ._thole import __version__

__all__ = ["__version__", "quad", "roots"]

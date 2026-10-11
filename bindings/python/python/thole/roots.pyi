from collections.abc import Callable
from typing import final

class ConvergenceError(RuntimeError): ...

@final
class Root:
    @property
    def x(self) -> float: ...
    @property
    def lo(self) -> float: ...
    @property
    def hi(self) -> float: ...
    @property
    def iterations(self) -> int: ...

def bisect(
    f: Callable[[float], float],
    a: float,
    b: float,
    *,
    xtol: float | None = None,
    rtol: float | None = None,
    max_iter: int | None = None,
) -> Root: ...

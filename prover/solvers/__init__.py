from .solvers import solve
from .extrema import solve_extrema

from .univariate import (
    solveset, wrap_relational,
    rational_eval, poly_roots, poly_extrema,
)

__all__ = [
    'solve', 'solve_extrema',
    'solveset', 'wrap_relational',
    'rational_eval', 'poly_roots', 'poly_extrema'
]
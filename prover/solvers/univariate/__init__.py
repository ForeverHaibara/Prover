from .solveset import solveset, wrap_relational

from .monotonicity import solve_extrema_univariate, solve_range_univariate

from .polynomial import rational_eval, poly_roots

__all__ = [
    'solveset', 'wrap_relational',
    'solve_extrema_univariate', 'solve_range_univariate',
    'rational_eval', 'poly_roots'
]
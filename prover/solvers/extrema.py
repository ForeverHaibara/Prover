import sympy as sp
from sympy.core import Equality, Expr, Tuple, sympify
from sympy.sets import Contains, Reals

from .solvers import _sympified_tuple, solve

from ..core import TractableSet
from ..core.tractable import mathref

def solve_extrema(f, symbols):
    """
    Solve the extrema of the given function by computing the derivative.
    """
    f = sympify(f)
    symbols = _sympified_tuple(symbols)
    if len(symbols) == 0:
        raise ValueError('No symbols are given.')
    if not isinstance(f, Expr):
        raise ValueError('The function must be a sympy expression.')

    df = []

    for symbol in symbols:
        df.append(Equality(sp.diff(f, symbol), 0))
    df.append(sp.And(*[Contains(symb, Reals, evaluate=False) for symb in symbols]))

    critic = solve(df, symbols, real=True)

    fvals = []
    fdoit = f.doit()
    for point in critic:
        fvals.append(Tuple(point, fdoit.subs(point.value).expand().radsimp()))

    if len(fvals):
        fkey = lambda x: x[1]
        fmin, fmax = min(fvals, key=fkey), max(fvals, key=fkey)

    description = '代回求得'
    description += '最小值 $%s$, 当 $%s$ 可取等.\n\n'%(
        mathref(fmin[1]), mathref(fmin[0].value)
    )
    description += '最大值 $%s$, 当 $%s$ 可取等.\n\n'%(
        mathref(fmax[1]), mathref(fmax[0].value)
    )
    description = description.rstrip('\n')

    extrema = TractableSet('f_minmax', Tuple(f), Tuple(fmin, fmax), description=description)

    return critic, extrema
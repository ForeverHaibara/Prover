import sympy as sp
from sympy.core import Dummy, Expr, Equality, Tuple, sympify
from sympy.logic.boolalg import Boolean

from ..core.traceable import TraceableSolveSet
from ..utilities import sympified_tuple

def _get_exprs_and_constraints(exprs):
    """
    Get the expressions and constraints from the given arguments.
    """
    exprs = sympified_tuple(exprs)
    expr_list = list(filter(lambda x: isinstance(x, Expr) or isinstance(x, Equality), exprs))
    # constrain_list = list(filter(lambda x: not isinstance(x, Expr), exprs))
    constrain_list = list(filter(lambda x: isinstance(x, Boolean) and not isinstance(x, Equality), exprs))
    if len(expr_list) + len(constrain_list) != len(exprs):
        raise ValueError('Not all arguments are expressions or booleans.')

    return expr_list, constrain_list


def solve(f, symbols, **flags) -> TraceableSolveSet:
    """
    Wrapper for sympy.solve, returning a TraceableSolveSet object.
    """
    flags['dict'] = flags.get('dict', True)
    as_eq = flags.pop('as_eq', True)
    real = flags.pop('real', False)

    (f, constraints), symbols = _get_exprs_and_constraints(f), sympified_tuple(symbols)
    if real:
        real_symbols = [Dummy(symb.name, real=True) for symb in symbols]
        f = [_.xreplace(dict(zip(symbols, real_symbols))) for _ in f]
        constraints = [_.xreplace(dict(zip(symbols, real_symbols))) for _ in constraints]
        symbols, real_symbols = real_symbols, symbols

    if len(f) == 0:
        f, constraints = constraints, f
    fsimp, constraintsimp = [f.doit() for f in f], [c.doit() for c in constraints]
    result = sp.solve(fsimp, symbols, **flags)
    if result is None:
        return None

    result = sympified_tuple(result)
    if len(constraints):
        filtered_result = []
        for res in result:
            if all(c.subs(res) is sp.true for c in constraintsimp):
                filtered_result.append(res)
        result = Tuple(*filtered_result)
                

    if real:
        f = [_.xreplace(dict(zip(symbols, real_symbols))) for _ in f]
        constraints = [_.xreplace(dict(zip(symbols, real_symbols))) for _ in constraints]
        result = result.xreplace(dict(zip(symbols, real_symbols)))
        symbols, real_symbols = real_symbols, symbols

    if len(symbols) == 1:
        name = symbols[0].name
    else:
        name = 'S'
    name = Dummy(name)


    if as_eq:
        f = list(f)
        for i in range(len(f)):
            if isinstance(f[i], Expr):
                f[i] = Equality(f[i], 0)

    f = sympify(Tuple(*f, *constraints))
    return TraceableSolveSet(name, f, result)
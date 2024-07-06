import sympy as sp

from sympy.logic import And, Or, Not, Xor, Nand, Nor
from sympy.core import S, Basic, sympify
from sympy.sets import Set, Intersection, Union, Complement
from sympy.utilities.iterables import iterable

from ...utilities import sympified_tuple

def solveset(f, symbols):
    """
    This is a wrapper of sympy.solveset that supports And, Or, Not, Nand, Nor also.
    """
    domain = S.Reals
    if isinstance(f, (And, Or, Not, Nand, Nor)):
        func = {
            And: Intersection,
            Or: Union,
            Not: lambda *x: Complement(domain, *x),
            Nand: lambda *x: Complement(domain, Intersection(*x)),
            Nor: lambda *x: Complement(domain, Union(*x))
        }
        u = [solveset(arg, symbols) for arg in f.args]
        return func[f.func](*u)
    return sp.solveset(f, symbols, domain)

def wrap_relational(rel, gen, return_type = 'set'):
    """
    Convert given relational objects to a specified type.
    """
    if (not isinstance(rel, Basic)):
        if callable(rel):
            if return_type == 'callable':
                return rel
            raise ValueError('Cannot convert type %s to %s.'%(type(rel), return_type))
    if rel is None or (iterable(rel) and len(rel) == 0):
        if return_type == 'callable':
            return lambda *args, **kwargs: True
        elif return_type == 'set':
            return S.Complexes

    if not isinstance(rel, Set):
        rel = sympified_tuple(rel)
        rel = solveset(And(*rel), gen)

    if return_type == 'set':
        return rel
    return lambda *args, **kwargs: rel.contains(*args)
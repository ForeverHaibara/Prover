import sympy as sp
from sympy.core import S, Basic
from sympy.polys import Poly, ZZ, QQ
from sympy.polys.numberfields import minimal_polynomial
from sympy.polys.rootoftools import ComplexRootOf
from sympy.simplify import fraction

from .solveset import wrap_relational
from ...core import make_traceable

def _closet(target, candidates, prec=20):
    """
    Find the closest candidate to the target.
    """
    candidates = [_ for _ in candidates if _.is_real]
    if len(candidates) == 1:
        return candidates[0]
    return min(candidates, key=lambda x: abs((x.n(prec) - target.n(prec))))

def _rootof_to_radicals(root):
    """
    Convert a sympy expression with ComplexRootOf class to radicals.
    """
    if not root.has(ComplexRootOf):
        return root
    poly = minimal_polynomial(root, polys=True)
    all_roots = sp.roots(poly, cubics=True, quartics=True)

    if not len(all_roots) == poly.degree():
        all_roots = poly.all_roots(radicals=False)

    return _closet(root, all_roots)

@make_traceable
def rational_eval(f, x):
    """
    Evaluate f(x) where f is a rational function.
    """
    if isinstance(f, Poly):
        v = f(x)
    else:
        if len(f.free_symbols) > 1:
            return
        elif len(f.free_symbols) == 0:
            return f
        gen = f.free_symbols.pop()
        p, q = fraction(f)
        p, q = Poly(p, gen), Poly(q, gen)        
        v = p(x)/q(x)

    if isinstance(x, Basic) and x.has(ComplexRootOf):
        v = _rootof_to_radicals(v)
    else:
        v = v.radsimp()
    return v

@make_traceable
def poly_roots(f, assumptions=None):
    verify = wrap_relational(assumptions, f.gen, return_type='callable')
    if f.domain in [ZZ, QQ]:
        roots = f.all_roots(radicals = False)
    else:
        roots = list(sp.roots(f, cubics=True, quartics=True).keys())
        
    roots = list(filter(verify, roots))
    return roots

@make_traceable
def poly_extrema(f, assumptions=None, prec=20):
    # first check whether it is a polynomial
    if (not isinstance(f, Poly)) and (f.free_symbols) == 1:
        f = Poly(f, f.free_symbols.pop())
    if isinstance(f, Poly) and len(f.gens) > 1:
        return

    fdiff = f.diff()

    domain = wrap_relational(assumptions, f.gen, return_type='set')
    domain = domain.intersect(S.Reals)

    roots = poly_roots(fdiff, domain)
    fdiv = f.div(fdiff)[1]
    fvals = [(root, fdiv(sp.re(root.n(prec))).n(prec)) for root in roots]

    for boundary in domain.boundary:
        fvals.append((boundary, f(boundary.n(prec)).n(prec)))

    if domain.sup is sp.oo:
        fvals.append((sp.oo, sp.oo if f.LC() > 0 else S.NegativeInfinity))
    if domain.inf is S.NegativeInfinity:
        fvals.append((S.NegativeInfinity, sp.sign(f.LC()) * (-1)**f.degree() * sp.oo))

    return fvals


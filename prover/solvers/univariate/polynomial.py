import sympy as sp
from sympy.core import S, Basic
from sympy.polys import Poly, ZZ, QQ
from sympy.polys.numberfields import minimal_polynomial
from sympy.polys.rootoftools import ComplexRootOf
from sympy.simplify import fraction
from sympy.sets import Complement, FiniteSet

from .solveset import wrap_relational
from .monotonicity import _range_from_critical_points
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
def rational_eval(f, x, dir='+-'):
    """
    Evaluate f(x) where f is a rational function.

    If x is infinite or a singularity of f, then the limit is returned.
    """
    def _poly_with_inf(f, x):
        if f.degree() == 0:
            return f.LC()
        elif x is S.Infinity:
            return S.Infinity if f.LC() > 0 else S.NegativeInfinity
        elif x is S.NegativeInfinity:
            return S.NegativeInfinity if (f.degree() % 2 == 0) ^ (f.LC() > 0) else S.Infinity
        return f(x)

    if isinstance(f, Poly):
        v = _poly_with_inf(f, x)
    else:
        if len(f.free_symbols) > 1:
            return
        elif len(f.free_symbols) == 0:
            return f
        gen = f.free_symbols.pop()
        p, q = fraction(f.together())
        p, q = Poly(p, gen), Poly(q, gen)

        if (x is S.Infinity) or (x is S.NegativeInfinity):
            if p.degree() > q.degree():
                return _poly_with_inf(p, x) * sp.sign(q.LC())
            elif p.degree() < q.degree():
                return sp.S(0)
            else:
                return p.LC() / q.LC()


        px, qx = p(x), q(x)
        if qx == 0:
            sgn_px = sp.sign(px)
            if dir == '+-' or sgn_px == 0:
                return S.ComplexInfinity
            for _ in range(q.degree()):
                q = q.diff()
                qx = q(x)
                sgn_qx = sp.sign(qx)
                if sgn_qx != 0:
                    if dir == '-':
                        sgn_qx = -sgn_qx
                    return sgn_px * sgn_qx * S.Infinity
            return
        else:
           v = p(x)/q(x)

    if isinstance(x, Basic) and x.has(ComplexRootOf):
        v = _rootof_to_radicals(v)
    else:
        v = v.radsimp()
    return v

@make_traceable
def poly_roots(f, domain=None):
    verify = wrap_relational(domain, f.gen, return_type='callable')
    if f.domain in [ZZ, QQ]:
        roots = f.all_roots(radicals = False)
    else:
        roots = list(sp.roots(f, cubics=True, quartics=True).keys())
        
    roots = list(filter(verify, roots))
    return roots

@make_traceable
def poly_extrema(f, domain=None):
    if (not isinstance(f, Poly)) and (f.free_symbols) == 1:
        f = Poly(f, f.free_symbols.pop())
    if isinstance(f, Poly) and len(f.gens) > 1:
        return

    fdiff = f.diff()

    domain = wrap_relational(domain, f.gen, return_type='set')
    domain = domain.intersect(S.Reals)

    roots = poly_roots(fdiff, domain)
    fdiv = f.div(fdiff)[1]
    criticals = [(root, rational_eval(fdiv, root)) for root in roots]

    flim = lambda x, dir: rational_eval(f, x, dir=dir)

    return _range_from_critical_points(flim, criticals, domain)

@make_traceable
def rational_extrema(f, domain=None):
    if isinstance(f, Poly):
        return poly_extrema(f, domain=domain)

    f = sp.cancel(f)
    if len(f.free_symbols) > 1:
        return
    elif len(f.free_symbols) == 0:
        return f
    gen = f.free_symbols.pop()
    f = f.together()
    p, q = fraction(f)
    p, q = Poly(p, gen), Poly(q, gen)

    if q.degree() == 0:
        return poly_extrema(Poly(p/q.LC(), gen), domain=domain)
    fdiff = p.diff() * q - p * q.diff()
    
    domain = wrap_relational(domain, gen, return_type='set')
    domain = domain.intersect(S.Reals)
    domain = Complement(domain, FiniteSet(*poly_roots(q)))

    roots = poly_roots(fdiff, domain)
    fdiv = (p.div(fdiff)[1].as_expr() / q.div(fdiff)[1].as_expr())
    criticals = [(root, rational_eval(fdiv, root)) for root in roots]

    flim = lambda x, dir: rational_eval(f, x, dir=dir)

    return _range_from_critical_points(flim, criticals, domain)
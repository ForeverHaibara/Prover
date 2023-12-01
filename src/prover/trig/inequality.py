from typing import Optional, List
from functools import lru_cache
import re

import sympy as sp
from sympy.printing.precedence import precedence_traditional, PRECEDENCE

from ...basic.types import is_rational_quadratic_roots
from ...basic.utils import radsimp
from ..proof import Proof


def substitute(f, arg, x, dir = '+-'):
    if not isinstance(x, sp.Expr) or x.is_finite:
        try:
            v = radsimp(f.subs(arg, x))
            assert v.is_finite
            return v
        except:
            pass
    v = sp.limit(f, arg, x, dir = dir)
    try:
        v = radsimp(v)
    except:
        pass
    return v


@lru_cache
def _get_transform(tp: str, n: int):
    """
    tp: one of 'u' or 'v' or 'w' or 'z', standing for sin, cos, tan and cot
    n : the degree
    For instance, 
    """
    t = sp.symbols('t')
    if n == 1:
        if tp == 'u':
            return (2*t)/(1+t*t)
        elif tp == 'v':
            return (1-t*t)/(1+t*t)
        elif tp == 'w':
            return (2*t)/(1-t*t)
        elif tp == 'z':
            return (1-t*t)/(2*t)
    
    if tp == 'z':
        return 1 / _get_transform('w', n)

    if n % 2 == 0:
        if tp == 'u':
            v = 2 * _get_transform('u', n // 2) * _get_transform('v', n // 2)
        elif tp == 'v':
            v = 2 * _get_transform('v', n // 2)**2 - 1
        elif tp == 'w':
            tmp = _get_transform('w', n // 2)
            v = 2 * tmp / (1 - tmp) / (1 + tmp)
    else:
        if tp == 'u':
            v =  _get_transform('u', n - 1) * (1-t*t)/(1+t*t) 
            v += _get_transform('v', n - 1) * (2*t)/(1+t*t)
        elif tp == 'v':
            v =  _get_transform('v', n - 1) * (1-t*t)/(1+t*t) 
            v -= _get_transform('u', n - 1) * (2*t)/(1+t*t)
        elif tp == 'w':
            tmp =  _get_transform('w', n - 1)
            v = (tmp*(1 - t*t) + 2*t) / (1 - t*t - tmp * 2*t)
    
    return v.factor()


def _convert_string_fill_cdot(f):
    for head in ('sin', 'cos', 'tan', 'cot'):
        f = f.replace('%s(x)'%head, '%s(1*x)'%head)
        f = re.sub('%s\((\d+)x\)'%head, lambda x: '%s(%s*x)'%(head, x.group(1)), f)

    return f


def _convert_string_to_poly(f, safe_degree = 10):
    f = _convert_string_fill_cdot(f)
    
    f = re.sub('sin\((\d+)\*x\)', lambda x: 'u%s'%x.group(1), f)
    f = re.sub('cos\((\d+)\*x\)', lambda x: 'v%s'%x.group(1), f)
    f = re.sub('tan\((\d+)\*x\)', lambda x: 'w%s'%x.group(1), f)
    f = re.sub('cot\((\d+)\*x\)', lambda x: 'z%s'%x.group(1), f)

    y = sp.sympify(f)

    def check_degree(x):
        assert x <= safe_degree, 'Degree must <= %d'%safe_degree
    
    if safe_degree is None or safe_degree <= 0:
        # disable degree check
        check_degree = lambda x: True

    params = {}
    for symbol in y.free_symbols:
        term = str(symbol)
        if len(term) == 1:
            tp, degree = term[0], 1
        else:
            tp, degree = term[0], int(term[1:])
        check_degree(degree)

        params[symbol] = _get_transform(tp, degree)

    y = y.subs(params)               

    return y


def prove_trig_extrema(
        f: str,
        method: str = 'auto',
        domain: Optional[List] = None,
        simplify: str = 'auto',
        linefeed: Optional[bool] = None,
        print_diff: bool = False,
        check_degree: int = 10
    ):
    """
    Prove the extrema of a trignometric function.

    Parameters
    -------
    f: str, a rational function wrt. sin(x), cos(x), tan(x)

    method: str, one of ['sos', 'derv', 'auto']
        Method 'sos' uses the sum of square method to display the proof of the result.
        Method 'derv' proves the extrema by computing the derivative.
        Method 'auto' chooses 'sos' when the extrema are rational while 'derv' otherwise.

    domain: None or a list of length two: [a,b], indicating the domain of x.
        When a is None, a = -\infty; when b is None, b = +\infty.
        Default to a = -\infty, b = +\infty.

    simplify: str, one of ['full', 'direct', 'none']
        'Full' applies arithmetic on the minimal polynomial to simplify the result. 
        'Direct' uses the sympy simplify function, which might be fast when handling quadratic roots but slow
        for cubic+ roots. 'None' does not make simplification, which is fast but sometimes not pretty.

    linefeed: Optional[bool]
        Whether writes the extrema in multiple lines to prevent the line to be too long when encountering
        cubic+ roots. Only takes effect when method == 'derv'.

    print_diff: bool
        Whether to print out the derivative in the terminal. Might be useful for further check in unsolvable ones.
    """

    method = method.lower()
    assert method in ['sos', 'derv', 'auto'], "Method should be one of 'sos' or 'derv' or 'auto'."

    simplify = simplify.lower()
    assert simplify in ['auto', 'full', 'direct', 'none'], "Simplify should be one of 'auto' or 'full' or 'direct' or 'none'."

    if domain is None:
        domain = [-sp.oo, sp.oo]
    else:
        _default = lambda x, y: y if x is None else radsimp(sp.tan(sp.sympify(x) / 2))
        domain = [_default(domain[0], -sp.oo), _default(domain[1], sp.oo)]
        if domain[0] == sp.zoo: domain[0] = -sp.oo
        if domain[1] == sp.zoo: domain[1] = sp.oo
        assert domain[0] <= domain[1], 'Require tan(domain[0]) <= tan(domain[1]).'

    regf = _convert_string_fill_cdot(f)
    x_ = sp.sympify(regf)
    y = _convert_string_to_poly(regf, check_degree)

    diff = y.diff('t').factor()
    t = sp.symbols('t')
    problem = sp.fraction(diff)[0].as_poly(t, extension = True)
    if print_diff: print(sp.latex(problem))

    extrema = _advanced_poly_roots(problem)

    # next decide which extrema correspond to the maximum and minimum
    extrema = list(extrema)
    extrema_numer = [sp.re(extrema[i].n(20)) for i in range(len(extrema))]

    # extract only roots within the domain
    boundary_filter = list(filter(lambda x: domain[0] <= extrema_numer[x] <= domain[1], range(len(extrema))))
    extrema = [extrema[i] for i in boundary_filter]
    extrema_numer = [extrema_numer[i] for i in boundary_filter]

    extrema_numerv = [sp.re(y.subs('t', i).n(20)) for i in extrema_numer]

    # be aware that the boundaries (sometimes sp.zoo) should be taken into account
    for i in range(2):
        extrema.append(domain[i])
        extrema_numer.append(domain[i])
        extrema_numerv.append(sp.re(substitute(y, 't', domain[i], dir = '+' if i == 0 else '-').n(20)))


    index_max = max(range(len(extrema_numerv)), key = lambda x: extrema_numerv[x])
    index_min = min(range(len(extrema_numerv)), key = lambda x: extrema_numerv[x])


    # sometimes the extrema is not rational, we simplify the equality using polynomial operations
    is_boundary = lambda x: None if x == domain[0] or x == domain[1] else problem
    dir_ = '+' if extrema_numer[index_max] == domain[0] else '-'
    extrema_max = _simplify_rational_polyroots(y, extrema[index_max], is_boundary(extrema[index_max]), method = simplify, dir = dir_)
    extrema_min = _simplify_rational_polyroots(y, extrema[index_min], is_boundary(extrema[index_min]), method = simplify, dir = dir_)

    iseq = lambda x: '\\approx ' if isinstance(x, sp.Float) else '='

    # generate the proof
    if method == 'auto':
        method = 'sos' if extrema_max.is_rational and extrema_min.is_rational else 'derv'

    s = '换元, 令 $t=\\tan (x/2)$, 则 $t\\in \\left[%s, %s\\right]$\n$$f(x) = %s = g(t) = %s$$\n$$g(t)=%s%s$$'%(
        sp.latex(domain[0]), sp.latex(domain[1]), sp.latex(x_), sp.latex(y), sp.latex(y.factor()), 
            '\\quad g\'(t)=%s'%sp.latex(diff) if method == 'derv' else '')

    if method == 'derv':
        rootsinfo = ['t_{%d} %s %s\\quad'%(i, iseq(z), sp.latex(z)) for i, z in enumerate(extrema)]
        if linefeed is None:
            linefeed = True if sum(len(_) for _ in rootsinfo) > 600 else False

        s += '\n解得极值点有 $$%s\\begin{aligned}& %s \\end{aligned}%s$$'%(
                ('\\left\\{' if linefeed else ''), 
                ('\\\\ & ' if linefeed else ' ').join(rootsinfo), 
                ('\\right.' if linefeed else '')
            )
        s += '\n代入验证最小值点 $t_{%d}$, 最大值点 $t_{%d}$'%(index_min, index_max)
        s += '\n$$%s\\begin{aligned}& g\\left(t_{%d}\\right)%s%s\\quad %s g\\left(t_{%d}\\right)%s%s\\end{aligned}%s$$'%(
                ('\\left\\{' if linefeed else ''),
                index_min, iseq(extrema_min), sp.latex(extrema_min), 
                '\\\\ & ' if linefeed else ' ',
                index_max, iseq(extrema_max), sp.latex(extrema_max),
                ('\\right.' if linefeed else '')
            )

    elif method == 'sos':        
        ext = lambda x: x if (x.is_finite and not x.is_rational and not isinstance(x, sp.Float)) else None
    
        def _sos(f, y, ext = None, direction = '>'):
            add_paren = lambda x: '\\left(%s\\right)'%sp.latex(x) if precedence_traditional(x) < PRECEDENCE['Mul'] else sp.latex(x)
            if not y.is_finite:
                return 'g(t)&%s%s'%(direction, sp.latex(y))
            else:
                return 'g(t)-%s&=%s %s 0'%(add_paren(y), sp.latex((f - y).factor(extension = ext)),
                    '\\geqslant' if direction == '>' else '\\leqslant')

        s += '\n$$\\begin{aligned}%s\\\\ %s\\end{aligned}$$'%(
            _sos(y, extrema_min, ext(extrema[index_min]), direction = '>'),
            _sos(y, extrema_max, ext(extrema[index_max]), direction = '<'),
        )
        s += '\n$f_{\\rm min}%s%s, f_{\\rm max}%s%s$, 取等分别为 $t_{\\rm min}%s%s, t_{\\rm max}%s%s$'%(
            iseq(extrema_min), sp.latex(extrema_min), 
            iseq(extrema_max), sp.latex(extrema_max),
            iseq(extrema_min), sp.latex(extrema[index_min]),
            iseq(extrema_max), sp.latex(extrema[index_max]))
    
    return Proof(s)


def _advanced_poly_roots(poly, prec = 20):
    """
    More carefully compute the real roots of a polynomial.
    """
    is_real = lambda v: v.is_real or (v.is_real is None and abs(sp.im(v.n(prec))) < sp.S(10)**(-prec+2))

    t = poly.args[-1]
    problem = poly.factor_list()[1]

    # PAY ATTENTION: they are times when the extrema has minimal polynomial with degree >= 5
    # e.g. 1/sin(x)+4/cos(x)    where (2t/(1-t*t))^3 = 1/4 (or introduce extension = 2**sp.Rational(1,3))
    # we should try rewriting the polynomial into expressions of (2t/(1-t*t))
    extrema = {}

    def _addroot(extrema, r):
        v = sp.re(r.n(prec))
        if extrema.get(v) is None:
            extrema[v] = r

    for subproblem in problem:
        p = subproblem[0]
        original_p = p
        
        # if not sp.polys.count_roots(p):
        #     continue 
        if p.degree() <= 4:
            for v in filter(is_real, sp.polys.roots(p)):
                _addroot(extrema, v)

        elif p.degree() <= 10 and all(x % 2 == 0 for (x,) in p.monoms()):
            # only has even-degree terms
            p = sum(coeff * t ** i for coeff, i in zip(p.all_coeffs()[::-2], range(p.degree()//2+1)))
            p = p.as_poly(t)
            for v in filter(is_real, sp.polys.roots(p)):
                if sp.re(v.n(prec)) >= 0:
                    _addroot(extrema, sp.sqrt(v))
                    _addroot(extrema, -sp.sqrt(v))

        elif p.degree() % 2 == 0:
            if p.degree() <= 10:
                n = p.degree()
                coeffs = p.all_coeffs()
                for flg in (1, -1):
                    initial_flg = -1 if flg == -1 and n % 4 == 2 else 1
                    for i in range(n//2):
                        if coeffs[i] != coeffs[n-i] * initial_flg:
                            break
                        initial_flg *= flg
                    else:
                        # u = t ± 1 / t
                        new_p_list = []
                        n = p.degree() // 2
                        for i in range(n+1):
                            if p.degree() < 2*n-i:
                                new_p_list.append(0)
                                continue 
                            new_p_list.append(p.coeffs()[0])
                            p = p.as_expr() - (t*t + flg)**(n-i) * (t)**i * p.coeffs()[0] 
                            p = p.as_poly(extension = True)

                        new_p = sum(coeff * t**(n-i) for i, coeff in enumerate(new_p_list))
                        new_p = new_p.as_poly(t)
                        for v in filter(is_real, sp.polys.roots(new_p)):
                                if flg == 1 and abs(sp.re(v.n(20))) < 2:
                                    continue
                                _addroot(extrema, v/2 + sp.sqrt(v**2 - flg*4)/2)
                                _addroot(extrema, v/2 - sp.sqrt(v**2 - flg*4)/2)
                        break
                        
            else:
                # try converting it to an equation wrt. (2t/(1-t^2))
                new_p_list = []
                n = p.degree() // 2
                for i in range(n+1):
                    if p.degree() < 2*n-i:
                        new_p_list.append(0)
                        continue 
                    new_p_list.append(p.coeffs()[0] * (-1)**(n-i) / 2**i)
                    p = p.as_expr() - (1 - t*t)**(n-i) * (2*t)**i * p.coeffs()[0] * (-1)**(n-i) / 2 ** i
                    p = p.as_poly(t)
                    
                # assert p is None or p.is_zero, 'Cannot solve all the extrema explicitly.'

                new_p = sum(coeff * t**i for i, coeff in enumerate(new_p_list))
                new_p = new_p.as_poly(t)

                for v in filter(is_real, sp.polys.roots(new_p)):
                    # 2t/(1-t*t) = v   =>  t*t + (2/v)t - 1 = 0  =>  t = -1/v +- sqrt(1+1/v/v) and v in R
                    _addroot(extrema, -1/v + sp.sqrt(1+v**(-2)))
                    _addroot(extrema, -1/v - sp.sqrt(1+v**(-2)))
    
        # add numerical roots
        p = original_p
        if p.degree() > 4:
            for r in sp.polys.nroots(p, n = prec):
                if r.is_real:
                    _addroot(extrema, r)

    return extrema.values()


def _simplify_rational_polyroots(
        target, 
        x, 
        original = None,
        method = 'auto',
        prec = 20,
        dir = '+-'
    ):
    """
    Compute target(x) where `x` is the root of polynomial `original` 
    and `target` is a rational function. When `original` is None, it uses
    the minimal polynomial of `x`.
    """

    arg = list(target.free_symbols)
    if len(arg) == 0:
        return target
    arg = arg[0]

    if isinstance(x, sp.Rational):
        return substitute(target, arg, x, dir = dir)
    elif isinstance(x, sp.Float):
        return substitute(target, arg, x, dir = dir).n(prec)
    elif x == sp.oo or x == -sp.oo:
        return substitute(target, arg, x, dir = dir)

    if method == 'auto':
        if is_rational_quadratic_roots(x):
            method = 'direct'
        else:
            method = 'full'

    if method == 'none':
        return target.subs(arg, x)
    elif method == 'direct':
        return substitute(target, arg, x, dir = dir)

    if original is None: 
        original = sp.minimal_polynomial(x).as_poly()
        _arg = original.args[-1]
        original = original.subs(_arg, arg)

    def _frob(poly):
        """obtain the frobenius form of a polynomial"""
        n = poly.degree()
        poly = poly.monic()
        A = sp.Matrix.zeros(n)
        for i, v in zip(range(n), poly.all_coeffs()[1:][::-1]):
            if i < n - 1: A[i+1,i] = 1
            A[i,-1] = -v
        return A

    A = _frob(original)

    def _poly_matrix(poly, A, original = None):
        if original: poly = poly % original
        coeffs = poly.all_coeffs()
        S = sp.Matrix.zeros(A.shape[0])
        for v in coeffs:
            # S = radsimp(S @ A)
            S = S @ A
            S += v * sp.Matrix.eye(A.shape[0])
        return S

    targett = sp.fraction(sp.cancel(target))
    final0 = _poly_matrix(targett[0].as_poly(arg, extension = True), A, original)
    final1 = _poly_matrix(targett[1].as_poly(arg, extension = True), A, original)
    
    final0 = radsimp(final0)
    final1 = radsimp(final1)

    final = final0 @ sp.Matrix.inv(final1)
    final = radsimp(final)

    det = sp.det(arg * sp.Matrix.eye(final.shape[0]) - final)
    det_ = det.as_poly(arg, extension = True)
    if det_ is None:
        deta, detb = sp.fraction(det)
        deta, detb = deta.as_poly(arg, extension = True), detb.as_poly(arg, extension = True)
        det_ = divmod(deta, detb)[0]

    eigvals = _advanced_poly_roots(det_)

    # find the nearest root to the numerical approximation
    approx = target.subs(arg, x.n(prec)).n(prec)
    eigvals = [(abs(_.n(prec) - approx), i, _) for i, _ in enumerate(eigvals)]

    return min(eigvals)[2]
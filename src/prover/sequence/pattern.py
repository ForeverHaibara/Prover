import sympy as sp

from ..proof import Proof

def prove_find_pattern(y: list, target = 114514):
    poly = 0
    x = list(range(1, len(y)+1))
    t = sp.symbols('x')
    for i in range(len(y)):
        if y[i] is None:
            y[i] = target 
    for i, v in zip(x, y):
        if v is not None:
            subpoly = 1
            scale = 1
            for p, q in zip(x, y):
                if q is not None and p != i:
                    subpoly *= t - p 
                    scale *= i - p 
        poly += subpoly / scale * v
    poly = poly.as_poly(t).as_expr()
        
    s = '正確答案是 $%s$\n\n因為當\n$$f(x)=%s$$\n$$\\begin{aligned}'%(target, sp.latex(poly)) 
    for i, v in zip(x, y):
        if v != target:
            s += 'f\\left(%s\\right)&=%s\\\\ '%(i, v)
    s = s[:-3] + '\\quad\\quad 真有邏輯\\\\ ' 
    for i, v in zip(x, y):
        if v == target:
            s += 'f\\left(%s\\right)&=%s\\\\ '%(i, v)
    s += '\\end{aligned}$$\n $\\quad\\quad$真是有趣\n\n哇 數學\n\n$\\quad\\quad\\quad$哇'
    return Proof(s)
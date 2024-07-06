from sympy.core import Dummy, Tuple

from .traceable import Traceable, TraceableExpr, mathref


def change_of_var(f, subs, name=None, result=None, simplify=None):
    if result is not None:
        value2 = result
    else:
        value2 = f.subs(subs) if not isinstance(f, Traceable) else f.value.subs(subs)
        if callable(simplify):
            value2 = simplify(value2)

    if isinstance(f, Traceable):
        defin = f.definition
        description = '将 $%s$ 代入 $%s$, 得\n\\begin{equation}' % (mathref(subs), mathref(f.name))

        defin2 = defin.subs(subs)
        if name is not None:
            description += '%s = ' % mathref(name)
        if defin2 == value2:
            description += '%s = %s\\end{equation}' % (mathref(f), mathref(value2))
        else:
            description += '%s = %s = %s\\end{equation}' % (mathref(f), mathref(defin2), mathref(value2))

        if name is None:
            return Traceable(f, defin.subs(subs), value2, description=description)
        else:
            return Traceable(name, f, value2, description=description)
    return value2


def make_traceable(func):
    def wrapper(*args, **kwargs):
        traceable = kwargs.pop('traceable', False)
        result = func(*args, **kwargs)
        if (traceable is False) or isinstance(result, Traceable):
            return result
        if traceable is True:
            traceable = Dummy()
        return Traceable(traceable, Tuple(*args), result)
    return wrapper
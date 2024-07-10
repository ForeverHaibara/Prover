"""
输出证明时: 有一些定义(definition), 引理(lemma)...
输出函数加一个字典, 如果某个定义或引理被显示过一次, 则不再显示

每个数学元素要记录得到它的证明. 例如求根写成 “由\\eqref{...}解得...”

打印最终完整证明时, 对于每个父元素, 递归打印其父元素, 直到根元素(定义...)

class NamedExpr

"""
from functools import partial

from sympy.core import Basic, Expr, Symbol, Dict, Tuple, sympify
from sympy.core.function import Application, Function, Derivative, UndefinedFunction
from sympy.logic.boolalg import Boolean, BooleanFunction
from sympy.printing import latex
from sympy.utilities.iterables import iterable

def stop_at_traceable(obj):
    """
    Return an object stopping at Traceable objects to shorten the expression.
    """
    return obj.replace(Traceable, lambda *x: x[0])

def _merge_suffixes(suffix):
    # 'S_2_{34} -> S_{2,34}'
    splits = suffix.split('_')
    if len(splits) == 0:
        return suffix
    return splits[0] + '_{%s}'%(','.join(splits[1:]).translate(str.maketrans('','','{}')),)



class Traceable(Basic):
    """
    Wrapper for sympy objects with traceable graph.

    Parameters
    ==========
    name : Abbreviation for the instance. Either sympy Symbol or UndefinedFunction.
    definition : A sympy class containing its parent objects so
        that we can trace back to the root object.
    value : Simplified value of the object. If value is not provided, it is set to definition.
        If definition and value are not the same, the object means that the definition could imply the value.
    """
    _description: str = None
    def __new__(cls, *args, **kwargs):
        description = kwargs.pop('description', None)
        args = sympify(args)
        if len(args) == 2 and isinstance(args[1], Expr) and cls is Traceable:
            cls = TraceableExpr
        elif len(args) == 3 and isinstance(args[2], Expr) and cls is Traceable:
            cls = TraceableExpr
        obj = super().__new__(cls, *args, **kwargs)
        obj._description = description
        for funcname in ('__len__', '__iter__'):
            if hasattr(obj.value, funcname):
                setattr(obj, funcname, getattr(obj.value, funcname))

        return obj

    @property
    def name(self):
        return self.args[0]

    @property
    def definition(self):
        return self.args[1]

    @property
    def value(self):
        return self.args[1] if len(self.args) <= 2 else self.args[2]

    def describe(self, **kwargs):
        if self._description is not None:
            if isinstance(self._description, str):
                return self._description
            elif callable(self._description):
                return self._description(**kwargs)
            elif isinstance(self._description, Basic):
                return ref(self._description, **kwargs)
            raise TypeError(f'Invalid description type: {type(self._description)}')

        name, definition, value = self.name, self.definition, self.value
        s = ''
        if isinstance(definition, Expr) and isinstance(value, Expr):
            if definition.has(Traceable):
                if isinstance(name, (Symbol, UndefinedFunction)):
                    if definition == value:
                        s = '令 $%s = %s$.'%(ref(name), ref(definition))
                    else:
                        s = '令\n\\begin{equation}\\label{%d}%s = %s = %s.\\end{equation}'%(
                            id(self), mathref(name), mathref(definition), mathref(value)
                        )
                else:
                    name_str = mathref(name)
                    def_str = mathref(definition)
                    if name_str == def_str:
                        if definition != value:
                            s = '则\n\\begin{equation}%s = %s.\\end{equation}'%(name_str, mathref(value))
                    else:
                        if definition != value:
                            s = '则\n\\begin{equation}%s = %s = %s.\\end{equation}'%(
                                name_str, def_str, mathref(value)
                            )
                        else:
                            s = '则\n\\begin{equation}%s = %s.\\end{equation}'%(name_str, def_str)
            else: # not self.definition.has(Traceable)
                s = '定义 $%s = %s$.' % (mathref(name), mathref(definition))
                

            return s

        else:
            return '由 $%s$ 得 $%s = %s$.' % (mathref(self.definition), mathref(self.name), mathref(self.value))

            name, definition = self.name, self.definition
            return '定义 $%s = %s$.' % (latex(name), latex(stop_at_traceable(definition)))
        
        return ''

    def doit(self, **kwargs):
        return self.value.doit(**kwargs)

    def __getitem__(self, i):
        if not hasattr(self.value, '__getitem__'):
            raise TypeError(f'Value of class {self.value.__class__} does not support __getitem__.')

        i = sympify(i)
        name = self.name.name if hasattr(self.name, 'name') else self.name
        func = self.name.func if hasattr(self.name, 'func') else Symbol
        suffixed = func(_merge_suffixes(name + '_{%s}' % i))
        cls = _promote_traceable_classes(self.value[i].__class__)
        return cls(suffixed, Tuple(self, i), self.value[i], description='')



class TraceableApplication(Traceable, Application):
    ...


class TraceableExpr(TraceableApplication, Function):
    def diff(self, *args, **kwargs):
        evaluate = kwargs.get('evaluate', None)
        if evaluate is not None and (not evaluate):
            return Derivative(self, *args, **kwargs)

        kwargs['evaluate'] = False if evaluate is None else evaluate
        name2 = self.name.diff(*args, **kwargs)

        # definition2 = self.definition
        # if hasattr(definition2, 'diff'):
        #     if not definition2.has(Traceable):
        #         kwargs['evaluate'] = True if evaluate is None else evaluate
        #     definition2 = definition2.diff(*args, **kwargs)
        #     if not definition2.has(Traceable):
        #         definition2 = definition2.factor()
        kwargs['evaluate'] = False
        definition2 = self.diff(*args, **kwargs)

        value2 = self.definition
        if len(self.args) > 2 and hasattr(self.value, 'diff'):
            value2 = self.value
        
        if not self.value.has(Traceable):
            kwargs['evaluate'] = True if evaluate is None else evaluate
        value2 = self.value.diff(*args, **kwargs)
        if not value2.has(Traceable):
            value2 = value2.factor()
        return TraceableExpr(name2, definition2, value2)

        return TraceableExpr(name2, definition2)


class TraceableBoolean(TraceableApplication, BooleanFunction):
    ...


class TraceableSet(Traceable):
    @property
    def parent(self):
        return self.args[1]

    def describe(self):
        if self._description is None:
            return '由 $%s$ 得 $%s$.' % (latex(self.parent), latex(self.value))
        return super().describe()



class TraceableSolveSet(TraceableSet):
    def describe(self):
        def _value_parser():
            if iterable(self.value) and len(self.value) == 1:
                value = self.value[0]
                environ = lambda s: '$%s$.'%s
            else:
                value = self.value
                environ = lambda s: '\n\\begin{equation}%s.\\end{equation}'%s
            s = mathref(value).replace(':', '=')
            return environ(s)

        if self._description is None:
            if iterable(self.parent) and len(self.parent) > 1:
                return '联立 %s 解得 %s' % (ref(self.parent, delimiter='$'), _value_parser())
            else:
                parent = self.parent[0] if iterable(self.parent) else self.parent
                return '由 %s 解得 %s' % (ref(parent, delimiter='$'), _value_parser())

        return super().describe()


def _promote_traceable_classes(cls):
    if issubclass(cls, Traceable):
        return cls
    elif issubclass(cls, Expr):
        return TraceableExpr
    elif issubclass(cls, (Boolean, BooleanFunction)):
        return TraceableBoolean
    return Traceable


def ref(obj, **kwargs):
    delimiter = kwargs.pop('delimiter', '')
    if delimiter is not None and delimiter != '':
        s = ref(obj, **kwargs)
        if not s.startswith('\\ref') and not s.startswith('\\eqref'):
            s = '%s%s%s'%(delimiter, s, delimiter)
        return s

    math = kwargs.pop('math', False)
    s = f'\\ref{{{id(obj)}}}'
    if not isinstance(obj, Basic):
        obj = sympify(obj)

    if math:
        s = latex(stop_at_traceable(obj))

    else:
        if isinstance(obj, TraceableExpr):
            s = f'\\eqref{{{id(obj)}}}'
        elif obj.has(Traceable):
            if iterable(obj):
                0

        if not isinstance(obj, Traceable):
            s = latex(stop_at_traceable(obj))
    s = s.replace(':', '=')
    return s

def mathref(obj, **kwargs):
    kwargs['math'] = True
    return ref(obj, **kwargs)
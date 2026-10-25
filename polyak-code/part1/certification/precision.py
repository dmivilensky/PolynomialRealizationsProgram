"""Scoped precision settings; no verification leaves process-global changes behind."""
from functools import wraps


def local_precision(*,bits=160,digits=40):
    def decorate(function):
        @wraps(function)
        def scoped(*args,**kwargs):
            from flint import ctx
            import mpmath as mp
            with ctx.workprec(bits),mp.workdps(digits):
                return function(*args,**kwargs)
        return scoped
    return decorate

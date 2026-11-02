"""Compiled unconstrained L-BFGS via SciPy's L-BFGS-B 3.0 port.

Sources: Byrd, Lu, Nocedal and Zhu, SIAM J. Sci. Comput. 16 (1995), 1190--1208,
https://doi.org/10.1137/0916069; Zhu et al., Algorithm 778, ACM TOMS 23 (1997),
550--560, https://doi.org/10.1145/279232.279236; Morales and Nocedal, Remark
on Algorithm 778, ACM TOMS 38 (2011), Article 7,
https://doi.org/10.1145/2049662.2049669.

With no bounds, the compact L-BFGS direction uses scalar initial Hessian
(y.T y)/(s.T y); the compiled solver retains its More--Thuente search. Primary
memory is 20 and maxls=20. Relative objective and gradient thresholds are zero,
with large native iteration/evaluation caps, so the shared oracle decides
success. The native code may still terminate on stagnation or search failure;
its status is preserved. Every compiled function/gradient evaluation goes
through O.fg. Complete compiled optimization and floating-point line search
are not covered by the mathematical Lean L-BFGS update model.
"""

from scipy.optimize import minimize


def solve(O, x0, m=10, maxls=20):
    res = minimize(
        O.fg,
        x0,
        jac=True,
        method="L-BFGS-B",
        callback=lambda xk: O.mark_iter(),
        options=dict(maxcor=m, ftol=0.0, gtol=0.0, maxiter=10**9, maxfun=10**9, maxls=maxls),
    )
    O.note("message", str(res.message))
    O.note("scipy_status", int(res.status))

"""CG_DESCENT 6.8 (memory = 0) and L-CG_DESCENT 6.8 (memory = 11), the original C code of Hager and Zhang through
the pycgdescent wheel (A. Fikl, version 0.12.1, which builds CG_DESCENT-C 6.8 with small non-algorithmic patches).

Sources: W. W. Hager, H. Zhang, "A new conjugate gradient method with guaranteed descent and an efficient line
search", SIAM J. Optim. 16 (2005) 170-192; W. W. Hager, H. Zhang, "Algorithm 851: CG_DESCENT, a conjugate gradient
method with guaranteed descent", ACM TOMS 32 (2006) 113-137; W. W. Hager, H. Zhang, "The limited memory conjugate
gradient method", SIAM J. Optim. 23 (2013) 2150-2168 (L-CG_DESCENT, memory > 0).
Settings: all defaults of CG_DESCENT 6.8 (AWolfe = 0 with the automatic switch to approximate Wolfe, QuadStep = 1,
delta = 0.1, sigma = 0.9, eps = 1e-6, theta = 1, psi0 = 0.01, psi1 = 1, psi2 = 2, nslow = 1000, ...), except
memory (0 for CG_DESCENT, 11 = its default for L-CG_DESCENT) and the stopping tolerance tol = 1e-300 with
StopFac = 0 (gradient test effectively off: the oracle decides).  The C code calls fun (f only: QuadStep),
jac (g only: approximate-Wolfe secant steps) and funjac; all three are passed and counted by the oracle
(an f-only or g-only call at a new point is one point).
The oracle's stop signals propagate through the C code as C++ exceptions (tested); a caller-owned work array
avoids the leak of the C work space when that happens; it must be zero-initialized (an np.empty work array, as
returned by pycgdescent.allocate_work_for, made the run stop at x0 with status 11 on BAR).  The final CG_DESCENT
status (e.g. 4 = line search failed, 9 = no cost or gradient improvement) is recorded in info when it stops by
itself.
"""

import numpy as np
import pycgdescent as cgd


def solve(O, x0, memory=0, **options):
    opts = dict(memory=memory, StopFac=0.0)
    opts.update(options)
    param = cgd.OptimizeOptions(**opts)
    work = np.zeros(
        cgd.min_work_size(param, len(x0))
    )  # must be zeroed: allocate_work_for gives np.empty, and
    # garbage there made CG_DESCENT stop with status 11

    def fun(x):
        return O.f(x)

    def jac(g, x):
        g[:] = O.g(x)

    def funjac(g, x):
        f, gg = O.fg(x)
        g[:] = gg
        return f

    def cb(info):
        if info.it > 0:  # CG_DESCENT also calls back at the initial point (iter = 0).
            O.mark_iter()
        return 1

    r = cgd.minimize(
        fun,
        np.array(x0, dtype=float),
        jac=jac,
        funjac=funjac,
        tol=1e-300,
        options=param,
        callback=cb,
        work=work,
    )
    O.note("status", int(r.status))
    O.note("message", r.message)
    O.note("nsubspaces", int(r.nsubspaces))

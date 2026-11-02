/* SC-MSS / SC-SR1: original C implementation from the published equations.
   Source comparison and numerical choices: docs/NativeSCAudit.md.
   No n-by-n Hessian/complement basis and no allocation within iterations. */
#include "sc_native.h"
#include <float.h>
#include <limits.h>
#include <math.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static void gemm(const CNBackend *b, char ta, char tb, int m, int n, int k,
                 const double *A, int lda, const double *B, int ldb, double *C,
                 int ldc) {
  double one = 1, zero = 0;
  b->blas.dgemm(&ta, &tb, &m, &n, &k, &one, (double *)A, &lda, (double *)B,
                &ldb, &zero, C, &ldc);
}
int cn_sc_init(CNScWork *w, int n, int m, int q) {
  memset(w, 0, sizeof(*w));
  if (n < 1 || m < 1 || q < 1 || m > INT_MAX / 1024 || n > INT_MAX / 8)
    return CN_INVALID;
  w->n = n;
  w->m = m;
  w->q = q;
  w->k = 2 * m;
  /* Generous LAPACK workspace supports blocked QR/SVD/SYEV, reused. */
  w->lwork = 128 * w->k + 4 * n;
  size_t nv = (size_t)n * (8 * m + 2) + 8 * (size_t)w->k * w->k +
              5 * (size_t)w->k + w->lwork + q;
  if (nv > SIZE_MAX / sizeof(double))
    return CN_MEMORY;
  w->arena = calloc(nv, sizeof(double));
  w->piv = calloc((size_t)w->k, sizeof(int));
  if (!w->arena || !w->piv) {
    cn_sc_free(w);
    return CN_MEMORY;
  }
  double *t = w->arena;
#define TAKE(field, count)                                                     \
  w->field = t;                                                                \
  t += (count)
  TAKE(S, (size_t)n * m);
  TAKE(Y, (size_t)n * m);
  TAKE(Sn, (size_t)n * m);
  TAKE(Yn, (size_t)n * m);
  TAKE(Psi, (size_t)n * w->k);
  TAKE(P, (size_t)n * w->k);
  TAKE(small, (size_t)w->k * w->k);
  TAKE(small2, (size_t)w->k * w->k);
  TAKE(small3, (size_t)w->k * w->k);
  TAKE(small4, (size_t)w->k * w->k);
  TAKE(R, (size_t)w->k * w->k);
  TAKE(W, (size_t)w->k * w->k);
  TAKE(X, (size_t)w->k * w->k);
  TAKE(tmp, (size_t)w->k * w->k);
  TAKE(eval, w->k);
  TAKE(tau, w->k);
  TAKE(sv, w->k);
  TAKE(vec, n);
  TAKE(vec2, n);
  TAKE(work, w->lwork);
  TAKE(history, q);
#undef TAKE
  return CN_OK;
}
void cn_sc_free(CNScWork *w) {
  free(w->arena);
  free(w->piv);
  memset(w, 0, sizeof(*w));
}

/* B = P diag(lambda) P' + gamma (I-PP'). Normalize each pair
   simultaneously: all compact formulas are invariant under this change. */
int cn_sc_model(CNScWork *w, const CNBackend *b, int variant, double zeta,
                double zc, double tol) {
  (void)zc;
  int n = w->n, p = w->p, ld = w->k, info, one = 1;
  w->rank = 0;
  if (!p)
    return CN_OK;
  for (int j = 0; j < p; j++) {
    double ns = cn_norm(b, n, w->S + (size_t)n * j);
    if (!(ns > 0) || !isfinite(ns))
      return CN_NUMERICAL;
    for (int i = 0; i < n; i++) {
      w->Sn[i + (size_t)n * j] = w->S[i + (size_t)n * j] / ns;
      w->Yn[i + (size_t)n * j] = w->Y[i + (size_t)n * j] / ns;
    }
  }
  /* X = lower(S'Y)+strict-lower(S'Y)' for chronological pairs. */
  gemm(b, 'T', 'N', p, p, n, w->Sn, n, w->Yn, n, w->X, ld);
  for (int j = 0; j < p; j++)
    for (int i = 0; i < j; i++)
      w->X[i + ld * j] = w->X[j + ld * i];
  int cols = variant ? p : 2 * p;
  if (!variant) {
    /* The author's LMSS_SC retains the raw m-window, selecting independent
       columns of normalized S for the compact model, including dependent
       trials. */
    memcpy(w->Psi, w->Sn, (size_t)n * p * sizeof(double));
    memset(w->piv, 0, (size_t)p * sizeof(int));
    b->dgeqp3(&n, &p, w->Psi, &n, w->piv, w->tau, w->work, &w->lwork, &info);
    if (info)
      return CN_NUMERICAL;
    int selected = 0, mn = n < p ? n : p;
    double lead = mn ? fabs(w->Psi[0]) : 0;
    for (int j = 0; j < mn; j++)
      if (fabs(w->Psi[j + (size_t)n * j]) > tol * lead)
        w->piv[selected++] = w->piv[j] - 1;
    for (int j = 0; j < selected; j++)
      for (int i = j + 1; i < selected; i++)
        if (w->piv[i] < w->piv[j]) {
          int t = w->piv[i];
          w->piv[i] = w->piv[j];
          w->piv[j] = t;
        }
    for (int j = 0; j < selected; j++) {
      int src = w->piv[j];
      double ns = cn_norm(b, n, w->S + (size_t)n * src);
      for (int i = 0; i < n; i++) {
        w->Sn[i + (size_t)n * j] = w->S[i + (size_t)n * src] / ns;
        w->Yn[i + (size_t)n * j] = w->Y[i + (size_t)n * src] / ns;
      }
    }
    p = selected;
    cols = 2 * p;
    if (!p)
      return CN_OK;
    gemm(b, 'T', 'N', p, p, n, w->Sn, n, w->Yn, n, w->X, ld);
    for (int j = 0; j < p; j++)
      for (int i = 0; i < j; i++)
        w->X[i + ld * j] = w->X[j + ld * i];
    /* W=(S'S)^-1 using QR, avoiding the squared-condition Gram solve. */
    memcpy(w->Psi, w->Sn, (size_t)n * p * sizeof(double));
    b->dgeqrf(&n, &p, w->Psi, &n, w->tau, w->work, &w->lwork, &info);
    if (info)
      return CN_NUMERICAL;
    memset(w->R, 0, (size_t)ld * ld * sizeof(double));
    memset(w->small, 0, (size_t)ld * ld * sizeof(double));
    for (int j = 0; j < p; j++)
      for (int i = 0; i <= j; i++)
        w->R[i + ld * j] = w->Psi[i + (size_t)n * j];
    for (int j = 0; j < p; j++)
      w->small[j + ld * j] = 1;
    char side = 'L', upper = 'U', no = 'N', diag = 'N';
    double alpha = 1;
    b->blas.dtrsm(&side, &upper, &no, &diag, &p, &p, &alpha, w->R, &ld,
                  w->small, &ld);
    gemm(b, 'N', 'T', p, p, p, w->small, ld, w->small, ld, w->W, ld);
    gemm(b, 'N', 'N', p, p, p, w->W, ld, w->X, ld, w->tmp, ld);
    gemm(b, 'N', 'N', p, p, p, w->tmp, ld, w->W, ld, w->small, ld);
    memset(w->small2, 0, (size_t)ld * ld * sizeof(double));
    for (int j = 0; j < p; j++)
      for (int i = 0; i < p; i++) {
        w->small2[i + ld * j] = -zeta * w->W[i + ld * j] - w->small[i + ld * j];
        w->small2[i + ld * (j + p)] = w->W[i + ld * j];
        w->small2[i + p + ld * j] = w->W[i + ld * j];
      }
    memcpy(w->Psi, w->Sn, (size_t)n * p * sizeof(double));
    memcpy(w->Psi + (size_t)n * p, w->Yn, (size_t)n * p * sizeof(double));
  } else {
    gemm(b, 'T', 'N', p, p, n, w->Sn, n, w->Sn, n, w->small, ld);
    for (int j = 0; j < p; j++)
      for (int i = 0; i < p; i++)
        w->small2[i + ld * j] = w->X[i + ld * j] - zeta * w->small[i + ld * j];
    for (int j = 0; j < p; j++)
      for (int i = 0; i < n; i++)
        w->Psi[i + (size_t)n * j] =
            w->Yn[i + (size_t)n * j] - zeta * w->Sn[i + (size_t)n * j];
  }
  if (!cn_finite(cols * ld, w->small2) || !cn_finite(n * cols, w->Psi))
    return CN_NUMERICAL;
  memset(w->piv, 0, (size_t)cols * sizeof(int));
  b->dgeqp3(&n, &cols, w->Psi, &n, w->piv, w->tau, w->work, &w->lwork, &info);
  if (info)
    return CN_NUMERICAL;
  int mn = n < cols ? n : cols, r = 0;
  double first = mn ? fabs(w->Psi[0]) : 0;
  for (int j = 0; j < mn; j++)
    if (fabs(w->Psi[j + (size_t)n * j]) > tol * first)
      r++;
  if (!r)
    return CN_OK;
  memset(w->R, 0, (size_t)ld * ld * sizeof(double));
  for (int j = 0; j < cols; j++)
    for (int i = 0; i < r && i <= j; i++)
      w->R[i + ld * j] = w->Psi[i + (size_t)n * j];
  for (int j = 0; j < cols; j++)
    for (int i = 0; i < cols; i++)
      w->small[i + ld * j] = w->small2[(w->piv[i] - 1) + ld * (w->piv[j] - 1)];
  if (variant) {
    /* Solve K Z=R' rather than form K^-1. */
    for (int j = 0; j < r; j++)
      for (int i = 0; i < cols; i++)
        w->tmp[i + ld * j] = w->R[j + ld * i];
    b->blas.dgesv(&cols, &r, w->small, &ld, w->piv, w->tmp, &ld, &info);
    if (info)
      return CN_NUMERICAL;
    gemm(b, 'N', 'N', r, r, cols, w->R, ld, w->tmp, ld, w->small3, ld);
  } else {
    gemm(b, 'N', 'N', r, cols, cols, w->R, ld, w->small, ld, w->tmp, ld);
    gemm(b, 'N', 'T', r, r, cols, w->tmp, ld, w->R, ld, w->small3, ld);
  }
  for (int j = 0; j < r; j++)
    for (int i = 0; i < j; i++) {
      double a = .5 * (w->small3[i + ld * j] + w->small3[j + ld * i]);
      w->small3[i + ld * j] = w->small3[j + ld * i] = a;
    }
  if (!cn_finite(ld * r, w->small3))
    return CN_NUMERICAL;
  char eig = 'V', u = 'U';
  b->blas.dsyev(&eig, &u, &r, w->small3, &ld, w->eval, w->work, &w->lwork,
                &info);
  if (info)
    return CN_NUMERICAL;
  b->dorgqr(&n, &r, &r, w->Psi, &n, w->tau, w->work, &w->lwork, &info);
  if (info)
    return CN_NUMERICAL;
  gemm(b, 'N', 'N', n, r, r, w->Psi, n, w->small3, ld, w->P, n);
  for (int i = 0; i < r; i++)
    w->eval[i] += zeta;
  w->rank = r;
  (void)one;
  return cn_finite(n * r, w->P) && cn_finite(r, w->eval) ? CN_OK : CN_NUMERICAL;
}

/* Exact separable shape-changing infinity subproblem, including indefinite
   scalar boxes and a zero-gradient negative-curvature complement. */
int cn_sc_shape(const CNBackend *b, int n, int r, const double *P,
                const double *lam, double gamma, const double *g, double delta,
                double *p, double *pBp, double *a, double *gp) {
  if (!(delta > 0) || !isfinite(delta) || !isfinite(gamma))
    return CN_INVALID;
  memcpy(gp, g, (size_t)n * sizeof(double));
  for (int j = 0; j < r; j++) {
    a[j] = cn_dot(b, n, P + (size_t)n * j, g);
    for (int i = 0; i < n; i++)
      gp[i] -= P[i + (size_t)n * j] * a[j];
  }
  if (r == n)
    memset(gp, 0, (size_t)n * sizeof(double));
  double ng = cn_norm(b, n, gp);
  if (gamma > 0 && ng <= delta * gamma) {
    for (int i = 0; i < n; i++)
      p[i] = -gp[i] / gamma;
  } else if (ng > 0) {
    for (int i = 0; i < n; i++)
      p[i] = -delta * gp[i] / ng;
  } else if (gamma < 0 && r < n) {
    int row = 0;
    double best = INFINITY;
    for (int i = 0; i < n; i++) {
      double t = 0;
      for (int j = 0; j < r; j++)
        t += P[i + (size_t)n * j] * P[i + (size_t)n * j];
      if (t < best) {
        best = t;
        row = i;
      }
    }
    for (int i = 0; i < n; i++) {
      double t = 0;
      for (int j = 0; j < r; j++)
        t -= P[i + (size_t)n * j] * P[row + (size_t)n * j];
      p[i] = t;
    }
    p[row] += 1;
    double np = cn_norm(b, n, p);
    if (!(np > 0))
      return CN_NUMERICAL;
    for (int i = 0; i < n; i++)
      p[i] *= delta / np;
  } else
    memset(p, 0, (size_t)n * sizeof(double));
  *pBp = gamma * cn_dot(b, n, p, p);
  for (int j = 0; j < r; j++) {
    double v = -delta * (a[j] < 0 ? -1 : 1);
    if (lam[j] == 0 && a[j] == 0)
      v = 0;
    if (lam[j] > 0)
      v = fmax(-delta, fmin(delta, -a[j] / lam[j]));
    *pBp += lam[j] * v * v;
    for (int i = 0; i < n; i++)
      p[i] += P[i + (size_t)n * j] * v;
  }
  return cn_finite(n, p) && isfinite(*pBp) ? CN_OK : CN_NUMERICAL;
}

static void sc_history(CNScWork *w, const CNBackend *b, const double *s,
                       const double *y) {
  double sy = cn_dot(b, w->n, s, y), v = NAN;
  if (sy != 0) {
    double t = cn_dot(b, w->n, y, y) / sy;
    if (isfinite(t))
      v = t;
  }
  w->history[w->hnext] = v;
  w->hnext = (w->hnext + 1) % w->q;
  if (w->hcount < w->q)
    w->hcount++;
}
static double sc_gamma(const CNScWork *w, double old) {
  double v = -INFINITY;
  for (int j = 0; j < w->hcount; j++)
    if (isfinite(w->history[j]))
      v = fmax(v, w->history[j]);
  return isfinite(v) ? v : old;
}
static void sc_append(CNScWork *w, const double *s, const double *y) {
  if (w->p == w->m) {
    memmove(w->S, w->S + w->n, (size_t)w->n * (w->m - 1) * sizeof(double));
    memmove(w->Y, w->Y + w->n, (size_t)w->n * (w->m - 1) * sizeof(double));
    w->p--;
  }
  memcpy(w->S + (size_t)w->n * w->p, s, (size_t)w->n * sizeof(double));
  memcpy(w->Y + (size_t)w->n * w->p, y, (size_t)w->n * sizeof(double));
  w->p++;
}
static int sc_mss_remember(CNScWork *w, const CNBackend *b, const double *s,
                           const double *y, double tol) {
  (void)tol;
  double ns = cn_norm(b, w->n, s);
  if (!(ns > 0) || !isfinite(ns))
    return 0;
  sc_append(w, s, y);
  return 1;
}
static int sc_sr1_remember(CNScWork *w, const CNBackend *b, const double *s,
                           const double *y, const double *Bs, double tol) {
  for (int i = 0; i < w->n; i++)
    w->vec[i] = y[i] - Bs[i];
  double nv = cn_norm(b, w->n, w->vec), ns = cn_norm(b, w->n, s);
  if (ns > 0 && nv > 0 && isfinite(nv) &&
      fabs(cn_dot(b, w->n, s, w->vec)) > tol * fmax(ns * nv, 1e-10)) {
    sc_append(w, s, y);
    return 1;
  }
  return 0;
}
int cn_sc_execute(int variant, const CNParams *par, const CNBackend *b,
                  const CNOracle *O, const double *x0) {
  int n = O->n, m = cn_int(par, "m", variant ? 5 : 3),
      q = cn_int(par, "q", variant ? 7 : 5);
  double rank_tol = cn_get(par, "rank_tol", 1e-10),
         skip_tol = cn_get(par, "r", 1e-8);
  int dense = cn_int(par, "init_dense", 1), status = CN_OK;
  if ((variant != 0 && variant != 1) || m < 1 || q < 1 || !(rank_tol > 0) ||
      !(skip_tol >= 0))
    return CN_INVALID;
  /* Model dimension never exceeds n; q remains an independent observation
   * history. */
  CNScWork w;
  status = cn_sc_init(&w, n, m, q);
  if (status)
    return status;
  double *mem = calloc((size_t)15 * n + 2 * w.k, sizeof(double));
  if (!mem) {
    cn_sc_free(&w);
    return CN_MEMORY;
  }
  double *x = mem, *g = x + n, *xn = g + n, *gn = xn + n, *d = gn + n,
         *s = d + n, *y = s + n, *Bs = y + n, *step = Bs + n, *gp = step + n,
         *lswork = gp + n, *a = lswork + 4 * n;
  double f, fn, zeta = 1, zc = 1, delta = 0;
  long nrej = 0, nskip = 0, iteration = 0;
  const char *reason = NULL;
  if (O->fg(O->context, x0, &f, g)) {
    status = CN_CALLBACK;
    goto done;
  }
  memcpy(x, x0, (size_t)n * sizeof(double));
  double ng = cn_norm(b, n, g);
  if (!(ng > 0) || !isfinite(ng)) {
    reason = "zero_or_nonfinite_gradient";
    goto done;
  }
  for (int i = 0; i < n; i++)
    d[i] = -g[i];
  CNLineParams lp = {1e-4, .9, 1e-6, 0, 5, 3000, 1};
  int ls = cn_more_thuente(b, O, x, f, g, d, 1, &lp, xn, &fn, gn, lswork);
  if (ls < 0) {
    status = ls;
    goto done;
  }
  if (!ls) {
    reason = "initial_line_search_failed";
    goto done;
  }
  for (int i = 0; i < n; i++) {
    s[i] = xn[i] - x[i];
    y[i] = gn[i] - g[i];
  }
  /* Author Init.2 begins with gamma=1 in its q-history. The first
     initialized gamma is itself stored; later trials store their raw yy/sy. */
  w.history[0] = 1;
  w.hcount = 1;
  w.hnext = 1 % q;
  double sy0 = cn_dot(b, n, s, y),
         bb0 = sy0 != 0 ? cn_dot(b, n, y, y) / sy0 : NAN;
  zeta = isfinite(bb0) ? fmax(1, bb0) : 1;
  w.history[w.hnext] = zeta;
  w.hnext = (w.hnext + 1) % q;
  if (w.hcount < q)
    w.hcount++;
  if (variant) {
    zeta = sc_gamma(&w, zeta);
    for (int i = 0; i < n; i++)
      Bs[i] = zeta * s[i];
    nskip += !sc_sr1_remember(&w, b, s, y, Bs, skip_tol);
  } else
    nskip += !sc_mss_remember(&w, b, s, y, rank_tol);
  delta = 2 * cn_norm(b, n, s);
  memcpy(x, xn, (size_t)n * sizeof(double));
  memcpy(g, gn, (size_t)n * sizeof(double));
  f = fn;
  if (O->mark(O->context)) {
    status = CN_CALLBACK;
    goto done;
  }
  iteration++;
  while (1) {
    if (variant || !dense)
      zc = zeta;
    status = cn_sc_model(&w, b, variant, zeta, zc, rank_tol);
    if (status) {
      reason = "numerical_model_failure";
      status = CN_OK;
      goto done;
    }
    double pBp;
    status =
        cn_sc_shape(b, n, w.rank, w.P, w.eval, zc, g, delta, step, &pBp, a, gp);
    if (status) {
      reason = "numerical_model_failure";
      status = CN_OK;
      goto done;
    }
    double pred = -(cn_dot(b, n, g, step) + .5 * pBp);
    int changed = 0;
    for (int i = 0; i < n; i++) {
      xn[i] = x[i] + step[i];
      if (xn[i] != x[i])
        changed = 1;
    }
    if (!changed) {
      reason = "unrepresentable_step";
      goto done;
    }
    if (O->fg(O->context, xn, &fn, gn)) {
      status = CN_CALLBACK;
      goto done;
    }
    int finite = isfinite(fn) && cn_finite(n, gn);
    double ratio = finite && pred > 0 ? (f - fn) / pred : -INFINITY;
    int accepted = ratio > 9e-4;
    if (O->trace) {
      CNParam items[] = {{"iteration", iteration}, {"radius", delta},
                         {"ratio", ratio},         {"predicted_decrease", pred},
                         {"accepted", accepted},   {"window", w.p},
                         {"rank", w.rank},         {"gamma", zeta},
                         {"gamma_perp", zc}};
      CNTrace t = {"sc_trial", items, 9, xn, gn, NULL, NULL};
      if (O->trace(O->context, &t)) {
        status = CN_CALLBACK;
        goto done;
      }
    }
    if (finite) {
      for (int i = 0; i < n; i++)
        y[i] = gn[i] - g[i];
      double sy = cn_dot(b, n, step, y),
             bb = sy != 0 ? cn_dot(b, n, y, y) / sy : NAN;
      double oldmax = sc_gamma(&w, zeta);
      zeta = isfinite(bb) ? fmax(oldmax, bb) : oldmax;
      if (!variant && dense && sy > 0 && isfinite(bb))
        zc = bb;
      if (variant) {
        for (int i = 0; i < n; i++)
          Bs[i] = zeta * step[i];
        nskip += !sc_sr1_remember(&w, b, step, y, Bs, skip_tol);
      } else
        nskip += !sc_mss_remember(&w, b, step, y, rank_tol);
      sc_history(&w, b, step, y);
    }
    if (accepted) {
      memcpy(x, xn, (size_t)n * sizeof(double));
      memcpy(g, gn, (size_t)n * sizeof(double));
      f = fn;
      if (O->mark(O->context)) {
        status = CN_CALLBACK;
        goto done;
      }
      iteration++;
    } else
      nrej++;
    if (ratio > .75) {
      if (cn_norm(b, n, step) > .8 * delta)
        delta *= 2;
    } else if (ratio < .1)
      delta *= .5;
    if (delta < 100 * DBL_EPSILON * fmax(1, cn_norm(b, n, x))) {
      reason = "trust_region_radius_collapsed";
      goto done;
    }
  }
done:
  if (O->note(O->context, "nrej", (double)nrej) ||
      O->note(O->context, "nskip", (double)nskip))
    status = CN_CALLBACK;
  if (reason && status != CN_CALLBACK && O->stop(O->context, reason))
    status = CN_CALLBACK;
  free(mem);
  cn_sc_free(&w);
  return status;
}

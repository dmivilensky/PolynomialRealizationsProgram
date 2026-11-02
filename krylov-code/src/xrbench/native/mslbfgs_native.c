/* F. V. Gubarev, A Multi-Secant Limited-Memory BFGS Method (2026),
   https://optimization-online.org/wp-content/uploads/2026/03/ms-lbfgs.pdf.
   Uniform polar variant: (9), window selection (18)-(19), symmetric damping
   (20)-(21), retained whole block updates (Fig. 1), scalar scale (Sec. 4.4).
   Square-root compact representation implements (44) without formed inverse
   Gram matrices. No eigenvalue clipping, ridge, or rank truncation is used. */
#include "mslbfgs_native.h"
#include <float.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>
#define AT(a, i, j, ld) ((a)[(i) + (size_t)(j) * (ld)])
typedef struct {
    int n, m, M, p, first, next, nu, rows, r, window, damped;
    double es, ey, gamma;
    const CNBackend *b;
    double *S, *Y, *A, *F, *Q, *R, *SY, *Sc, *Yc, *HY, *BS;
    double *O, *sbs, *yhy, *U, *VT, *sig, *root, *small, *small2, *small3, *svda;
    double *temp, *temp2, *Ftmp, *qwork, *features, *tau, *work, *vec, *vec2;
    int *lo, *size, *piv;
    double *roots;
    int lw;
} MS;
static void mm(MS *s, char ta, char tb, int a, int b, int c, double alpha, const double *A, int la,
               const double *B, int lb, double beta, double *C, int lc) {
    s->b->blas.dgemm(&ta, &tb, &a, &b, &c, &alpha, (double *)A, &la, (double *)B, &lb, &beta, C,
                     &lc);
}
static double dot(MS *s, const double *a, const double *b) { return cn_dot(s->b, s->n, a, b); }
static int qr(MS *s, double *a, int nr, int nc, int ld, int form) {
    int info, k = nr < nc ? nr : nc;
    s->b->dgeqrf(&nr, &nc, a, &ld, s->tau, s->work, &s->lw, &info);
    if (!info && form)
        s->b->dorgqr(&nr, &k, &k, a, &ld, s->tau, s->work, &s->lw, &info);
    return info == 0;
}
static int svd(MS *s, const double *o, int q, int ld) {
    for (int j = 0; j < q; j++)
        for (int i = 0; i < q; i++)
            AT(s->svda, i, j, q) = AT(o, i, j, ld);
    char job = 'A';
    int info;
    s->b->dgesvd(&job, &job, &q, &q, s->svda, &q, s->sig, s->U, &q, s->VT, &q, s->work, &s->lw,
                 &info);
    return info == 0 && cn_finite(q, s->sig) && s->sig[q - 1] > 0;
}
/* Exact quadratic roots along one ray in the damping box. */
static void cons(double p, double q, double c, double es, double ey, double a, double b,
                 double *g) {
    double cc = c * ((1 - a) * (1 - b) + a * b) + (1 - a) * b * p + a * (1 - b) * q;
    double pp = (1 - a) * (1 - a) * p + 2 * a * (1 - a) * c + a * a * q;
    double qq = (1 - b) * (1 - b) * q + 2 * b * (1 - b) * c + b * b * p;
    g[0] = cc - es * pp;
    g[1] = cc - ey * qq;
}
static double ray(double p, double q, double c, double es, double ey, double ph) {
    double u = cos(ph), v = sin(ph), rm = .5 / fmax(u, v), f0[2], fh[2], f1[2], cand[5];
    int nc = 1;
    cons(p, q, c, es, ey, 0, 0, f0);
    cons(p, q, c, es, ey, .5 * rm * u, .5 * rm * v, fh);
    cons(p, q, c, es, ey, rm * u, rm * v, f1);
    cand[0] = rm;
    for (int j = 0; j < 2; j++) {
        double A = 2 * (f1[j] - 2 * fh[j] + f0[j]) / (rm * rm), B = (f1[j] - f0[j]) / rm - A * rm,
               C = f0[j];
        if (fabs(A) <= DBL_EPSILON * fmax(fabs(B), fabs(C))) {
            if (B != 0) {
                double z = -C / B;
                if (z > 0 && z <= rm)
                    cand[nc++] = z;
            }
        } else {
            double D = B * B - 4 * A * C;
            if (D >= 0) {
                double z = -.5 * (B + copysign(sqrt(D), B));
                double roots[2] = {z / A, z != 0 ? C / z : 0};
                for (int k = 0; k < 2; k++)
                    if (roots[k] > 0 && roots[k] <= rm)
                        cand[nc++] = roots[k];
            }
        }
    }
    double best = INFINITY, tol = 1e-13 * (fabs(c) + p + q);
    for (int k = 0; k < nc; k++) {
        double g[2];
        cons(p, q, c, es, ey, cand[k] * u, cand[k] * v, g);
        if (g[0] >= -tol && g[1] >= -tol && cand[k] < best)
            best = cand[k];
    }
    return best;
}
int cn_ms_damping(double p, double q, double c, double es, double ey, double *a, double *b) {
    double sc = fmax(fmax(p, q), fabs(c));
    if (!isfinite(sc) || sc <= 0)
        return 0;
    p /= sc;
    q /= sc;
    c /= sc;
    double g[2];
    cons(p, q, c, es, ey, 0, 0, g);
    if (fmin(g[0], g[1]) >= -1e-13 * (fabs(c) + p + q)) {
        *a = *b = 0;
        return 1;
    }
    const double pi = 3.14159265358979323846, gr = .6180339887498948482;
    double bp = 0, br = INFINITY;
    int bi = 0;
    for (int i = 0; i <= 90; i++) {
        double ph = .5 * pi * i / 90, z = ray(p, q, c, es, ey, ph);
        if (z < br) {
            bp = ph;
            br = z;
            bi = i;
        }
    }
    if (!isfinite(br))
        return 0;
    double l = .5 * pi * (bi > 0 ? bi - 1 : 0) / 90, h = .5 * pi * (bi < 90 ? bi + 1 : 90) / 90;
    double x1 = h - gr * (h - l), x2 = l + gr * (h - l), f1 = ray(p, q, c, es, ey, x1),
           f2 = ray(p, q, c, es, ey, x2);
    for (int i = 0; i < 40; i++) {
        if (f1 < br) {
            br = f1;
            bp = x1;
        }
        if (f2 < br) {
            br = f2;
            bp = x2;
        }
        if (f1 <= f2) {
            h = x2;
            x2 = x1;
            f2 = f1;
            x1 = h - gr * (h - l);
            f1 = ray(p, q, c, es, ey, x1);
        } else {
            l = x1;
            x1 = x2;
            f1 = f2;
            x2 = l + gr * (h - l);
            f2 = ray(p, q, c, es, ey, x2);
        }
    }
    *a = fmin(.5, fmax(0, br * cos(bp)));
    *b = fmin(.5, fmax(0, br * sin(bp)));
    return 1;
}
void cn_ms_destroy(void *v) {
    MS *s = v;
    if (!s)
        return;
    free(s->S);
    free(s->Y);
    free(s->A);
    free(s->F);
    free(s->Q);
    free(s->R);
    free(s->SY);
    free(s->Sc);
    free(s->Yc);
    free(s->HY);
    free(s->BS);
    free(s->O);
    free(s->sbs);
    free(s->yhy);
    free(s->U);
    free(s->VT);
    free(s->sig);
    free(s->root);
    free(s->small);
    free(s->small2);
    free(s->small3);
    free(s->svda);
    free(s->temp);
    free(s->temp2);
    free(s->Ftmp);
    free(s->qwork);
    free(s->features);
    free(s->tau);
    free(s->work);
    free(s->vec);
    free(s->vec2);
    free(s->lo);
    free(s->size);
    free(s->piv);
    free(s->roots);
    free(s);
}
void *cn_ms_create(int n, int m, int M, double es, double ey, const CNBackend *b) {
    if (n < 1 || m < 1 || M < 0 || M > m || es <= 0 || es >= .5 || ey <= 0 || ey >= .5)
        return NULL;
    MS *s = calloc(1, sizeof(*s));
    if (!s)
        return NULL;
    s->n = n;
    s->m = m;
    s->M = M;
    s->es = es;
    s->ey = ey;
    s->b = b;
    s->gamma = 1;
    int d = m + 1, t = 2 * m, r = n < t ? n : t, fr = m * m, fl = n + fr;
    s->lw = 128 * (fr + t + 16);
#define ALLOC(name, count, type)                                                                   \
    s->name = calloc((size_t)(count), sizeof(type));                                               \
    if (!s->name) {                                                                                \
        cn_ms_destroy(s);                                                                          \
        return NULL;                                                                               \
    }
    ALLOC(S, (size_t)n * d, double);
    ALLOC(Y, (size_t)n * d, double);
    ALLOC(A, d * d, double);
    ALLOC(F, fr * d, double);
    ALLOC(Q, (size_t)n * r, double);
    ALLOC(R, r * r, double);
    ALLOC(SY, d * d, double);
    ALLOC(Sc, (size_t)n * d, double);
    ALLOC(Yc, (size_t)n * d, double);
    ALLOC(HY, (size_t)n * d, double);
    ALLOC(BS, (size_t)n * d, double);
    ALLOC(O, d * d, double);
    ALLOC(sbs, d * d, double);
    ALLOC(yhy, d * d, double);
    ALLOC(U, d * d, double);
    ALLOC(VT, d * d, double);
    ALLOC(sig, d, double);
    ALLOC(root, d * d, double);
    ALLOC(small, d * d, double);
    ALLOC(small2, d * d, double);
    ALLOC(small3, d * d, double);
    ALLOC(svda, d * d, double);
    ALLOC(temp, d * (r > d ? r : d), double);
    ALLOC(temp2, (size_t)n * r, double);
    ALLOC(Ftmp, fr * d, double);
    ALLOC(qwork, (size_t)n * t, double);
    ALLOC(features, (size_t)(fl + t) * t, double);
    ALLOC(tau, t, double);
    ALLOC(work, s->lw, double);
    ALLOC(vec, n, double);
    ALLOC(vec2, n, double);
    ALLOC(lo, d, int);
    ALLOC(size, d, int);
    ALLOC(piv, d, int);
    ALLOC(roots, d * d * d, double);
#undef ALLOC
    return s;
}
/* H products use the factored positive compact form (44). */
static void hprod(MS *s, const double *v, double *out) {
    int n = s->n, p = s->p, d = s->m + 1, fr = s->m * s->m;
    if (!s->nu) {
        for (int i = 0; i < n; i++)
            out[i] = s->gamma * v[i];
        return;
    }
    for (int j = 0; j < p; j++)
        s->small[j] = dot(s, s->S + (size_t)j * n, v);
    mm(s, 'N', 'N', p, 1, p, 1, s->A, d, s->small, p, 0, s->small2, p);
    memcpy(s->vec, v, n * sizeof(double));
    mm(s, 'N', 'N', n, 1, p, -1, s->Y, n, s->small2, p, 1, s->vec, n);
    for (int j = 0; j < p; j++)
        s->small2[j] = dot(s, s->Y + (size_t)j * n, s->vec);
    mm(s, 'T', 'N', p, 1, p, 1, s->A, d, s->small2, p, 0, s->small3, p);
    for (int i = 0; i < n; i++)
        out[i] = s->gamma * s->vec[i];
    mm(s, 'N', 'N', n, 1, p, -s->gamma, s->S, n, s->small3, p, 1, out, n);
    mm(s, 'N', 'N', s->rows, 1, p, 1, s->F, fr, s->small, p, 0, s->Ftmp, fr);
    mm(s, 'T', 'N', p, 1, s->rows, 1, s->F, fr, s->Ftmp, fr, 0, s->small2, p);
    mm(s, 'N', 'N', n, 1, p, 1, s->S, n, s->small2, p, 1, out, n);
}
static int bprod(MS *s, const double *v, double *out) {
    int n = s->n, r = s->r;
    if (!s->nu) {
        for (int i = 0; i < n; i++)
            out[i] = v[i] / s->gamma;
        return 1;
    }
    for (int j = 0; j < r; j++)
        s->temp[j] = dot(s, s->Q + (size_t)j * n, v);
    memcpy(s->temp + r, s->temp, r * sizeof(double));
    char side = 'L', up = 'U', tr = 'T', di = 'N';
    int one = 1;
    double alpha = 1;
    s->b->blas.dtrsm(&side, &up, &tr, &di, &r, &one, &alpha, s->R, &r, s->temp + r, &r);
    tr = 'N';
    s->b->blas.dtrsm(&side, &up, &tr, &di, &r, &one, &alpha, s->R, &r, s->temp + r, &r);
    for (int i = 0; i < n; i++)
        out[i] = v[i] / s->gamma;
    for (int j = 0; j < r; j++)
        s->temp[j] = s->temp[r + j] - s->temp[j] / s->gamma;
    mm(s, 'N', 'N', n, 1, r, 1, s->Q, n, s->temp, r, 1, out, n);
    return cn_finite(n, out);
}
int cn_ms_product(void *v, const double *x, double *out, int inverse) {
    MS *s = v;
    if (inverse) {
        hprod(s, x, out);
        return cn_finite(s->n, out);
    }
    return bprod(s, x, out);
}
static int rebuild(MS *s) {
    int p = s->p, n = s->n, d = s->m + 1, fr = s->m * s->m;
    mm(s, 'T', 'N', p, p, n, 1, s->S, n, s->Y, n, 0, s->SY, d);
    memset(s->A, 0, d * d * sizeof(double));
    memset(s->F, 0, fr * d * sizeof(double));
    s->rows = 0;
    for (int z = 0; z < s->nu; z++) {
        int q = s->size[z], st = s->lo[z] - s->first, info;
        for (int j = 0; j < q; j++)
            for (int i = 0; i < q; i++)
                AT(s->small, i, j, q) = AT(s->SY, st + i, st + j, d);
        memset(s->small2, 0, d * d * sizeof(double));
        for (int j = 0; j < q; j++)
            AT(s->small2, j, j, q) = 1;
        s->b->blas.dgesv(&q, &q, s->small, &q, s->piv, s->small2, &q, &info);
        if (info)
            return 0;
        mm(s, 'N', 'N', p, q, p, -1, s->A, d, s->SY + (size_t)st * d, d, 0, s->temp, p);
        for (int j = 0; j < q; j++)
            AT(s->temp, st + j, j, p) += 1;
        mm(s, 'N', 'N', p, q, q, 1, s->temp, p, s->small2, q, 0, s->small3, d);
        for (int j = 0; j < q; j++)
            for (int i = 0; i < p; i++)
                AT(s->A, i, st + j, d) += AT(s->small3, i, j, d);
        /* F <- F(I-SY[:,w] O_w^-1 E_w^T), then append the kernel root. */
        if (s->rows) {
            mm(s, 'N', 'N', s->rows, q, p, 1, s->F, fr, s->SY + (size_t)st * d, d, 0, s->Ftmp, fr);
            mm(s, 'N', 'N', s->rows, q, q, 1, s->Ftmp, fr, s->small2, q, 0, s->features, fr);
            for (int j = 0; j < q; j++)
                for (int i = 0; i < s->rows; i++)
                    AT(s->F, i, st + j, fr) -= AT(s->features, i, j, fr);
        }
        double *rt = s->roots + (size_t)z * d * d;
        for (int j = 0; j < q; j++)
            for (int i = 0; i < q; i++)
                AT(s->F, s->rows + i, st + j, fr) = AT(rt, i, j, d);
        s->rows += q;
    }
    if (!cn_finite(d * d, s->A))
        return 0;
    /* Thin QR of individually scaled [S,Y], retaining all QR columns. */
    int nc = 2 * p, r = n < nc ? n : nc;
    for (int j = 0; j < nc; j++) {
        double *v = (j < p ? s->S : s->Y) + (size_t)(j % p) * n, scale = 0;
        for (int i = 0; i < n; i++)
            scale = fmax(scale, fabs(v[i]));
        if (!isfinite(scale) || scale == 0)
            return 0;
        for (int i = 0; i < n; i++)
            AT(s->qwork, i, j, n) = v[i] / scale;
    }
    if (!qr(s, s->qwork, n, nc, n, 1))
        return 0;
    memcpy(s->Q, s->qwork, (size_t)n * r * sizeof(double));
    s->r = r;
    /* QR of [sqrt(gamma) Qop*basis; F S^T basis], factor H|span(S,Y). */
    mm(s, 'T', 'N', p, r, n, 1, s->S, n, s->Q, n, 0, s->temp, p);
    mm(s, 'N', 'N', p, r, p, 1, s->A, d, s->temp, p, 0, s->qwork, p);
    memcpy(s->temp2, s->Q, (size_t)n * r * sizeof(double));
    mm(s, 'N', 'N', n, r, p, -1, s->Y, n, s->qwork, p, 1, s->temp2, n);
    int ld = n + s->rows;
    for (int j = 0; j < r; j++)
        for (int i = 0; i < n; i++)
            AT(s->features, i, j, ld) = sqrt(s->gamma) * AT(s->temp2, i, j, n);
    mm(s, 'N', 'N', s->rows, r, p, 1, s->F, fr, s->temp, p, 0, s->features + n, ld);
    if (!cn_finite(ld * r, s->features) || !qr(s, s->features, ld, r, ld, 0))
        return 0;
    for (int j = 0; j < r; j++)
        for (int i = 0; i < r; i++)
            AT(s->R, i, j, r) = i <= j ? AT(s->features, i, j, ld) : 0;
    for (int i = 0; i < r; i++)
        if (AT(s->R, i, i, r) == 0 || !isfinite(AT(s->R, i, i, r)))
            return 0;
    return 1;
}
static void grams(MS *s, int q) {
    int n = s->n, d = s->m + 1;
    mm(s, 'T', 'N', q, q, n, 1, s->Sc, n, s->Yc, n, 0, s->O, d);
    /* Factor-based positive Gram forms avoid cancellation of B/H products. */
    if (!s->nu) {
        mm(s, 'T', 'N', q, q, n, 1, s->Sc, n, s->BS, n, 0, s->sbs, d);
        mm(s, 'T', 'N', q, q, n, 1, s->Yc, n, s->HY, n, 0, s->yhy, d);
        return;
    }
    for (int j = 0; j < q; j++) {
        int r = s->r, p = s->p, fr = s->m * s->m;
        double *v = s->Sc + (size_t)j * n;
        for (int k = 0; k < r; k++)
            AT(s->qwork, k, j, r) = dot(s, s->Q + (size_t)k * n, v);
        memcpy(s->temp, s->qwork + (size_t)j * r, r * sizeof(double));
        char side = 'L', up = 'U', tr = 'T', di = 'N';
        int one = 1;
        double alpha = 1;
        s->b->blas.dtrsm(&side, &up, &tr, &di, &r, &one, &alpha, s->R, &r, s->temp, &r);
        for (int i = 0; i < n; i++)
            s->vec[i] = v[i];
        mm(s, 'N', 'N', n, 1, r, -1, s->Q, n, s->qwork + (size_t)j * r, r, 1, s->vec, n);
        /* Save explicit features for all candidates, no subtractive Gram formula. */
        for (int i = 0; i < n; i++)
            AT(s->features, i, j, n + r) = s->vec[i] / sqrt(s->gamma);
        for (int i = 0; i < r; i++)
            AT(s->features, n + i, j, n + r) = s->temp[i];
        (void)p;
        (void)fr;
    }
    mm(s, 'T', 'N', q, q, n + s->r, 1, s->features, n + s->r, s->features, n + s->r, 0, s->sbs, d);
    for (int j = 0; j < q; j++) {
        double *v = s->Yc + (size_t)j * n;
        int p = s->p, fr = s->m * s->m;
        for (int k = 0; k < p; k++)
            s->small[k] = dot(s, s->S + (size_t)k * n, v);
        mm(s, 'N', 'N', p, 1, p, 1, s->A, d, s->small, p, 0, s->small2, p);
        memcpy(s->vec, v, n * sizeof(double));
        mm(s, 'N', 'N', n, 1, p, -1, s->Y, n, s->small2, p, 1, s->vec, n);
        for (int i = 0; i < n; i++)
            AT(s->features, i, j, n + s->rows) = sqrt(s->gamma) * s->vec[i];
        mm(s, 'N', 'N', s->rows, 1, p, 1, s->F, fr, s->small, p, 0,
           s->features + n + (size_t)j * (n + s->rows), s->rows);
    }
    mm(s, 'T', 'N', q, q, n + s->rows, 1, s->features, n + s->rows, s->features, n + s->rows, 0,
       s->yhy, d);
}
static int select_window(MS *s, int qmax, int bound) {
    int d = s->m + 1;
    for (int q = bound < qmax ? bound : qmax; q >= 1; q--) {
        int st = qmax - q;
        if (!svd(s, s->O + st + (size_t)st * d, q, d))
            continue;
        double ld = 0, ti = 0, trace = 0;
        for (int j = 0; j < q; j++) {
            ld += log(s->sig[j]);
            ti += 1 / s->sig[j];
            trace += AT(s->yhy, st + j, st + j, d);
        }
        for (int j = 0; j < q; j++)
            for (int i = 0; i < q; i++)
                AT(s->small, i, j, q) =
                    .5 * (AT(s->sbs, st + i, st + j, d) + AT(s->sbs, st + j, st + i, d));
        char up = 'L';
        int info;
        s->b->blas.dpotrf(&up, &q, s->small, &q, &info);
        if (info)
            continue;
        double ls = 0;
        for (int j = 0; j < q; j++)
            ls += 2 * log(AT(s->small, j, j, q));
        if (ld >= log(s->es) + ls && 1 / ti >= s->ey * trace)
            return q;
    }
    return 0;
}
int cn_ms_update(void *v, const double *sn, const double *yn) {
    MS *s = v;
    int n = s->n, d = s->m + 1, qmax = s->p + 1;
    if (qmax > (s->M > 0 ? s->M : 1))
        qmax = s->M > 0 ? s->M : 1;
    int old = qmax - 1;
    for (int j = 0; j < old; j++) {
        memcpy(s->Sc + (size_t)j * n, s->S + (size_t)(s->p - old + j) * n, n * sizeof(double));
        memcpy(s->Yc + (size_t)j * n, s->Y + (size_t)(s->p - old + j) * n, n * sizeof(double));
    }
    memcpy(s->Sc + (size_t)old * n, sn, n * sizeof(double));
    memcpy(s->Yc + (size_t)old * n, yn, n * sizeof(double));
    double gam = s->gamma;
    if (!s->nu) {
        double yy = dot(s, yn, yn), sy = fabs(dot(s, sn, yn));
        if (yy > 0 && sy > 0)
            gam = sy / yy;
    }
    for (int j = 0; j < qmax; j++) {
        if (!s->nu) {
            for (int i = 0; i < n; i++) {
                AT(s->HY, i, j, n) = gam * AT(s->Yc, i, j, n);
                AT(s->BS, i, j, n) = AT(s->Sc, i, j, n) / gam;
            }
        } else {
            hprod(s, s->Yc + (size_t)j * n, s->HY + (size_t)j * n);
            if (!bprod(s, s->Sc + (size_t)j * n, s->BS + (size_t)j * n))
                return CN_NUMERICAL;
        }
    }
    grams(s, qmax);
    int q = select_window(s, qmax, qmax), need = (q == 0);
    if (s->M == 0) {
        double c = AT(s->O, old, old, d);
        need =
            !(c > 0 && c >= fmax(s->es * AT(s->sbs, old, old, d), s->ey * AT(s->yhy, old, old, d)));
        q = 1;
    }
    if (need) {
        double c = AT(s->O, old, old, d), sign = s->M == 0 || c >= 0 ? 1 : -1, a, b;
        if (!cn_ms_damping(AT(s->sbs, old, old, d), AT(s->yhy, old, old, d), sign * c, s->es, s->ey,
                           &a, &b))
            return 0;
        if (a != 0 || b != 0) {
            for (int i = 0; i < n; i++) {
                double so = AT(s->Sc, i, old, n), yo = AT(s->Yc, i, old, n),
                       hy = AT(s->HY, i, old, n), bs = AT(s->BS, i, old, n);
                AT(s->Sc, i, old, n) = (1 - a) * so + sign * a * hy;
                AT(s->Yc, i, old, n) = (1 - b) * yo + sign * b * bs;
                AT(s->HY, i, old, n) = (1 - b) * hy + sign * b * so;
                AT(s->BS, i, old, n) = (1 - a) * bs + sign * a * yo;
            }
            s->damped++;
            grams(s, qmax);
        }
        q = 1;
    }
    int st = qmax - q;
    if (!svd(s, s->O + st + (size_t)st * d, q, d))
        return 0;
    double trace = 0, yy = 0;
    for (int j = 0; j < q; j++) {
        trace += s->sig[j];
        yy += dot(s, s->Yc + (size_t)(st + j) * n, s->Yc + (size_t)(st + j) * n);
    }
    gam = trace / yy;
    if (!isfinite(gam) || gam <= 0)
        return 0;
    /* Root diag(sig^-1/2) U^T has root^T root=K_R^-1 directly. */
    for (int j = 0; j < q; j++)
        for (int i = 0; i < q; i++)
            AT(s->root, i, j, d) = AT(s->U, j, i, q) / sqrt(s->sig[i]);
    memcpy(s->S + (size_t)s->p * n, s->Sc + (size_t)old * n, n * sizeof(double));
    memcpy(s->Y + (size_t)s->p * n, s->Yc + (size_t)old * n, n * sizeof(double));
    s->p++;
    int id = s->next++;
    s->lo[s->nu] = id - q + 1;
    s->size[s->nu] = q;
    memcpy(s->roots + (size_t)s->nu * d * d, s->root, d * d * sizeof(double));
    s->nu++;
    if (s->p > s->m) {
        memmove(s->S, s->S + n, (size_t)(s->p - 1) * n * sizeof(double));
        memmove(s->Y, s->Y + n, (size_t)(s->p - 1) * n * sizeof(double));
        s->p--;
        s->first++;
    }
    int keep = s->nu;
    while (keep > 0 && s->lo[keep - 1] >= s->first)
        keep--; /* longest valid suffix */
    if (keep) {
        s->nu -= keep;
        memmove(s->lo, s->lo + keep, s->nu * sizeof(int));
        memmove(s->size, s->size + keep, s->nu * sizeof(int));
        memmove(s->roots, s->roots + (size_t)keep * d * d, (size_t)s->nu * d * d * sizeof(double));
    }
    s->gamma = gam;
    s->window = q;
    if (!rebuild(s))
        return CN_NUMERICAL;
    return 1;
}
int cn_ms_snapshot(void *v, double *S, double *Y, int *meta, double *scale) {
    MS *s = v;
    if (S)
        memcpy(S, s->S, (size_t)s->n * s->p * sizeof(double));
    if (Y)
        memcpy(Y, s->Y, (size_t)s->n * s->p * sizeof(double));
    if (meta) {
        meta[0] = s->p;
        meta[1] = s->nu;
        meta[2] = s->window;
        meta[3] = s->damped;
    }
    if (scale)
        *scale = s->gamma;
    return s->p;
}
/* Section 5: Goldstein on initial/reset steepest descent, Armijo otherwise. */
static int search(MS *s, const CNOracle *o, const double *x, double f, const double *g,
                  const double *dir, int gold, double c1, double cg, double *xn, double *fn) {
    int n = s->n;
    double slope = dot(s, g, dir);
    if (!isfinite(slope) || slope >= 0)
        return 0;
    double alpha = gold ? 1 / cn_norm(s->b, n, g) : 1, lo = 0, hi = INFINITY, best = INFINITY,
           besta = 0;
    for (int it = 0; it < 100; it++) {
        int same = 1;
        for (int i = 0; i < n; i++) {
            xn[i] = x[i] + alpha * dir[i];
            if (xn[i] != x[i])
                same = 0;
        }
        if (same)
            break;
        if (o->f(o->context, xn, fn))
            return CN_CALLBACK;
        if (!isfinite(*fn)) {
            hi = alpha;
            alpha = gold && lo > 0 ? .5 * (lo + hi) : .1 * alpha;
            continue;
        }
        double arm = gold ? cg : c1;
        if (*fn > f + arm * alpha * slope) {
            hi = alpha;
            if (gold && lo > 0)
                alpha = .5 * (lo + hi);
            else {
                double den = 2 * (*fn - f - alpha * slope),
                       a = den > 0 ? -slope * alpha * alpha / den : .5 * alpha;
                alpha = fmin(fmax(a, .1 * alpha), .5 * alpha);
            }
            continue;
        }
        if (gold && *fn < f + (1 - cg) * alpha * slope) {
            lo = alpha;
            if (*fn < best) {
                best = *fn;
                besta = alpha;
            }
            if (isfinite(hi))
                alpha = .5 * (lo + hi);
            else {
                double den = 2 * (*fn - f - alpha * slope),
                       a = den > 0 ? -slope * alpha * alpha / den : 10 * alpha;
                alpha = fmin(fmax(a, 2 * alpha), 10 * alpha);
            }
            continue;
        }
        return 1;
    }
    if (gold && besta > 0) {
        for (int i = 0; i < n; i++)
            xn[i] = x[i] + besta * dir[i];
        *fn = best;
        return 1;
    }
    return 0;
}
int cn_ms_execute(const CNParams *p, const CNBackend *b, const CNOracle *o, const double *x0) {
    int n = o->n, m = cn_int(p, "m", 8), M = cn_int(p, "M", 8);
    /* Production comparisons use only the published uniform M >= 1 family.
       The M=0 positive-pair helper is retained solely for algebra diagnostics. */
    if (M < 1 || cn_int(p, "exact_last", 0))
        return CN_INVALID;
    MS *s = cn_ms_create(n, m, M, cn_get(p, "eps_s", .01), cn_get(p, "eps_y", .001), b);
    if (!s)
        return CN_MEMORY;
    double *all = calloc((size_t)n * 7, sizeof(double));
    if (!all) {
        cn_ms_destroy(s);
        return CN_MEMORY;
    }
    double *x = all, *g = x + n, *xn = g + n, *gn = xn + n, *dir = gn + n, *step = dir + n,
           *image = step + n, f, fn;
    int rc = CN_OK, k = 0;
    memcpy(x, x0, n * sizeof(double));
    if (o->fg(o->context, x, &f, g)) {
        rc = CN_CALLBACK;
        goto done;
    }
    for (;;) {
        if (!s->nu) {
            double norm = cn_norm(b, n, g);
            if (!isfinite(norm) || norm <= 0) {
                if (o->stop(o->context, norm == 0 ? "zero_gradient" : "nonfinite"))
                    rc = CN_CALLBACK;
                break;
            }
            for (int i = 0; i < n; i++)
                dir[i] = -g[i];
        } else {
            hprod(s, g, dir);
            for (int i = 0; i < n; i++)
                dir[i] = -dir[i];
        }
        int ok = search(s, o, x, f, g, dir, !s->nu, cn_get(p, "c1", 1e-4), cn_get(p, "c_gold", .25),
                        xn, &fn);
        if (ok < 0) {
            rc = ok;
            break;
        }
        if (!ok) {
            if (!s->nu) {
                if (o->stop(o->context, "line_search_failed_after_reset"))
                    rc = CN_CALLBACK;
                break;
            }
            s->p = s->first = s->next = s->nu = s->rows = s->r = 0;
            s->gamma = 1;
            continue;
        }
        if (o->g(o->context, xn, gn) || o->mark(o->context)) {
            rc = CN_CALLBACK;
            break;
        }
        for (int i = 0; i < n; i++) {
            step[i] = xn[i] - x[i];
            image[i] = gn[i] - g[i];
        }
        int updated = cn_ms_update(s, step, image);
        if (updated < 0) {
            if (o->stop(o->context, "numerical_failure"))
                rc = CN_CALLBACK;
            break;
        }
        memcpy(x, xn, n * sizeof(double));
        memcpy(g, gn, n * sizeof(double));
        f = fn;
        k++;
        if (o->trace) {
            CNParam items[] = {{"iteration", k},
                               {"window", s->window},
                               {"gamma", s->gamma},
                               {"damped", s->damped},
                               {"updated", updated}};
            CNTrace tr = {"accepted", items, 5, x, g, NULL, NULL};
            if (o->trace(o->context, &tr)) {
                rc = CN_CALLBACK;
                break;
            }
        }
    }
    if (o->note) {
        if (o->note(o->context, "ms_damped", s->damped) ||
            o->note(o->context, "ms_last_window", s->window))
            rc = CN_CALLBACK;
    }
done:
    free(all);
    cn_ms_destroy(s);
    return rc;
}

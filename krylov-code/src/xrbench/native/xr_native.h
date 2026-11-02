#ifndef XRBENCH_XR_NATIVE_H
#define XRBENCH_XR_NATIVE_H

#include <stddef.h>

/* Native execution uses exactly the observed XR data. BLAS/LAPACK functions
   are injected from SciPy's published Cython capsules, avoiding vendor ABI or
   integer-width assumptions. All exposed dense matrices are column-major. */
typedef struct { double real, imag; } XRComplex;

typedef struct {
    double (*ddot)(int *, double *, int *, double *, int *);
    double (*dnrm2)(int *, double *, int *);
    void (*dgemv)(char *, int *, int *, double *, double *, int *, double *, int *, double *, double *, int *);
    void (*dgemm)(char *, char *, int *, int *, int *, double *, double *, int *, double *, int *, double *, double *, int *);
    void (*dpotrf)(char *, int *, double *, int *, int *);
    void (*dpotrs)(char *, int *, int *, double *, int *, double *, int *, int *);
    void (*dgesv)(int *, int *, double *, int *, int *, double *, int *, int *);
    void (*dtrcon)(char *, char *, char *, int *, double *, int *, double *, double *, int *, int *);
    void (*dsyev)(char *, char *, int *, double *, int *, double *, double *, int *, int *);
    void (*dtrsm)(char *, char *, char *, char *, int *, int *, double *, double *, int *, double *, int *);
    void (*zpotrf)(char *, int *, XRComplex *, int *, int *);
    /* Preserve SciPy's compiled O(np) QR insertion/deletion kernels. Input
       Q/R describe old_p newest-first columns; S is chronological n-by-p.
       shared columns are the retained oldest prefix of S / newest old QR
       prefix. fresh requests full QR; used_fresh reports fallback/rebuild.
       The callback copies output to Q (leading n), R (leading ld), and
       propagates an existing Python exception by returning nonzero. */
    int (*qr_basis)(void *context, const double *S, int n, int p,
                    int old_p, int shared, int fresh,
                    double *Q, double *R, int ld, int *used_fresh);
    void *qr_context;
} XRBackend;

enum { XR_TRIAL_SECANT = 0, XR_TRIAL_MIDPOINT = 1, XR_TRIAL_LAGGED = 2 };
enum { XR_OK = 0, XR_ALLOC = -1, XR_NUMERICAL = -2, XR_INVALID = -3, XR_CALLBACK = -4 };

typedef struct {
    int m0, m_max, q;
    double inflation, theta, sigma, epsilon, eta0;
    int values, window_hermitian, probe, trial, split_model, floor, safeguard;
    double noise_multiplier, rank_multiplier;
} XRParams;

typedef struct {
    long nrej, nbt, nprobe, nskip, nsafe, nrank_deleted, nwindow_deleted;
    long nF_applied, nF_fallback, nF_omitted, ninterval_empty, nnumerical;
} XRCounters;

typedef struct {
    int n, slots, p, capacity, clean, iteration;
    double *x, *g;
    double f, tau0, c1, c2, fresh, lagged;
    int has_lagged, has_bounds;
    double lower, upper;
    /* Immutable normalized actual secants, chronological columns. Cached
       defect/pairing/euclidean use the same ||step||^2 coordinates as Python. */
    double *S, *Y, *scales, *delta, *pairing, *euclidean;
    unsigned long long *ids, next_id;
    /* Cached QR and Gram representations of previously retained pairs. */
    double *Q, *R, *gram;
    unsigned long long *qr_ids, *gram_ids;
    int qr_p, qr_updates, gram_p;
    /* Preallocated model output and workspaces. */
    double *u, *virtual_x, *virtual_g, *direction, *vwork, *vwork2;
    double *C, *T, *selected, *Awork, *Bwork, *Dwork;
    double *coeff, *rhs, *diag, *terms, *evals, *lapack_work;
    XRComplex *H;
    int *iwork, *pivots;
    long window_sum, model_calls;
    int max_window, memory_changes, maximum_capacity;
    XRCounters counters;
    char error[256];
} XRState;

typedef struct {
    double *u, *virtual_x, *virtual_g, *direction;
    double rho;
    int has_rho, safeguarded, first_pairs, deleted;
} XRModelResult;

int xr_state_init(XRState *, int n, int maximum_capacity);
void xr_state_free(XRState *);
int xr_state_start(XRState *, const XRParams *);
int xr_model_step(XRState *, const XRParams *, const XRBackend *, XRModelResult *);
/* Returns 1 for a stored positive pair, 0 for an unusable/nonpositive pair,
   or a negative error status; step/image are actual physical observations. */
int xr_pair_observe(XRState *, const XRBackend *, const double *step,
                    const double *image, double defect);
void xr_transport(XRState *, const XRBackend *, const double *actual_step);
void xr_update_capacity(XRState *, const XRParams *, int first_pairs,
                         int first_deleted, int evaluations);
void xr_learn_lagged(XRState *, const XRBackend *, const XRModelResult *,
                      const double *point, const double *gradient, double length);

#endif

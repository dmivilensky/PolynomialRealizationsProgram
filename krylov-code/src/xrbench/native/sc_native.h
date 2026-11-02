#ifndef XRBENCH_SC_NATIVE_H
#define XRBENCH_SC_NATIVE_H
#include "competitor_common.h"
/* Independent C implementation of the published compact SC-MSS / SC-SR1
   formulas. P has leading dimension n; small matrices use leading 2*m. */
typedef struct {
  int n, m, q, p, rank, k, lwork, hcount, hnext;
  double *arena, *S, *Y, *Sn, *Yn, *Psi, *P, *small, *small2, *small3, *small4;
  double *R, *W, *X, *tmp, *eval, *tau, *work, *history, *sv, *vec, *vec2;
  int *piv;
} CNScWork;
int cn_sc_init(CNScWork *, int, int, int);
void cn_sc_free(CNScWork *);
int cn_sc_model(CNScWork *, const CNBackend *, int, double, double, double);
int cn_sc_shape(const CNBackend *, int, int, const double *, const double *,
                double, const double *, double, double *, double *, double *,
                double *);
#endif

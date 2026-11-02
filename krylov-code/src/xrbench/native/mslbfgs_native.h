#ifndef XRBENCH_MSLBFGS_NATIVE_H
#define XRBENCH_MSLBFGS_NATIVE_H
#include "competitor_common.h"
/* Diagnostic API uses the identical model executed by cn_ms_execute. */
void *cn_ms_create(int n, int memory, int max_secants, double eps_s, double eps_y,
                   const CNBackend *);
void cn_ms_destroy(void *);
int cn_ms_update(void *, const double *, const double *);
int cn_ms_product(void *, const double *, double *, int inverse);
int cn_ms_snapshot(void *, double *, double *, int *, double *);
int cn_ms_damping(double, double, double, double, double, double *, double *);
#endif

#ifndef XRBENCH_COMPETITOR_COMMON_H
#define XRBENCH_COMPETITOR_COMMON_H
#include "xr_native.h"
/* All matrix arguments use column-major storage and LP64 SciPy capsules. */
typedef struct {
 XRBackend blas;
 void (*dgeqrf)(int*,int*,double*,int*,double*,double*,int*,int*);
 void (*dorgqr)(int*,int*,int*,double*,int*,double*,double*,int*,int*);
 void (*dgeqp3)(int*,int*,double*,int*,int*,double*,double*,int*,int*);
 void (*dgesvd)(char*,char*,int*,int*,double*,int*,double*,double*,int*,double*,int*,double*,int*,int*);
} CNBackend;
typedef struct {const char *key; double value;} CNParam;
typedef struct {const CNParam *items; int count;} CNParams;
/* Optional trace is diagnostics only. Scalars and vector snapshots are copied. */
typedef struct {
 const char *kind; const CNParam *items; int count;
 const double *x, *g, *x_P, *x_A;
} CNTrace;
typedef struct {
 int n; void *context;
 int (*fg)(void*,const double*,double*,double*);
 int (*f)(void*,const double*,double*);
 int (*g)(void*,const double*,double*);
 int (*mark)(void*);
 int (*note)(void*,const char*,double);
 int (*stop)(void*,const char*);
 int (*trace)(void*,const CNTrace*);
} CNOracle;
enum {CN_OK=0,CN_CALLBACK=-1,CN_MEMORY=-2,CN_NUMERICAL=-3,CN_INVALID=-4};
double cn_get(const CNParams*,const char*,double);
int cn_int(const CNParams*,const char*,int);
double cn_dot(const CNBackend*,int,const double*,const double*);
double cn_norm(const CNBackend*,int,const double*);
int cn_finite(int,const double*);
/* MT result: 1 accepted, 0 no sufficient decrease, negative callback failure.
   W is workspace of 4*n doubles (no per-trial allocation). The result includes
   a sufficient-decrease warning fallback, matching the O-ACCEL reference. */
typedef struct {double c1,c2,xtol,stpmin,stpmax; int maxfev; int allow_armijo_fallback;} CNLineParams;
int cn_more_thuente(const CNBackend*,const CNOracle*,const double*,double,
 const double*,const double*,double,const CNLineParams*,double*,double*,double*,double*);
int cn_oaccel_execute(const CNParams*,const CNBackend*,const CNOracle*,const double*);
int cn_ms_execute(const CNParams*,const CNBackend*,const CNOracle*,const double*);
int cn_sc_execute(int,const CNParams*,const CNBackend*,const CNOracle*,const double*);
#endif

#ifndef XRBENCH_XR_EXECUTOR_H
#define XRBENCH_XR_EXECUTOR_H

#include "xr_native.h"

typedef struct {
    int iteration, evaluation, accepted, gradient_evaluated, window, capacity;
    double value, slope, chi;
} XRTraceEvent;

/* Every nonzero callback result means an existing Python exception. No
   callback is retried, relaxed, converted to acceptance, or swallowed. */
typedef struct {
    void *context;
    int (*fg)(void *, const double *, double *, double *);
    int (*f)(void *, const double *, double *);
    int (*g)(void *, const double *, double *);
    int (*mark)(void *);
    int (*note_stop)(void *, const char *);
    int (*trace)(void *, const XRTraceEvent *);
    int (*accepted)(void *, const XRState *, int);
} XROracle;

int xr_execute(XRState *, const XRParams *, const XRBackend *, const XROracle *, int maxbt);

#endif

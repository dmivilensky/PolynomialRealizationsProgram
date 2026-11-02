/* The observed XR executor: krylov.tex Algorithm XR / Execution.lean.
   Floating-point Armijo uses the actual representable displacement. The
   compensation below is an error-free-partials accumulator (math.fsum's
   standard scheme), not a relaxed acceptance test. */
#include "xr_executor.h"

#include <float.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>

static int finite_vector(const double *x, int n) {
    for (int i = 0; i < n; ++i) if (!isfinite(x[i])) return 0;
    return 1;
}

static double compensated(const double *values, int count, int *overflow) {
    double partials[8], x, y, hi, lo, yr;
    int used = 0;
    *overflow = 0;
    for (int k = 0; k < count; ++k) {
        x = values[k];
        int next = 0;
        for (int j = 0; j < used; ++j) {
            y = partials[j];
            if (fabs(x) < fabs(y)) { double swap = x; x = y; y = swap; }
            hi = x + y;
            yr = hi - x;
            lo = y - yr;
            if (lo != 0.0) partials[next++] = lo;
            x = hi;
        }
        used = next;
        if (!isfinite(x)) { *overflow = 1; return x; }
        if (x != 0.0) partials[used++] = x;
    }
    hi = 0.0;
    lo = 0.0;
    if (used) {
        hi = partials[--used];
        while (used) {
            x = hi; y = partials[--used];
            hi = x + y; yr = hi - x; lo = y - yr;
            if (lo != 0.0) break;
        }
        if (used && ((lo < 0.0 && partials[used - 1] < 0.0) ||
                     (lo > 0.0 && partials[used - 1] > 0.0))) {
            y = lo * 2.0; x = hi + y; yr = x - hi;
            if (y == yr) hi = x;
        }
    }
    return hi;
}

static double curvature_ratio(double f, double ft, double slope) {
    if (!isfinite(ft) || !isfinite(slope) || !(slope < 0.0)) return INFINITY;
    double values[3] = {ft, -f, -slope};
    int overflow;
    double residual = compensated(values, 3, &overflow);
    if (overflow) return INFINITY;
    double result = 2.0 * (residual / -slope);
    return isfinite(result) ? result : INFINITY;
}

static double defect(const XRState *state, const XRParams *params,
                     const XRBackend *backend, double ft,
                     const double *gt, const double *step) {
    int one = 1, n = state->n;
    double left = backend->ddot(&n, state->g, &one, (double *)step, &one);
    double right = backend->ddot(&n, (double *)gt, &one, (double *)step, &one);
    if (!isfinite(state->f) || !isfinite(ft) || !isfinite(left) || !isfinite(right)) return NAN;
    double scale = fmax(fmax(fabs(state->f), fabs(ft)), fmax(fabs(left), fabs(right)));
    if (scale == 0.0) return 0.0;
    double values[4] = {ft, -state->f, -0.5 * left, -0.5 * right};
    int overflow;
    double delta = compensated(values, 4, &overflow);
    if (overflow) {
        double scaled[4] = {ft / scale, -state->f / scale,
                            -0.5 * left / scale, -0.5 * right / scale};
        delta = scale * compensated(scaled, 4, &overflow);
    }
    double noise = params->noise_multiplier * DBL_EPSILON * scale *
        (fabs(state->f / scale) + fabs(ft / scale) + fabs(left / scale) + fabs(right / scale));
    return fabs(delta) <= noise ? 0.0 : delta;
}

int xr_execute(XRState *state, const XRParams *params, const XRBackend *backend,
               const XROracle *oracle, int maxbt) {
    int n = state->n, one = 1, status = XR_OK;
    double *memory = calloc((size_t)n * 4, sizeof(double));
    if (!memory) return XR_ALLOC;
    double *point = memory, *gradient = memory + n, *step = memory + 2*n, *image = memory + 3*n;
    for (;;) {
        int nonzero = 0;
        for (int j = 0; j < n; ++j) if (state->g[j] != 0.0) { nonzero = 1; break; }
        if (!nonzero) break;
        XRModelResult current;
        status = xr_model_step(state, params, backend, &current);
        if (status != XR_OK) break;
        int first_pairs = current.first_pairs, first_deleted = current.deleted;
        int probed = 0, advanced = 0;
        double length = 1.0;
        for (int evaluation = 1; evaluation <= maxbt; ++evaluation) {
            int distinct = 0;
            for (int j = 0; j < n; ++j) {
                point[j] = state->x[j] + length * current.u[j];
                step[j] = point[j] - state->x[j];
                if (point[j] != state->x[j]) distinct = 1;
            }
            if (!distinct) {
                status = oracle->note_stop(oracle->context, "floating_point_stagnation") ? XR_CALLBACK : XR_OK;
                goto finish;
            }
            double value;
            int has_gradient = params->probe && !probed;
            int callback = has_gradient ? oracle->fg(oracle->context, point, &value, gradient)
                                        : oracle->f(oracle->context, point, &value);
            if (callback) { status = XR_CALLBACK; goto finish; }
            int finite_value = isfinite(value);
            double slope = backend->ddot(&n, state->g, &one, step, &one);
            double chi = finite_value ? curvature_ratio(state->f, value, slope) : INFINITY;
            int armijo = finite_value && slope < 0.0 && value <= state->f + params->sigma * slope;
            if (armijo && !has_gradient) {
                if (oracle->g(oracle->context, point, gradient)) { status = XR_CALLBACK; goto finish; }
                has_gradient = 1;
            }
            int finite_gradient = has_gradient && finite_vector(gradient, n);
            if (has_gradient && !finite_gradient) chi = INFINITY;
            int accepted = armijo && finite_gradient;
            int informative = finite_value && finite_gradient && chi < INFINITY;
            int used_window = state->p; /* Model that proposed this trial, before its new pair. */
            if (oracle->trace) {
                XRTraceEvent event = {state->iteration, evaluation, accepted, has_gradient,
                                      state->p, state->capacity, value, slope, chi};
                if (oracle->trace(oracle->context, &event)) { status = XR_CALLBACK; goto finish; }
            }
            if (informative && (accepted || (params->probe && !probed))) {
                for (int j = 0; j < n; ++j) image[j] = gradient[j] - state->g[j];
                double delta = params->values ? defect(state, params, backend, value, gradient, step) : 0.0;
                int stored = xr_pair_observe(state, backend, step, image, delta);
                if (stored < 0) { status = stored; goto finish; }
                if (!stored) state->counters.nskip++;
                if (params->trial == XR_TRIAL_LAGGED)
                    xr_learn_lagged(state, backend, &current, point, gradient, length);
            }
            if (accepted) {
                xr_transport(state, backend, step);
                xr_update_capacity(state, params, first_pairs, first_deleted, evaluation);
                memcpy(state->x, point, (size_t)n * sizeof(double));
                memcpy(state->g, gradient, (size_t)n * sizeof(double));
                state->f = value;
                state->iteration++;
                if (oracle->mark(oracle->context)) { status = XR_CALLBACK; goto finish; }
                if (oracle->accepted && oracle->accepted(oracle->context, state, used_window)) {
                    status = XR_CALLBACK; goto finish;
                }
                advanced = 1;
                break;
            }
            state->counters.nrej++;
            if (informative && params->probe && !probed) {
                probed = 1;
                state->counters.nprobe++;
                status = xr_model_step(state, params, backend, &current);
                if (status != XR_OK) goto finish;
                length = 1.0;
            } else {
                length /= fmin(fmax(chi, 2.0), 10.0);
                state->counters.nbt++;
            }
        }
        if (!advanced) {
            status = oracle->note_stop(oracle->context, "backtracking_limit") ? XR_CALLBACK : XR_OK;
            break;
        }
    }
finish:
    free(memory);
    return status;
}

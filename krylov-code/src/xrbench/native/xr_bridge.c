/* CPython/NumPy boundary only. The optimization and model state are C.
   Oracle exceptions retain their original Python identity across cleanup.
   BLAS/LAPACK pointers come from SciPy's public Cython capsule interfaces. */
#define PY_SSIZE_T_CLEAN
#define NPY_NO_DEPRECATED_API NPY_1_7_API_VERSION
#include <Python.h>
#include <numpy/arrayobject.h>

#include "xr_executor.h"

#include <limits.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>

static XRBackend numerical;
static void (*geqrf)(int *, int *, double *, int *, double *, double *, int *, int *);
static void (*orgqr)(int *, int *, int *, double *, int *, double *, double *, int *, int *);
static PyObject *qr_insert_function, *qr_delete_function, *linalg_error;

typedef struct {
    int n, maximum;
    PyObject *fg, *f, *g, *mark, *note, *trace, *accepted_hook, *last_point;
    double *qr_work, *tau;
    int qr_lwork;
} Bridge;

static void clear_bridge(Bridge *bridge) {
    Py_XDECREF(bridge->fg); Py_XDECREF(bridge->f); Py_XDECREF(bridge->g);
    Py_XDECREF(bridge->mark); Py_XDECREF(bridge->note); Py_XDECREF(bridge->trace);
    Py_XDECREF(bridge->accepted_hook); Py_XDECREF(bridge->last_point);
    free(bridge->qr_work); free(bridge->tau);
}

static PyObject *vector_copy(const double *data, int n) {
    npy_intp dimension = n;
    PyObject *array = PyArray_SimpleNew(1, &dimension, NPY_DOUBLE);
    if (array) memcpy(PyArray_DATA((PyArrayObject *)array), data, (size_t)n * sizeof(double));
    return array;
}

static PyObject *oracle_point(Bridge *bridge, const double *point) {
    if (!bridge->last_point || memcmp(PyArray_DATA((PyArrayObject *)bridge->last_point),
                                    point, (size_t)bridge->n * sizeof(double))) {
        PyObject *array = vector_copy(point, bridge->n);
        if (!array) return NULL;
        Py_XSETREF(bridge->last_point, array);
    }
    return bridge->last_point;
}

static int copy_gradient(PyObject *object, double *gradient, int n) {
    PyArrayObject *array = (PyArrayObject *)PyArray_FROM_OTF(object, NPY_DOUBLE, NPY_ARRAY_IN_ARRAY);
    if (!array) return -1;
    if (PyArray_NDIM(array) != 1 || PyArray_DIM(array, 0) != n) {
        Py_DECREF(array);
        PyErr_SetString(PyExc_ValueError, "Oracle gradient must have the same dimension as x");
        return -1;
    }
    memcpy(gradient, PyArray_DATA(array), (size_t)n * sizeof(double));
    Py_DECREF(array);
    return 0;
}

static int call_fg(void *context, const double *point, double *value, double *gradient) {
    Bridge *bridge = context;
    PyObject *array = oracle_point(bridge, point);
    if (!array) return -1;
    PyObject *answer = PyObject_CallOneArg(bridge->fg, array);
    if (!answer) return -1;
    PyObject *sequence = PySequence_Fast(answer, "Oracle.fg must return (value, gradient)");
    Py_DECREF(answer);
    if (!sequence) return -1;
    int result = -1;
    if (PySequence_Fast_GET_SIZE(sequence) != 2) {
        PyErr_SetString(PyExc_ValueError, "Oracle.fg must return exactly two objects");
    } else {
        *value = PyFloat_AsDouble(PySequence_Fast_GET_ITEM(sequence, 0));
        if (!PyErr_Occurred()) result = copy_gradient(PySequence_Fast_GET_ITEM(sequence, 1), gradient, bridge->n);
    }
    Py_DECREF(sequence);
    return result;
}

static int call_f(void *context, const double *point, double *value) {
    Bridge *bridge = context;
    PyObject *array = oracle_point(bridge, point);
    if (!array) return -1;
    PyObject *answer = PyObject_CallOneArg(bridge->f, array);
    if (!answer) return -1;
    *value = PyFloat_AsDouble(answer);
    Py_DECREF(answer);
    return PyErr_Occurred() ? -1 : 0;
}

static int call_g(void *context, const double *point, double *gradient) {
    Bridge *bridge = context;
    PyObject *array = oracle_point(bridge, point);
    if (!array) return -1;
    PyObject *answer = PyObject_CallOneArg(bridge->g, array);
    if (!answer) return -1;
    int status = copy_gradient(answer, gradient, bridge->n);
    Py_DECREF(answer);
    return status;
}

static int call_mark(void *context) {
    Bridge *bridge = context;
    PyObject *answer = PyObject_CallNoArgs(bridge->mark);
    if (!answer) return -1;
    Py_DECREF(answer);
    return 0;
}

static int note_object(Bridge *bridge, const char *name, PyObject *value) {
    if (!value) return -1;
    PyObject *key = PyUnicode_FromString(name);
    PyObject *answer = key ? PyObject_CallFunctionObjArgs(bridge->note, key, value, NULL) : NULL;
    Py_XDECREF(key); Py_DECREF(value);
    if (!answer) return -1;
    Py_DECREF(answer);
    return 0;
}

static int call_stop(void *context, const char *reason) {
    return note_object(context, "stop", PyUnicode_FromString(reason));
}

static PyObject *counter_dictionary(const XRCounters *c) {
    return Py_BuildValue("{s:l,s:l,s:l,s:l,s:l,s:l,s:l,s:l,s:l,s:l,s:l,s:l}",
        "nrej", c->nrej, "nbt", c->nbt, "nprobe", c->nprobe,
        "nskip", c->nskip, "nsafe", c->nsafe, "nrank_deleted", c->nrank_deleted,
        "nwindow_deleted", c->nwindow_deleted, "nF_applied", c->nF_applied,
        "nF_fallback", c->nF_fallback, "nF_omitted", c->nF_omitted,
        "ninterval_empty", c->ninterval_empty, "nnumerical", c->nnumerical);
}

static int call_trace(void *context, const XRTraceEvent *event) {
    Bridge *bridge = context;
    PyObject *record = Py_BuildValue("{s:i,s:i,s:d,s:d,s:d,s:O,s:i,s:i,s:O}",
        "iteration", event->iteration, "evaluation", event->evaluation,
        "value", event->value, "slope", event->slope, "chi", event->chi,
        "accepted", event->accepted ? Py_True : Py_False,
        "window", event->window, "capacity", event->capacity,
        "gradient_evaluated", event->gradient_evaluated ? Py_True : Py_False);
    if (!record) return -1;
    PyObject *answer = PyObject_CallMethod(bridge->trace, "append", "O", record);
    Py_DECREF(record);
    if (!answer) return -1;
    Py_DECREF(answer);
    return 0;
}

static int call_accepted(void *context, const XRState *state, int window) {
    Bridge *bridge = context;
    PyObject *x = vector_copy(state->x, state->n), *g = vector_copy(state->g, state->n);
    PyObject *counters = counter_dictionary(&state->counters);
    PyObject *info = counters ? Py_BuildValue("{s:i,s:i,s:i,s:i,s:O}",
        "iteration", state->iteration, "window", window, "capacity", state->capacity,
        "clean", state->clean, "counters", counters) : NULL;
    PyObject *value = PyFloat_FromDouble(state->f);
    PyObject *answer = x && g && info && value ?
        PyObject_CallFunctionObjArgs(bridge->accepted_hook, x, value, g, info, NULL) : NULL;
    Py_XDECREF(x); Py_XDECREF(g); Py_XDECREF(counters); Py_XDECREF(info); Py_XDECREF(value);
    if (!answer) return -1;
    Py_DECREF(answer);
    return 0;
}

static PyObject *matrix_view(double *data, int rows, int columns, int leading) {
    npy_intp shape[2] = {rows, columns}, strides[2] = {sizeof(double), leading * sizeof(double)};
    return PyArray_New(&PyArray_Type, 2, shape, NPY_DOUBLE, strides, data, 0,
                       NPY_ARRAY_WRITEABLE | NPY_ARRAY_ALIGNED, NULL);
}

static int fresh_qr(Bridge *bridge, const double *S, int n, int p,
                    double *Q, double *R, int ld) {
    for (int j = 0; j < p; ++j) memcpy(Q + (size_t)j*n, S + (size_t)(p-1-j)*n, (size_t)n*sizeof(double));
    int minus_one = -1, info = 0;
    double w1, w2;
    geqrf(&n, &p, Q, &n, bridge->tau, &w1, &minus_one, &info);
    if (info) goto failure;
    orgqr(&n, &p, &p, Q, &n, bridge->tau, &w2, &minus_one, &info);
    if (info) goto failure;
    int need = (int)fmax(w1, w2);
    if (need < 1) need = 1;
    if (need > bridge->qr_lwork) {
        double *work = realloc(bridge->qr_work, (size_t)need*sizeof(double));
        if (!work) { PyErr_NoMemory(); return -1; }
        bridge->qr_work = work;
        bridge->qr_lwork = need;
    }
    geqrf(&n, &p, Q, &n, bridge->tau, bridge->qr_work, &bridge->qr_lwork, &info);
    if (info) goto failure;
    memset(R, 0, (size_t)ld*p*sizeof(double));
    for (int j = 0; j < p; ++j) for (int i = 0; i <= j; ++i) R[i + (size_t)ld*j] = Q[i + (size_t)n*j];
    orgqr(&n, &p, &p, Q, &n, bridge->tau, bridge->qr_work, &bridge->qr_lwork, &info);
    if (!info) return 0;
failure:
    PyErr_Format(linalg_error, "Native QR LAPACK argument failure: %d", info);
    return -1;
}

static int qr_basis(void *context, const double *S, int n, int p, int old_p,
                    int shared, int fresh, double *Q, double *R, int ld, int *used_fresh) {
    Bridge *bridge = context;
    *used_fresh = fresh;
    if (fresh) return fresh_qr(bridge, S, n, p, Q, R, ld);
    if (old_p == p && shared == p) return 0;
    PyObject *q = matrix_view(Q, n, old_p, n), *r = matrix_view(R, old_p, old_p, ld);
    if (!q || !r) { Py_XDECREF(q); Py_XDECREF(r); return -1; }
    if (old_p > shared) {
        PyObject *args = Py_BuildValue("(OOi)", q, r, shared);
        PyObject *kwargs = Py_BuildValue("{s:i,s:s,s:O,s:O}", "p", old_p-shared,
            "which", "col", "overwrite_qr", Py_True, "check_finite", Py_False);
        PyObject *answer = args && kwargs ? PyObject_Call(qr_delete_function, args, kwargs) : NULL;
        Py_XDECREF(args); Py_XDECREF(kwargs);
        if (!answer) goto failure;
        if (!PyTuple_Check(answer) || PyTuple_GET_SIZE(answer) != 2) {
            Py_DECREF(answer); PyErr_SetString(PyExc_RuntimeError, "Unexpected SciPy qr_delete result"); goto failure;
        }
        Py_SETREF(q, Py_NewRef(PyTuple_GET_ITEM(answer, 0)));
        Py_SETREF(r, Py_NewRef(PyTuple_GET_ITEM(answer, 1)));
        Py_DECREF(answer);
    }
    for (int j = shared; j < p; ++j) {
        npy_intp size = n;
        PyObject *column = PyArray_SimpleNewFromData(1, &size, NPY_DOUBLE, (void *)(S+(size_t)j*n));
        PyObject *args = column ? Py_BuildValue("(OOOi)", q, r, column, 0) : NULL;
        Py_XDECREF(column);
        /* S is immutable observed data: qr_insert may overwrite its u argument
           when overwrite_qru is enabled. Keep its documented safe default. */
        PyObject *kwargs = Py_BuildValue("{s:s,s:O}", "which", "col",
                                         "check_finite", Py_False);
        PyObject *answer = args && kwargs ? PyObject_Call(qr_insert_function, args, kwargs) : NULL;
        Py_XDECREF(args); Py_XDECREF(kwargs);
        if (!answer) goto failure;
        if (!PyTuple_Check(answer) || PyTuple_GET_SIZE(answer) != 2) {
            Py_DECREF(answer); PyErr_SetString(PyExc_RuntimeError, "Unexpected SciPy qr_insert result"); goto failure;
        }
        Py_SETREF(q, Py_NewRef(PyTuple_GET_ITEM(answer, 0)));
        Py_SETREF(r, Py_NewRef(PyTuple_GET_ITEM(answer, 1)));
        Py_DECREF(answer);
    }
    if (!PyArray_Check(q) || !PyArray_Check(r) || PyArray_TYPE((PyArrayObject *)q) != NPY_DOUBLE ||
        PyArray_TYPE((PyArrayObject *)r) != NPY_DOUBLE || PyArray_NDIM((PyArrayObject *)q) != 2 ||
        PyArray_DIM((PyArrayObject *)q, 0) != n || PyArray_DIM((PyArrayObject *)q, 1) != p ||
        PyArray_NDIM((PyArrayObject *)r) != 2 || PyArray_DIM((PyArrayObject *)r, 0) != p ||
        PyArray_DIM((PyArrayObject *)r, 1) != p) {
        PyErr_SetString(PyExc_RuntimeError, "Unexpected SciPy updated QR dimensions"); goto failure;
    }
    for (int j = 0; j < p; ++j) for (int i = 0; i < n; ++i)
        Q[i+(size_t)n*j] = *(double *)PyArray_GETPTR2((PyArrayObject *)q, i, j);
    for (int j = 0; j < p; ++j) for (int i = 0; i < p; ++i)
        R[i+(size_t)ld*j] = *(double *)PyArray_GETPTR2((PyArrayObject *)r, i, j);
    Py_DECREF(q); Py_DECREF(r);
    return 0;
failure:
    Py_DECREF(q); Py_DECREF(r);
    if (PyErr_ExceptionMatches(linalg_error)) {
        PyErr_Clear(); *used_fresh = 1;
        return fresh_qr(bridge, S, n, p, Q, R, ld);
    }
    return -1;
}

static int integer_parameter(PyObject *params, const char *name, int *target) {
    PyObject *object = PyDict_GetItemString(params, name);
    if (!object) { PyErr_Format(PyExc_ValueError, "Missing XR parameter: %s", name); return -1; }
    long number = PyLong_AsLong(object);
    if (PyErr_Occurred()) return -1;
    if (number < INT_MIN || number > INT_MAX) { PyErr_SetString(PyExc_OverflowError, "XR integer parameter too large"); return -1; }
    *target = (int)number; return 0;
}

static int float_parameter(PyObject *params, const char *name, double *target) {
    PyObject *object = PyDict_GetItemString(params, name);
    if (!object) { PyErr_Format(PyExc_ValueError, "Missing XR parameter: %s", name); return -1; }
    *target = PyFloat_AsDouble(object); return PyErr_Occurred() ? -1 : 0;
}

static int boolean_parameter(PyObject *params, const char *name, int *target) {
    PyObject *object = PyDict_GetItemString(params, name);
    if (!object) { PyErr_Format(PyExc_ValueError, "Missing XR parameter: %s", name); return -1; }
    *target = PyObject_IsTrue(object); return *target < 0 ? -1 : 0;
}

static int parameters(PyObject *dictionary, XRParams *params) {
    if (!PyDict_Check(dictionary)) { PyErr_SetString(PyExc_TypeError, "XR parameters must be a dictionary"); return -1; }
#define INT(name) if (integer_parameter(dictionary, #name, &params->name)) return -1
#define FLOAT(name) if (float_parameter(dictionary, #name, &params->name)) return -1
#define BOOL(name) if (boolean_parameter(dictionary, #name, &params->name)) return -1
    INT(m0); INT(m_max); INT(q);
    FLOAT(inflation); FLOAT(theta); FLOAT(sigma); FLOAT(epsilon); FLOAT(eta0);
    FLOAT(noise_multiplier); FLOAT(rank_multiplier);
    BOOL(values); BOOL(probe); BOOL(floor); BOOL(safeguard);
#undef INT
#undef FLOAT
#undef BOOL
    PyObject *object = PyDict_GetItemString(dictionary, "window");
    if (!object) { PyErr_SetString(PyExc_ValueError, "Missing window policy"); return -1; }
    const char *window = PyUnicode_AsUTF8(object);
    if (!window) return -1;
    if (strcmp(window, "hermitian") && strcmp(window, "positive")) {
        PyErr_SetString(PyExc_ValueError, "Unknown XR window policy"); return -1;
    }
    params->window_hermitian = !strcmp(window, "hermitian");
    object = PyDict_GetItemString(dictionary, "split");
    if (!object) { PyErr_SetString(PyExc_ValueError, "Missing value split"); return -1; }
    const char *split = PyUnicode_AsUTF8(object);
    if (!split) return -1;
    if (strcmp(split, "model") && strcmp(split, "euclidean")) {
        PyErr_SetString(PyExc_ValueError, "Unknown XR value split"); return -1;
    }
    params->split_model = !strcmp(split, "model");
    object = PyDict_GetItemString(dictionary, "trial");
    if (!object) { PyErr_SetString(PyExc_ValueError, "Missing XR trial policy"); return -1; }
    const char *trial = PyUnicode_AsUTF8(object);
    if (!trial) return -1;
    if (strcmp(trial, "secant") && strcmp(trial, "midpoint") && strcmp(trial, "lagged")) {
        PyErr_SetString(PyExc_ValueError, "Unknown XR trial policy"); return -1;
    }
    params->trial = !strcmp(trial, "secant") ? XR_TRIAL_SECANT :
                    !strcmp(trial, "midpoint") ? XR_TRIAL_MIDPOINT : XR_TRIAL_LAGGED;
    if (params->m0 < 1 || params->m_max < params->m0 || params->q < 1 ||
        !(params->inflation > 1.0 && isfinite(params->inflation)) ||
        !(params->theta > 0.0 && isfinite(params->theta)) ||
        !(params->sigma > 0.0 && params->sigma < 0.5) ||
        !(params->epsilon > 0.0 && params->epsilon < 1.0) ||
        !(params->eta0 > 0.0 && params->eta0 < 1.0-2.0*params->sigma) ||
        !(params->noise_multiplier >= 0.0 && isfinite(params->noise_multiplier)) ||
        !(params->rank_multiplier > 0.0 && isfinite(params->rank_multiplier))) {
        PyErr_SetString(PyExc_ValueError, "Invalid native XR algorithm parameters"); return -1;
    }
    return 0;
}

static int summarize(Bridge *bridge, XRState *state) {
    if (note_object(bridge, "counters", counter_dictionary(&state->counters))) return -1;
    if (note_object(bridge, "mean_window", PyFloat_FromDouble((double)state->window_sum / fmax(state->model_calls, 1)))) return -1;
    if (note_object(bridge, "maximum_window", PyLong_FromLong(state->max_window))) return -1;
    if (note_object(bridge, "growing_memory", Py_BuildValue("{s:i,s:i,s:i,s:i}",
        "final", state->capacity, "maximum", state->maximum_capacity,
        "changes", state->memory_changes, "clean", state->clean))) return -1;
    PyObject *bounds = state->has_bounds ? Py_BuildValue("(dd)", state->lower, state->upper) : Py_NewRef(Py_None);
    if (note_object(bridge, "spectral_estimates", bounds)) return -1;
    return note_object(bridge, "secant_curvature", PyFloat_FromDouble(state->fresh));
}

static PyObject *solve(PyObject *self, PyObject *arguments) {
    (void)self;
    PyObject *oracle, *initial, *dictionary, *mu = Py_None, *upper = Py_None;
    PyObject *trace = Py_None, *accepted_hook = Py_None;
    int maxbt = 80;
    if (!PyArg_ParseTuple(arguments, "OOO|OOiOO", &oracle, &initial, &dictionary,
                          &mu, &upper, &maxbt, &trace, &accepted_hook)) return NULL;
    XRParams params;
    if (parameters(dictionary, &params)) return NULL;
    if (maxbt < 1) { PyErr_SetString(PyExc_ValueError, "maxbt must be positive"); return NULL; }
    PyArrayObject *x = (PyArrayObject *)PyArray_FROM_OTF(initial, NPY_DOUBLE, NPY_ARRAY_IN_ARRAY);
    if (!x) return NULL;
    if (PyArray_NDIM(x) != 1 || PyArray_DIM(x, 0) < 1 || PyArray_DIM(x, 0) > INT_MAX) {
        Py_DECREF(x); PyErr_SetString(PyExc_ValueError, "XR requires a nonempty one-dimensional point"); return NULL;
    }
    XRState state;
    int n = (int)PyArray_DIM(x, 0), maximum = params.m_max < n ? params.m_max : n;
    int status = xr_state_init(&state, n, maximum), started = 0;
    Bridge bridge = {0};
    bridge.n = n; bridge.maximum = maximum;
    if (status != XR_OK) { Py_DECREF(x); xr_state_free(&state); PyErr_NoMemory(); return NULL; }
    memcpy(state.x, PyArray_DATA(x), (size_t)n*sizeof(double));
    Py_DECREF(x);
    bridge.fg = PyObject_GetAttrString(oracle, "fg"); bridge.f = PyObject_GetAttrString(oracle, "f");
    bridge.g = PyObject_GetAttrString(oracle, "g"); bridge.mark = PyObject_GetAttrString(oracle, "mark_iter");
    bridge.note = PyObject_GetAttrString(oracle, "note");
    bridge.trace = Py_NewRef(trace); bridge.accepted_hook = Py_NewRef(accepted_hook);
    bridge.tau = calloc((size_t)maximum+1, sizeof(double));
    if (!bridge.tau) PyErr_NoMemory();
    if (!bridge.fg || !bridge.f || !bridge.g || !bridge.mark || !bridge.note || !bridge.tau) goto cleanup;
    if (call_fg(&bridge, state.x, &state.f, state.g)) goto cleanup;
    if (!isfinite(state.f)) { PyErr_SetString(PyExc_ValueError, "XR requires a finite initial value and gradient"); goto cleanup; }
    for (int j = 0; j < n; ++j) if (!isfinite(state.g[j])) {
        PyErr_SetString(PyExc_ValueError, "XR requires a finite initial value and gradient"); goto cleanup;
    }
    if (mu != Py_None || upper != Py_None) {
        if (mu == Py_None || upper == Py_None) {
            PyErr_SetString(PyExc_ValueError, "initial spectral estimates require finite 0 < mu <= L"); goto cleanup;
        }
        state.lower = PyFloat_AsDouble(mu); state.upper = PyFloat_AsDouble(upper);
        if (PyErr_Occurred()) goto cleanup;
        if (!(state.lower > 0 && state.lower <= state.upper && isfinite(state.upper))) {
            PyErr_SetString(PyExc_ValueError, "initial spectral estimates require finite 0 < mu <= L"); goto cleanup;
        }
        state.has_bounds = 1;
    }
    status = xr_state_start(&state, &params);
    if (status != XR_OK) { PyErr_SetString(PyExc_ValueError, state.error); goto cleanup; }
    started = 1;
    XRBackend backend = numerical;
    backend.qr_basis = qr_basis; backend.qr_context = &bridge;
    XROracle callbacks = {&bridge, call_fg, call_f, call_g, call_mark, call_stop,
                         trace != Py_None ? call_trace : NULL,
                         accepted_hook != Py_None ? call_accepted : NULL};
    status = xr_execute(&state, &params, &backend, &callbacks, maxbt);
    if (status == XR_ALLOC && !PyErr_Occurred()) PyErr_NoMemory();
    if (status == XR_INVALID && !PyErr_Occurred()) PyErr_SetString(PyExc_ValueError, state.error);
    if (status == XR_NUMERICAL && !PyErr_Occurred()) PyErr_SetString(linalg_error, state.error);
    if (status == XR_CALLBACK && !PyErr_Occurred()) PyErr_SetString(PyExc_RuntimeError, "Native callback failed without an exception");
cleanup:
    if (PyErr_ExceptionMatches(linalg_error) || PyErr_ExceptionMatches(PyExc_FloatingPointError)) {
        PyObject *kind, *value, *traceback;
        PyErr_Fetch(&kind, &value, &traceback);
        PyObject *detail = value ? PyObject_Str(value) : PyUnicode_FromString("native numerical failure");
        Py_XDECREF(kind); Py_XDECREF(value); Py_XDECREF(traceback);
        if (bridge.note && call_stop(&bridge, "numerical_linear_algebra") == 0)
            note_object(&bridge, "detail", detail);
        else Py_XDECREF(detail);
        if (started) state.counters.nnumerical++;
    }
    if (started) {
        PyObject *kind = NULL, *value = NULL, *traceback = NULL;
        PyErr_Fetch(&kind, &value, &traceback);
        int failed = summarize(&bridge, &state);
        if (kind) { PyErr_Clear(); PyErr_Restore(kind, value, traceback); }
        else if (failed && !PyErr_Occurred()) PyErr_SetString(PyExc_RuntimeError, "Native summary callback failed");
    }
    clear_bridge(&bridge);
    xr_state_free(&state);
    if (PyErr_Occurred()) return NULL;
    Py_RETURN_NONE;
}

static void *capsule_pointer(PyObject *module, const char *symbol) {
    PyObject *capsules = PyObject_GetAttrString(module, "__pyx_capi__");
    if (!capsules) return NULL;
    PyObject *capsule = PyDict_GetItemString(capsules, symbol);
    if (!capsule) { Py_DECREF(capsules); PyErr_Format(PyExc_ImportError, "Missing SciPy capsule: %s", symbol); return NULL; }
    const char *name = PyCapsule_GetName(capsule);
    if (!name || !strstr(name, "int *") || strstr(name, "int64")) {
        Py_DECREF(capsules); PyErr_Format(PyExc_ImportError, "Unsupported SciPy integer ABI for %s", symbol); return NULL;
    }
    void *pointer = PyCapsule_GetPointer(capsule, name);
    Py_DECREF(capsules); return pointer;
}

static int initialize_numerical(void) {
    if (sizeof(int) != 4 || sizeof(double) != 8 || sizeof(XRComplex) != 16) {
        PyErr_SetString(PyExc_ImportError, "XR requires int32 and IEEE double SciPy capsules"); return -1;
    }
    PyObject *blas = PyImport_ImportModule("scipy.linalg.cython_blas");
    PyObject *lapack = PyImport_ImportModule("scipy.linalg.cython_lapack");
    if (!blas || !lapack) { Py_XDECREF(blas); Py_XDECREF(lapack); return -1; }
    void *pointer;
#define LOAD(module, member) do { pointer = capsule_pointer(module, #member); if (!pointer) goto failure; memcpy(&numerical.member, &pointer, sizeof(pointer)); } while (0)
    LOAD(blas, ddot); LOAD(blas, dnrm2); LOAD(blas, dgemv); LOAD(blas, dgemm); LOAD(blas, dtrsm);
    LOAD(lapack, dpotrf); LOAD(lapack, dpotrs); LOAD(lapack, dgesv); LOAD(lapack, dtrcon);
    LOAD(lapack, dsyev); LOAD(lapack, zpotrf);
#undef LOAD
    pointer = capsule_pointer(lapack, "dgeqrf"); if (!pointer) goto failure; memcpy(&geqrf, &pointer, sizeof(pointer));
    pointer = capsule_pointer(lapack, "dorgqr"); if (!pointer) goto failure; memcpy(&orgqr, &pointer, sizeof(pointer));
    Py_DECREF(blas); Py_DECREF(lapack);
    PyObject *scipy_linalg = PyImport_ImportModule("scipy.linalg");
    PyObject *numpy_linalg = PyImport_ImportModule("numpy.linalg");
    if (!scipy_linalg || !numpy_linalg) { Py_XDECREF(scipy_linalg); Py_XDECREF(numpy_linalg); return -1; }
    qr_insert_function = PyObject_GetAttrString(scipy_linalg, "qr_insert");
    qr_delete_function = PyObject_GetAttrString(scipy_linalg, "qr_delete");
    linalg_error = PyObject_GetAttrString(numpy_linalg, "LinAlgError");
    Py_DECREF(scipy_linalg); Py_DECREF(numpy_linalg);
    return qr_insert_function && qr_delete_function && linalg_error ? 0 : -1;
failure:
    Py_DECREF(blas); Py_DECREF(lapack); return -1;
}

static int snapshot_vector(PyObject *mapping, const char *key, double *target, int n) {
    PyObject *object = PyDict_GetItemString(mapping, key);
    if (!object) { PyErr_Format(PyExc_ValueError, "Missing state vector: %s", key); return -1; }
    return copy_gradient(object, target, n);
}

static int snapshot_float(PyObject *mapping, const char *key, double *target, int required) {
    PyObject *object = PyDict_GetItemString(mapping, key);
    if (!object || object == Py_None) {
        if (required) { PyErr_Format(PyExc_ValueError, "Missing state scalar: %s", key); return -1; }
        return 0;
    }
    *target = PyFloat_AsDouble(object);
    if (PyErr_Occurred()) return -1;
    if (!isfinite(*target)) { PyErr_Format(PyExc_ValueError, "Nonfinite state scalar: %s", key); return -1; }
    return 0;
}

/* Debug cache snapshots own their arrays. IDs use the native one-based
   observation identity and Q/R retain the documented newest-first basis. */
static PyObject *matrix_copy(const double *data, int rows, int columns, int leading) {
    npy_intp shape[2] = {rows, columns};
    PyObject *array = PyArray_EMPTY(2, shape, NPY_DOUBLE, 1);
    if (array) for (int j = 0; j < columns; ++j)
        memcpy((double *)PyArray_DATA((PyArrayObject *)array)+(size_t)rows*j,
               data+(size_t)leading*j, (size_t)rows*sizeof(double));
    return array;
}

static int read_matrix(PyObject *mapping, const char *key, double *target,
                       int rows, int columns, int leading) {
    PyObject *object = PyDict_GetItemString(mapping, key);
    if (!object) { PyErr_Format(PyExc_ValueError, "Missing cache matrix: %s", key); return -1; }
    PyArrayObject *array = (PyArrayObject *)PyArray_FROM_OTF(object, NPY_DOUBLE, NPY_ARRAY_IN_ARRAY);
    if (!array) return -1;
    if (PyArray_NDIM(array) != 2 || PyArray_DIM(array, 0) != rows || PyArray_DIM(array, 1) != columns) {
        Py_DECREF(array); PyErr_Format(PyExc_ValueError, "Invalid cache matrix dimensions: %s", key); return -1;
    }
    for (int j = 0; j < columns; ++j) for (int i = 0; i < rows; ++i) {
        double value = *(double *)PyArray_GETPTR2(array, i, j);
        if (!isfinite(value)) { Py_DECREF(array); PyErr_SetString(PyExc_ValueError, "Nonfinite cache matrix"); return -1; }
        target[i+(size_t)leading*j] = value;
    }
    Py_DECREF(array); return 0;
}

static int restore_cache(PyObject *snapshot, const char *key, XRState *state, int qr) {
    PyObject *cache = PyDict_GetItemString(snapshot, key);
    if (!cache || cache == Py_None) return 0;
    if (!PyDict_Check(cache)) { PyErr_SetString(PyExc_TypeError, "Model cache must be a dictionary"); return -1; }
    PyObject *object = PyDict_GetItemString(cache, "ids");
    if (!object) { PyErr_SetString(PyExc_ValueError, "Missing cache observation IDs"); return -1; }
    PyObject *ids = PySequence_Fast(object, "Cache IDs must be a sequence");
    if (!ids) return -1;
    Py_ssize_t count = PySequence_Fast_GET_SIZE(ids);
    if (count < 0 || count > state->slots || count > state->n) {
        Py_DECREF(ids); PyErr_SetString(PyExc_ValueError, "Invalid cache size"); return -1;
    }
    unsigned long long *target = qr ? state->qr_ids : state->gram_ids, previous = 0;
    for (Py_ssize_t j = 0; j < count; ++j) {
        unsigned long long id = PyLong_AsUnsignedLongLong(PySequence_Fast_GET_ITEM(ids, j));
        if (PyErr_Occurred()) { Py_DECREF(ids); return -1; }
        if (id <= previous || id > state->next_id) {
            Py_DECREF(ids); PyErr_SetString(PyExc_ValueError, "Cache IDs must be increasing observed identities"); return -1;
        }
        target[j] = id; previous = id;
    }
    Py_DECREF(ids);
    int p = (int)count;
    if (qr) {
        if (read_matrix(cache, "Q", state->Q, state->n, p, state->n) ||
            read_matrix(cache, "R", state->R, p, p, state->slots)) return -1;
        state->qr_p = p;
        object = PyDict_GetItemString(cache, "updates");
        if (object) {
            long updates = PyLong_AsLong(object);
            if (PyErr_Occurred()) return -1;
            if (updates < 0 || updates > INT_MAX) { PyErr_SetString(PyExc_ValueError, "Invalid QR refresh count"); return -1; }
            state->qr_updates = (int)updates;
        }
    } else {
        if (read_matrix(cache, "matrix", state->gram, p, p, state->slots)) return -1;
        state->gram_p = p;
    }
    return 0;
}

static PyObject *export_cache(const XRState *state, int qr) {
    int p = qr ? state->qr_p : state->gram_p;
    const unsigned long long *source = qr ? state->qr_ids : state->gram_ids;
    PyObject *ids = PyList_New(p), *result = NULL;
    if (!ids) return NULL;
    for (int j = 0; j < p; ++j) {
        PyObject *id = PyLong_FromUnsignedLongLong(source[j]);
        if (!id) { Py_DECREF(ids); return NULL; }
        PyList_SET_ITEM(ids, j, id);
    }
    if (qr) {
        PyObject *q = matrix_copy(state->Q, state->n, p, state->n);
        PyObject *r = matrix_copy(state->R, p, p, state->slots);
        if (q && r) result = Py_BuildValue("{s:O,s:O,s:O,s:i}", "Q", q, "R", r,
                                          "ids", ids, "updates", state->qr_updates);
        Py_XDECREF(q); Py_XDECREF(r);
    } else {
        PyObject *matrix = matrix_copy(state->gram, p, p, state->slots);
        if (matrix) result = Py_BuildValue("{s:O,s:O}", "matrix", matrix, "ids", ids);
        Py_XDECREF(matrix);
    }
    Py_DECREF(ids); return result;
}

static PyObject *debug_model(PyObject *self, PyObject *arguments) {
    (void)self;
    PyObject *snapshot, *dictionary;
    if (!PyArg_ParseTuple(arguments, "OO", &snapshot, &dictionary)) return NULL;
    if (!PyDict_Check(snapshot)) { PyErr_SetString(PyExc_TypeError, "Model snapshot must be a dictionary"); return NULL; }
    XRParams params;
    if (parameters(dictionary, &params)) return NULL;
    PyObject *x_object = PyDict_GetItemString(snapshot, "x");
    PyArrayObject *x = x_object ? (PyArrayObject *)PyArray_FROM_OTF(x_object, NPY_DOUBLE, NPY_ARRAY_IN_ARRAY) : NULL;
    if (!x) { if (!PyErr_Occurred()) PyErr_SetString(PyExc_ValueError, "Missing model point"); return NULL; }
    if (PyArray_NDIM(x) != 1 || PyArray_DIM(x, 0) < 1 || PyArray_DIM(x, 0) > INT_MAX) {
        Py_DECREF(x); PyErr_SetString(PyExc_ValueError, "Invalid model point dimension"); return NULL;
    }
    int n = (int)PyArray_DIM(x, 0), maximum = params.m_max < n ? params.m_max : n;
    XRState state;
    int status = xr_state_init(&state, n, maximum);
    Bridge bridge = {0};
    PyObject *result = NULL, *sequence = NULL;
    double *pair_buffers = NULL;
    if (status != XR_OK) { Py_DECREF(x); xr_state_free(&state); return PyErr_NoMemory(); }
    memcpy(state.x, PyArray_DATA(x), (size_t)n*sizeof(double));
    Py_DECREF(x);
    bridge.n = n; bridge.maximum = maximum;
    bridge.tau = calloc((size_t)maximum+1, sizeof(double));
    if (!bridge.tau) { PyErr_NoMemory(); goto finish; }
    if (snapshot_vector(snapshot, "g", state.g, n) || snapshot_float(snapshot, "f", &state.f, 1)) goto finish;
    status = xr_state_start(&state, &params);
    if (status != XR_OK) { PyErr_SetString(PyExc_ValueError, state.error); goto finish; }
    if (snapshot_float(snapshot, "tau0", &state.tau0, 0) || snapshot_float(snapshot, "c1", &state.c1, 0) ||
        snapshot_float(snapshot, "c2", &state.c2, 0)) goto finish;
    PyObject *capacity = PyDict_GetItemString(snapshot, "capacity");
    if (capacity) {
        long value = PyLong_AsLong(capacity);
        if (PyErr_Occurred()) goto finish;
        if (value < 1 || value > maximum) { PyErr_SetString(PyExc_ValueError, "Invalid snapshot capacity"); goto finish; }
        state.capacity = (int)value; state.maximum_capacity = (int)value;
    }
    PyObject *pairs = PyDict_GetItemString(snapshot, "pairs");
    if (pairs) {
        sequence = PySequence_Fast(pairs, "Snapshot pairs must be a sequence");
        if (!sequence) goto finish;
        if (PySequence_Fast_GET_SIZE(sequence) > state.slots) {
            PyErr_SetString(PyExc_ValueError, "Snapshot exceeds the executor's observation capacity"); goto finish;
        }
        pair_buffers = calloc((size_t)n*2, sizeof(double));
        if (!pair_buffers) { PyErr_NoMemory(); goto finish; }
        for (Py_ssize_t j = 0; j < PySequence_Fast_GET_SIZE(sequence); ++j) {
            PyObject *pair = PySequence_Fast_GET_ITEM(sequence, j);
            if (!PyDict_Check(pair)) { PyErr_SetString(PyExc_TypeError, "Each snapshot pair must be a dictionary"); goto finish; }
            if (snapshot_vector(pair, "step", pair_buffers, n) || snapshot_vector(pair, "image", pair_buffers+n, n)) goto finish;
            status = xr_pair_observe(&state, &numerical, pair_buffers, pair_buffers+n, 0.0);
            if (status != 1) { PyErr_SetString(PyExc_ValueError, "Snapshot pairs must have positive observed curvature"); goto finish; }
            if (snapshot_float(pair, "delta", &state.delta[j], 0) ||
                snapshot_float(pair, "pairing", &state.pairing[j], 0) ||
                snapshot_float(pair, "euclidean", &state.euclidean[j], 0)) goto finish;
            PyObject *identity = PyDict_GetItemString(pair, "id");
            if (identity) {
                unsigned long long id = PyLong_AsUnsignedLongLong(identity);
                if (PyErr_Occurred()) goto finish;
                if (!id || (j && id <= state.ids[j-1])) {
                    PyErr_SetString(PyExc_ValueError, "Pair IDs must be positive and increasing"); goto finish;
                }
                state.ids[j] = id; state.next_id = id;
            }
        }
    }
    if (snapshot_float(snapshot, "secant_curvature", &state.fresh, 0)) goto finish;
    PyObject *lagged = PyDict_GetItemString(snapshot, "lagged");
    if (lagged && lagged != Py_None) {
        state.lagged = PyFloat_AsDouble(lagged);
        if (PyErr_Occurred()) goto finish;
        if (!(state.lagged > 0.0 && isfinite(state.lagged))) {
            PyErr_SetString(PyExc_ValueError, "Invalid lagged curvature"); goto finish;
        }
        state.has_lagged = 1;
    }
    PyObject *bounds = PyDict_GetItemString(snapshot, "bounds");
    if (bounds && bounds != Py_None) {
        PyObject *values = PySequence_Fast(bounds, "Bounds must be a pair");
        if (!values) goto finish;
        if (PySequence_Fast_GET_SIZE(values) != 2) {
            Py_DECREF(values); PyErr_SetString(PyExc_ValueError, "Bounds must contain two scalars"); goto finish;
        }
        state.lower = PyFloat_AsDouble(PySequence_Fast_GET_ITEM(values, 0));
        state.upper = PyFloat_AsDouble(PySequence_Fast_GET_ITEM(values, 1));
        Py_DECREF(values);
        if (PyErr_Occurred()) goto finish;
        if (!(state.lower > 0.0 && state.lower <= state.upper && isfinite(state.upper))) {
            PyErr_SetString(PyExc_ValueError, "Invalid snapshot spectral bounds"); goto finish;
        }
        state.has_bounds = 1;
    }
    if (!(state.tau0 > 0.0 && state.c1 > 0.0 && state.c2 >= state.c1 && state.fresh > 0.0)) {
        PyErr_SetString(PyExc_ValueError, "Invalid model scale constants"); goto finish;
    }
    if (restore_cache(snapshot, "qr_cache", &state, 1) ||
        restore_cache(snapshot, "gram_cache", &state, 0)) goto finish;
    XRBackend backend = numerical;
    backend.qr_basis = qr_basis; backend.qr_context = &bridge;
    XRModelResult model;
    status = xr_model_step(&state, &params, &backend, &model);
    if (status != XR_OK) {
        if (!PyErr_Occurred()) PyErr_SetString(status == XR_ALLOC ? PyExc_MemoryError : linalg_error, state.error);
        goto finish;
    }
    PyObject *u = vector_copy(model.u, n), *vx = vector_copy(model.virtual_x, n);
    PyObject *vg = vector_copy(model.virtual_g, n), *direction = vector_copy(model.direction, n);
    PyObject *rho = model.has_rho ? PyFloat_FromDouble(model.rho) : Py_NewRef(Py_None);
    PyObject *indices = PyList_New(state.p), *counters = counter_dictionary(&state.counters);
    PyObject *new_bounds = state.has_bounds ? Py_BuildValue("(dd)", state.lower, state.upper) : Py_NewRef(Py_None);
    if (indices) for (int j = 0; j < state.p; ++j) {
        PyObject *index = PyLong_FromUnsignedLongLong(state.ids[j]-1);
        if (!index) { Py_CLEAR(indices); break; }
        PyList_SET_ITEM(indices, j, index);
    }
    if (u && vx && vg && direction && rho && indices && counters && new_bounds)
        result = Py_BuildValue("{s:O,s:O,s:O,s:O,s:O,s:O,s:O,s:O,s:d,s:O,s:i,s:i}",
            "u", u, "virtual_x", vx, "virtual_g", vg, "direction", direction,
            "rho", rho, "pair_indices", indices, "counters", counters, "bounds", new_bounds,
            "secant_curvature", state.fresh, "safeguarded", model.safeguarded ? Py_True : Py_False,
            "first_pairs", model.first_pairs, "deleted", model.deleted);
    if (result) {
        PyObject *qr_cache = export_cache(&state, 1), *gram_cache = export_cache(&state, 0);
        if (!qr_cache || !gram_cache || PyDict_SetItemString(result, "qr_cache", qr_cache) ||
            PyDict_SetItemString(result, "gram_cache", gram_cache)) Py_CLEAR(result);
        Py_XDECREF(qr_cache); Py_XDECREF(gram_cache);
    }
    Py_XDECREF(u); Py_XDECREF(vx); Py_XDECREF(vg); Py_XDECREF(direction); Py_XDECREF(rho);
    Py_XDECREF(indices); Py_XDECREF(counters); Py_XDECREF(new_bounds);
finish:
    Py_XDECREF(sequence); free(pair_buffers); clear_bridge(&bridge); xr_state_free(&state);
    return result;
}

static PyMethodDef methods[] = {
    {"solve", solve, METH_VARARGS, "Execute XR in C with the unchanged Python oracle."},
    {"debug_model", debug_model, METH_VARARGS, "Evaluate a seeded observed-data model for independent tests."},
    {NULL, NULL, 0, NULL}
};
static struct PyModuleDef definition = {
    PyModuleDef_HEAD_INIT, "_xr_native", NULL, -1, methods, NULL, NULL, NULL, NULL
};

PyMODINIT_FUNC PyInit__xr_native(void) {
    import_array();
    if (initialize_numerical()) return NULL;
    return PyModule_Create(&definition);
}

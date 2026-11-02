/* Diagnostics use Python buffers only; production execution stays in
 * sc_native.c. */
#define PY_SSIZE_T_CLEAN
#include "sc_native.h"
#include <Python.h>
#include <string.h>
extern CNBackend cn_backend;
static PyObject *vector_list(const double *x, int n) {
  PyObject *v = PyList_New(n);
  if (!v)
    return NULL;
  for (int i = 0; i < n; i++) {
    PyObject *t = PyFloat_FromDouble(x[i]);
    if (!t) {
      Py_DECREF(v);
      return NULL;
    }
    PyList_SET_ITEM(v, i, t);
  }
  return v;
}
static int doubles(PyObject *o, Py_buffer *v) {
  if (PyObject_GetBuffer(o, v, PyBUF_CONTIG_RO | PyBUF_FORMAT) < 0)
    return 0;
  if (v->itemsize != 8 || !v->format || strcmp(v->format, "d")) {
    PyBuffer_Release(v);
    PyErr_SetString(PyExc_TypeError, "expected contiguous double array");
    return 0;
  }
  return 1;
}
/* Inputs S,Y are flattened column-major contiguous vectors, n is explicit. */
PyObject *cn_debug_sc_model(PyObject *self, PyObject *args) {
  (void)self;
  PyObject *S, *Y;
  int n, variant;
  double gamma, gc, tol = 1e-10;
  Py_buffer sb, yb;
  if (!PyArg_ParseTuple(args, "OOiidd|d", &S, &Y, &n, &variant, &gamma, &gc,
                        &tol))
    return NULL;
  if (!doubles(S, &sb))
    return NULL;
  if (!doubles(Y, &yb)) {
    PyBuffer_Release(&sb);
    return NULL;
  }
  if (n < 1 || sb.len != yb.len || sb.len % (8 * n)) {
    PyBuffer_Release(&sb);
    PyBuffer_Release(&yb);
    PyErr_SetString(PyExc_ValueError, "invalid model dimensions");
    return NULL;
  }
  int p = (int)(sb.len / (8 * n));
  CNScWork w;
  int rc = cn_sc_init(&w, n, p ? p : 1, 1);
  if (!rc) {
    w.p = p;
    memcpy(w.S, sb.buf, sb.len);
    memcpy(w.Y, yb.buf, yb.len);
    rc = cn_sc_model(&w, &cn_backend, variant, gamma, gc, tol);
  }
  PyBuffer_Release(&sb);
  PyBuffer_Release(&yb);
  if (rc) {
    cn_sc_free(&w);
    PyErr_SetString(PyExc_ArithmeticError, "SC model factorization failed");
    return NULL;
  }
  PyObject *pv = vector_list(w.P, n * w.rank),
           *lv = vector_list(w.eval, w.rank), *out = NULL;
  if (pv && lv)
    out = Py_BuildValue("NNi", pv, lv, w.rank);
  else {
    Py_XDECREF(pv);
    Py_XDECREF(lv);
  }
  cn_sc_free(&w);
  return out;
}
PyObject *cn_debug_sc_step(PyObject *self, PyObject *args) {
  (void)self;
  PyObject *G, *P, *L;
  double gamma, delta;
  int n, r;
  Py_buffer gb, pb, lb;
  if (!PyArg_ParseTuple(args, "OOOiidd", &G, &P, &L, &n, &r, &gamma, &delta))
    return NULL;
  if (!doubles(G, &gb))
    return NULL;
  if (!doubles(P, &pb)) {
    PyBuffer_Release(&gb);
    return NULL;
  }
  if (!doubles(L, &lb)) {
    PyBuffer_Release(&gb);
    PyBuffer_Release(&pb);
    return NULL;
  }
  if (n < 1 || r < 0 || r > n || gb.len != 8 * n ||
      pb.len != 8 * (Py_ssize_t)n * r || lb.len != 8 * r) {
    PyBuffer_Release(&gb);
    PyBuffer_Release(&pb);
    PyBuffer_Release(&lb);
    PyErr_SetString(PyExc_ValueError, "invalid step dimensions");
    return NULL;
  }
  double *mem = PyMem_Calloc((size_t)2 * n + r, sizeof(double));
  if (!mem) {
    PyBuffer_Release(&gb);
    PyBuffer_Release(&pb);
    PyBuffer_Release(&lb);
    return PyErr_NoMemory();
  }
  double pBp;
  int rc = cn_sc_shape(&cn_backend, n, r, pb.buf, lb.buf, gamma, gb.buf, delta,
                       mem, &pBp, mem + 2 * n, mem + n);
  PyBuffer_Release(&gb);
  PyBuffer_Release(&pb);
  PyBuffer_Release(&lb);
  PyObject *out = NULL;
  if (!rc) {
    PyObject *p = vector_list(mem, n);
    if (p)
      out = Py_BuildValue("Nd", p, pBp);
  } else
    PyErr_SetString(PyExc_ArithmeticError, "SC subproblem failed");
  PyMem_Free(mem);
  return out;
}

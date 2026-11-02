/* CPython boundary only. All optimization controllers and searches execute C.
   Callback exceptions retain their identity and no evaluation is retried. */
#define PY_SSIZE_T_CLEAN
#define NPY_NO_DEPRECATED_API NPY_1_7_API_VERSION
#include <Python.h>
#include <numpy/arrayobject.h>
#include "competitor_common.h"
#include <limits.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>
CNBackend cn_backend;
typedef struct {int n;PyObject *fg,*f,*g,*mark,*note,*trace,*point;} Bridge;
static PyObject *vector(const double*x,int n){npy_intp m=n;PyObject*a=PyArray_SimpleNew(1,&m,NPY_DOUBLE);if(a)memcpy(PyArray_DATA((PyArrayObject*)a),x,(size_t)n*sizeof(double));return a;}
static PyObject *point(Bridge*b,const double*x){if(!b->point||memcmp(PyArray_DATA((PyArrayObject*)b->point),x,(size_t)b->n*sizeof(double))){PyObject*a=vector(x,b->n);if(!a)return NULL;Py_XSETREF(b->point,a);}return b->point;}
static int gradient(PyObject*a,double*g,int n){PyArrayObject*v=(PyArrayObject*)PyArray_FROM_OTF(a,NPY_DOUBLE,NPY_ARRAY_IN_ARRAY);if(!v)return -1;if(PyArray_NDIM(v)!=1||PyArray_DIM(v,0)!=n){Py_DECREF(v);PyErr_SetString(PyExc_ValueError,"Gradient shape differs from point");return -1;}memcpy(g,PyArray_DATA(v),(size_t)n*sizeof(double));Py_DECREF(v);return 0;}
static int fg(void*c,const double*x,double*f,double*g){Bridge*b=c;PyObject*a=point(b,x);if(!a)return -1;PyObject*r=PyObject_CallOneArg(b->fg,a);if(!r)return -1;PyObject*s=PySequence_Fast(r,"fg must return (f,g)");Py_DECREF(r);if(!s)return -1;int status=-1;if(PySequence_Fast_GET_SIZE(s)!=2)PyErr_SetString(PyExc_ValueError,"fg must return two objects");else{*f=PyFloat_AsDouble(PySequence_Fast_GET_ITEM(s,0));if(!PyErr_Occurred())status=gradient(PySequence_Fast_GET_ITEM(s,1),g,b->n);}Py_DECREF(s);return status;}
static int fun(void*c,const double*x,double*f){Bridge*b=c;PyObject*a=point(b,x);if(!a)return -1;PyObject*r=PyObject_CallOneArg(b->f,a);if(!r)return -1;*f=PyFloat_AsDouble(r);Py_DECREF(r);return PyErr_Occurred()?-1:0;}
static int grad(void*c,const double*x,double*g){Bridge*b=c;PyObject*a=point(b,x);if(!a)return -1;PyObject*r=PyObject_CallOneArg(b->g,a);if(!r)return -1;int s=gradient(r,g,b->n);Py_DECREF(r);return s;}
static int mark(void*c){Bridge*b=c;PyObject*r=PyObject_CallNoArgs(b->mark);if(!r)return -1;Py_DECREF(r);return 0;}
static int note_object(Bridge*b,const char*k,PyObject*v){
 /* Final diagnostics may run during a convergence/budget callback exception.
    Save/clear/restore it around the optional note, preserving exact identity. */
 PyObject *kind=NULL,*value=NULL,*tb=NULL;PyErr_Fetch(&kind,&value,&tb);int result=0;
 if(!v){if(!kind)PyErr_NoMemory();result=-1;}
 else if(b->note){PyObject*r=PyObject_CallFunction(b->note,"sO",k,v);if(!r)result=-1;Py_XDECREF(r);}
 Py_XDECREF(v);if(kind){PyErr_Clear();PyErr_Restore(kind,value,tb);}return result;
}
static int note(void*c,const char*k,double v){return note_object(c,k,PyFloat_FromDouble(v));}
static int stop(void*c,const char*k){return note_object(c,"stop",PyUnicode_FromString(k));}
static int trace(void*c,const CNTrace*t){Bridge*b=c;PyObject*r=PyDict_New();if(!r)return -1;for(int i=0;i<t->count;i++){PyObject*v=PyFloat_FromDouble(t->items[i].value);if(!v||PyDict_SetItemString(r,t->items[i].key,v)){Py_XDECREF(v);Py_DECREF(r);return -1;}Py_DECREF(v);}const double *vs[]={t->x,t->g,t->x_P,t->x_A};const char*ks[]={"x","g","x_P","x_A"};for(int i=0;i<4;i++){PyObject*v=vs[i]?vector(vs[i],b->n):Py_NewRef(Py_None);if(!v||PyDict_SetItemString(r,ks[i],v)){Py_XDECREF(v);Py_DECREF(r);return -1;}Py_DECREF(v);}if(t->kind){PyObject*v=PyUnicode_FromString(t->kind);if(!v||PyDict_SetItemString(r,"kind",v)){Py_XDECREF(v);Py_DECREF(r);return -1;}Py_DECREF(v);}PyObject*a=PyObject_CallMethod(b->trace,"append","O",r);Py_DECREF(r);if(!a)return -1;Py_DECREF(a);return 0;}
static void clear(Bridge*b){Py_XDECREF(b->fg);Py_XDECREF(b->f);Py_XDECREF(b->g);Py_XDECREF(b->mark);Py_XDECREF(b->note);Py_XDECREF(b->trace);Py_XDECREF(b->point);}
static PyObject *solve(PyObject*self,PyObject*args){(void)self;const char*method;PyObject*o,*x0,*dictionary,*tr=Py_None;if(!PyArg_ParseTuple(args,"sOOO|O",&method,&o,&x0,&dictionary,&tr))return NULL;if(!PyDict_Check(dictionary)){PyErr_SetString(PyExc_TypeError,"Native parameters must be dictionary");return NULL;}CNParams p={0};p.count=(int)PyDict_Size(dictionary);CNParam*items=calloc((size_t)p.count+1,sizeof(CNParam));if(!items)return PyErr_NoMemory();p.items=items;PyObject*k,*v;Py_ssize_t pos=0;int i=0;while(PyDict_Next(dictionary,&pos,&k,&v)){items[i].key=PyUnicode_AsUTF8(k);items[i].value=PyFloat_AsDouble(v);if(PyErr_Occurred()||!items[i].key){free(items);return NULL;}if(!isfinite(items[i].value)){free(items);PyErr_SetString(PyExc_ValueError,"Native parameters must be finite");return NULL;}i++;}
 PyArrayObject*x=(PyArrayObject*)PyArray_FROM_OTF(x0,NPY_DOUBLE,NPY_ARRAY_IN_ARRAY);if(!x){free(items);return NULL;}if(PyArray_NDIM(x)!=1||PyArray_DIM(x,0)<1||PyArray_DIM(x,0)>INT_MAX){free(items);Py_DECREF(x);PyErr_SetString(PyExc_ValueError,"Nonempty vector required");return NULL;}
 Bridge b={0};b.n=(int)PyArray_DIM(x,0);b.fg=PyObject_GetAttrString(o,"fg");b.f=PyObject_GetAttrString(o,"f");b.g=PyObject_GetAttrString(o,"g");b.mark=PyObject_GetAttrString(o,"mark_iter");b.trace=Py_NewRef(tr);int status=CN_CALLBACK;
 if(b.fg&&b.f&&b.g&&b.mark){b.note=PyObject_GetAttrString(o,"note");if(!b.note&&PyErr_ExceptionMatches(PyExc_AttributeError))PyErr_Clear();if(!PyErr_Occurred()){
 CNOracle callbacks={b.n,&b,fg,fun,grad,mark,note,stop,tr!=Py_None?trace:NULL};const double*start=PyArray_DATA(x);
 if(!strcmp(method,"oaccel"))status=cn_oaccel_execute(&p,&cn_backend,&callbacks,start);
#ifdef HAVE_MS
 else if(!strcmp(method,"mslbfgs"))status=cn_ms_execute(&p,&cn_backend,&callbacks,start);
#endif
#ifdef HAVE_SC
 else if(!strcmp(method,"mss")||!strcmp(method,"sr1"))status=cn_sc_execute(!strcmp(method,"sr1"),&p,&cn_backend,&callbacks,start);
#endif
 else{PyErr_SetString(PyExc_ValueError,"Unknown native competitor");}
 }}
 free(items);Py_DECREF(x);clear(&b);if(!PyErr_Occurred()){if(status==CN_MEMORY)PyErr_NoMemory();else if(status==CN_INVALID)PyErr_SetString(PyExc_ValueError,"Invalid native competitor parameters");else if(status==CN_NUMERICAL)PyErr_SetString(PyExc_FloatingPointError,"Native competitor numerical failure");else if(status!=CN_OK)PyErr_SetString(PyExc_RuntimeError,"Native competitor callback failed");}if(PyErr_Occurred())return NULL;Py_RETURN_NONE;
}
/* Test-only line-search entry: independent SciPy DCSRCH comparisons. */
static PyObject *debug_search(PyObject*self,PyObject*args){
 (void)self;PyObject*o,*xo,*go,*do_;double f0,initial,c1,c2,xtol,lo,hi;int maxfev,fallback;
 if(!PyArg_ParseTuple(args,"OOdOOddddddii",&o,&xo,&f0,&go,&do_,&initial,&c1,&c2,&xtol,&lo,&hi,&maxfev,&fallback))return NULL;
 PyArrayObject*x=(PyArrayObject*)PyArray_FROM_OTF(xo,NPY_DOUBLE,NPY_ARRAY_IN_ARRAY),*g=(PyArrayObject*)PyArray_FROM_OTF(go,NPY_DOUBLE,NPY_ARRAY_IN_ARRAY),*d=(PyArrayObject*)PyArray_FROM_OTF(do_,NPY_DOUBLE,NPY_ARRAY_IN_ARRAY);
 if(!x||!g||!d){Py_XDECREF(x);Py_XDECREF(g);Py_XDECREF(d);return NULL;}
 int n=(int)PyArray_SIZE(x);if(PyArray_NDIM(x)!=1||n<1||PyArray_NDIM(g)!=1||PyArray_SIZE(g)!=n||PyArray_NDIM(d)!=1||PyArray_SIZE(d)!=n){Py_DECREF(x);Py_DECREF(g);Py_DECREF(d);PyErr_SetString(PyExc_ValueError,"Search vectors must have equal positive lengths");return NULL;}
 double*w=calloc((size_t)6*n,sizeof(double));if(!w){Py_DECREF(x);Py_DECREF(g);Py_DECREF(d);return PyErr_NoMemory();}
 Bridge b={0};b.n=n;b.fg=PyObject_GetAttrString(o,"fg");CNOracle callbacks={n,&b,fg,NULL,NULL,NULL,NULL,NULL,NULL};CNLineParams p={c1,c2,xtol,lo,hi,maxfev,fallback};double f=0;int status=CN_CALLBACK;if(b.fg)status=cn_more_thuente(&cn_backend,&callbacks,PyArray_DATA(x),f0,PyArray_DATA(g),PyArray_DATA(d),initial,&p,w,&f,w+n,w+2*n);
 PyObject*r=NULL;if(!PyErr_Occurred()){PyObject*xn=vector(w,n),*gn=vector(w+n,n);if(xn&&gn)r=Py_BuildValue("(iOdO)",status,xn,f,gn);Py_XDECREF(xn);Py_XDECREF(gn);}clear(&b);free(w);Py_DECREF(x);Py_DECREF(g);Py_DECREF(d);return r;
}
static void *capsule(PyObject*m,const char*s){PyObject*d=PyObject_GetAttrString(m,"__pyx_capi__");if(!d)return NULL;PyObject*c=PyDict_GetItemString(d,s);if(!c){Py_DECREF(d);PyErr_Format(PyExc_ImportError,"Missing SciPy capsule: %s",s);return NULL;}const char*n=PyCapsule_GetName(c);if(!n||!strstr(n,"int *")||strstr(n,"int64")){Py_DECREF(d);PyErr_SetString(PyExc_ImportError,"Unsupported SciPy LP64 ABI");return NULL;}void*p=PyCapsule_GetPointer(c,n);Py_DECREF(d);return p;}
static int numerical(void){if(sizeof(int)!=4||sizeof(double)!=8){PyErr_SetString(PyExc_ImportError,"Requires int32 double64 capsules");return -1;}PyObject*b=PyImport_ImportModule("scipy.linalg.cython_blas"),*l=PyImport_ImportModule("scipy.linalg.cython_lapack");if(!b||!l){Py_XDECREF(b);Py_XDECREF(l);return -1;}void*p;
#define LOAD(module,path,symbol) do{p=capsule(module,symbol);if(!p)goto fail;memcpy(&cn_backend.path,&p,sizeof(p));}while(0)
 LOAD(b,blas.ddot,"ddot");LOAD(b,blas.dnrm2,"dnrm2");LOAD(b,blas.dgemv,"dgemv");LOAD(b,blas.dgemm,"dgemm");LOAD(b,blas.dtrsm,"dtrsm");LOAD(l,blas.dpotrf,"dpotrf");LOAD(l,blas.dpotrs,"dpotrs");LOAD(l,blas.dgesv,"dgesv");LOAD(l,blas.dtrcon,"dtrcon");LOAD(l,blas.dsyev,"dsyev");LOAD(l,blas.zpotrf,"zpotrf");LOAD(l,dgeqrf,"dgeqrf");LOAD(l,dorgqr,"dorgqr");LOAD(l,dgeqp3,"dgeqp3");LOAD(l,dgesvd,"dgesvd");
#undef LOAD
 Py_DECREF(b);Py_DECREF(l);return 0;
 fail:Py_DECREF(b);Py_DECREF(l);return -1;}
#ifdef HAVE_SC_DEBUG
extern PyObject *cn_debug_sc_model(PyObject*,PyObject*);
extern PyObject *cn_debug_sc_step(PyObject*,PyObject*);
#endif
static PyMethodDef methods[]={
 {"solve",solve,METH_VARARGS,"Run a full C competitor using the common oracle."},
 {"line_search",debug_search,METH_VARARGS,"Test-only More--Thuente kernel."},
#ifdef HAVE_SC_DEBUG
 {"sc_model",cn_debug_sc_model,METH_VARARGS,"Independent compact model diagnostic."},
 {"sc_step",cn_debug_sc_step,METH_VARARGS,"Independent trust-region step diagnostic."},
#endif
 {NULL,NULL,0,NULL}};
static struct PyModuleDef module={PyModuleDef_HEAD_INIT,"_competitor_native",NULL,-1,methods,NULL,NULL,NULL,NULL};
PyMODINIT_FUNC PyInit__competitor_native(void){import_array();if(numerical())return NULL;return PyModule_Create(&module);}

/* Observed-data XR model, memory and numerical kernels.
 * Mathematical source: krylov/XR/{AlgorithmModel,Practical,ModelStep}.lean.
 * Rank resolution, compensated defects and finite execution stops are the
 * documented floating-point policies, not new secant equations. */
#include "xr_native.h"

#include <float.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define AT(a,i,j,ld) ((a)[(size_t)(j)*(ld)+(i)])
#define MIN(a,b) ((a)<(b)?(a):(b))
#define MAX(a,b) ((a)>(b)?(a):(b))

static int fail(XRState *s, int code, const char *text) {
    snprintf(s->error, sizeof(s->error), "%s", text);
    return code;
}

int xr_state_init(XRState *s, int n, int maximum_capacity) {
    size_t nm, mm;
    memset(s, 0, sizeof(*s));
    if (n < 1 || maximum_capacity < 1 || MIN(n,maximum_capacity)==INT_MAX) return XR_INVALID;
    s->n = n;
    s->slots = MIN(n, maximum_capacity) + 1;
    nm = (size_t)n * s->slots;
    mm = (size_t)s->slots * s->slots;
    if (nm > SIZE_MAX / sizeof(double) || mm > SIZE_MAX / sizeof(XRComplex))
        return fail(s, XR_ALLOC, "native XR workspace size overflow");
#define ALLOC(name,count,type) do { \
    s->name = (type *)calloc((count), sizeof(type)); \
    if (!s->name) { xr_state_free(s); return XR_ALLOC; } \
} while (0)
    ALLOC(x,n,double); ALLOC(g,n,double);
    ALLOC(S,nm,double); ALLOC(Y,nm,double); ALLOC(Q,nm,double);
    ALLOC(scales,s->slots,double); ALLOC(delta,s->slots,double);
    ALLOC(pairing,s->slots,double); ALLOC(euclidean,s->slots,double);
    ALLOC(ids,s->slots,unsigned long long);
    ALLOC(qr_ids,s->slots,unsigned long long);
    ALLOC(gram_ids,s->slots,unsigned long long);
    ALLOC(R,mm,double); ALLOC(gram,mm,double); ALLOC(C,mm,double);
    ALLOC(T,mm,double); ALLOC(selected,mm,double);
    ALLOC(Awork,mm,double); ALLOC(Bwork,mm,double); ALLOC(Dwork,mm,double);
    ALLOC(H,mm,XRComplex);
    ALLOC(u,n,double); ALLOC(virtual_x,n,double); ALLOC(virtual_g,n,double);
    ALLOC(direction,n,double); ALLOC(vwork,n,double); ALLOC(vwork2,n,double);
    ALLOC(coeff,s->slots,double); ALLOC(rhs,s->slots,double);
    ALLOC(diag,s->slots,double); ALLOC(terms,s->slots,double);
    ALLOC(evals,s->slots,double); ALLOC(lapack_work,4*s->slots,double);
    ALLOC(iwork,s->slots,int); ALLOC(pivots,s->slots,int);
#undef ALLOC
    return XR_OK;
}

void xr_state_free(XRState *s) {
#define FREE(name) free(s->name)
    FREE(x); FREE(g); FREE(S); FREE(Y); FREE(Q); FREE(R); FREE(gram);
    FREE(scales); FREE(delta); FREE(pairing); FREE(euclidean);
    FREE(ids); FREE(qr_ids); FREE(gram_ids);
    FREE(C); FREE(T); FREE(selected); FREE(Awork); FREE(Bwork); FREE(Dwork); FREE(H);
    FREE(u); FREE(virtual_x); FREE(virtual_g); FREE(direction); FREE(vwork); FREE(vwork2);
    FREE(coeff); FREE(rhs); FREE(diag); FREE(terms); FREE(evals); FREE(lapack_work);
    FREE(iwork); FREE(pivots);
#undef FREE
    memset(s, 0, sizeof(*s));
}

int xr_state_start(XRState *s, const XRParams *p) {
    double size = 0.0;
    int i;
    if (s->n<1 || p->m0<1 || p->m_max<p->m0 || p->q<1 ||
        MIN(s->n,p->m_max)>s->slots-1 || !(p->inflation>1.0) || !(p->theta>0.0) ||
        !(p->sigma>0.0 && p->sigma<0.5) || !(p->epsilon>0.0 && p->epsilon<1.0) ||
        !(p->eta0>0.0 && p->eta0<1.0-2.0*p->sigma) || !(p->noise_multiplier>=0.0) ||
        !(p->rank_multiplier>0.0) || p->trial<XR_TRIAL_SECANT || p->trial>XR_TRIAL_LAGGED)
        return fail(s,XR_INVALID,"invalid native XR algorithm parameters");
    if (!isfinite(s->f)) return fail(s, XR_INVALID, "XR requires a finite initial value");
    for (i=0; i<s->n; ++i) {
        if (!isfinite(s->g[i]))
            return fail(s, XR_INVALID, "XR requires a finite initial gradient");
        size = MAX(size, fabs(s->g[i]));
    }
    s->tau0 = size == 0.0 ? 1.0 : 1.0 / size;
    s->c1 = p->epsilon * s->tau0;
    s->c2 = s->tau0 / p->epsilon;
    s->fresh = 1.0 / s->tau0;
    s->capacity = MIN(s->n, p->m0);
    s->maximum_capacity = s->capacity;
    return XR_OK;
}

static double dot(const XRBackend *b, int n, const double *x, const double *y) {
    int one=1;
    return b->ddot(&n, (double *)x, &one, (double *)y, &one);
}

static double size(const XRBackend *b, int n, const double *x) {
    int one=1;
    return b->dnrm2(&n, (double *)x, &one);
}

static void gemv(const XRBackend *b, int n, int p, const double *A,
                int trans, const double *x, double beta, double *y) {
    char t = trans ? 'T' : 'N';
    int one=1;
    double alpha=1.0;
    b->dgemv(&t, &n, &p, &alpha, (double *)A, &n, (double *)x,
             &one, &beta, y, &one);
}

static void drop_pairs(XRState *s, int count) {
    int remain=s->p-count;
    if (count <= 0) return;
    memmove(s->S, s->S+(size_t)count*s->n, (size_t)remain*s->n*sizeof(double));
    memmove(s->Y, s->Y+(size_t)count*s->n, (size_t)remain*s->n*sizeof(double));
#define DROP(name,type) memmove(s->name,s->name+count,(size_t)remain*sizeof(type))
    DROP(scales,double); DROP(delta,double); DROP(pairing,double); DROP(euclidean,double);
    DROP(ids,unsigned long long);
#undef DROP
    s->p=remain;
}

int xr_pair_observe(XRState *s, const XRBackend *b, const double *step,
                    const double *image, double defect) {
    double scale=size(b,s->n,step), curvature;
    double *sn, *yn;
    int i, j=s->p;
    if (!(scale>0.0) || !isfinite(scale)) return 0;
    if (j>=s->slots) return fail(s,XR_INVALID,"native XR observation capacity exceeded");
    sn=s->S+(size_t)j*s->n; yn=s->Y+(size_t)j*s->n;
    for (i=0;i<s->n;++i) {
        sn[i]=step[i]/scale;
        yn[i]=image[i]/scale;
        if (!isfinite(yn[i])) return 0;
    }
    curvature=dot(b,s->n,sn,yn);
    if (!(curvature>0.0)) return 0;
    s->scales[j]=scale;
    s->delta[j]=defect/scale/scale;
    s->pairing[j]=s->euclidean[j]=0.0;
    s->ids[j]=++s->next_id;
    ++s->p;
    s->fresh=curvature;
    return 1;
}

void xr_transport(XRState *s, const XRBackend *b, const double *actual_step) {
    int i,j;
    for (j=0;j<s->p;++j) {
        for (i=0;i<s->n;++i) s->vwork[i]=actual_step[i]/s->scales[j];
        s->pairing[j]+=dot(b,s->n,s->Y+(size_t)j*s->n,s->vwork);
        s->euclidean[j]+=dot(b,s->n,s->S+(size_t)j*s->n,s->vwork);
    }
}

void xr_update_capacity(XRState *s, const XRParams *p, int first_pairs,
                         int first_deleted, int evaluations) {
    int old=s->capacity;
    if (first_deleted>=MAX(1,(first_pairs+1)/2)) {
        s->capacity=MAX(MIN(p->m0,s->n),s->capacity/2);
        s->clean=0;
    } else {
        s->clean=(evaluations==1 && first_deleted==0 && first_pairs==MIN(s->capacity,s->n))
                 ? s->clean+1 : 0;
        if (s->clean==p->q) {
            s->capacity=MIN(MIN(s->capacity+MIN(p->m0,s->n),p->m_max),s->n);
            s->clean=0;
        }
    }
    s->memory_changes+=(old!=s->capacity);
    s->maximum_capacity=MAX(s->maximum_capacity,s->capacity);
}

void xr_learn_lagged(XRState *s, const XRBackend *b, const XRModelResult *m,
                      const double *point, const double *gradient, double length) {
    double norm, displacement, numerator, estimate;
    int i;
    if (length!=1.0 || m->safeguarded) return;
    norm=size(b,s->n,m->direction);
    if (!(norm>0.0) || !isfinite(norm)) return;
    for (i=0;i<s->n;++i) {
        s->vwork[i]=m->direction[i]/norm;
        s->vwork2[i]=point[i]-m->virtual_x[i];
    }
    displacement=dot(b,s->n,s->vwork,s->vwork2);
    if (displacement==0.0 || !isfinite(displacement)) return;
    for (i=0;i<s->n;++i) s->vwork2[i]=gradient[i]-m->virtual_g[i];
    numerator=dot(b,s->n,s->vwork,s->vwork2);
    estimate=numerator/displacement;
    if (estimate>0.0 && isfinite(estimate)) { s->lagged=estimate; s->has_lagged=1; }
}

static double fallback(const XRState *s, const XRParams *p) {
    return p->trial==XR_TRIAL_MIDPOINT && s->has_bounds
         ? s->lower/2.0+s->upper/2.0 : s->fresh;
}

static int prepare_qr(XRState *s, const XRParams *p, const XRBackend *b) {
    int start=-1,shared=0,i,retained,info=0,used_fresh=0;
    int fresh, nold=s->qr_p, ld=s->slots;
    double threshold=p->rank_multiplier*DBL_EPSILON*MAX(s->n,s->p);
    double resolution=p->rank_multiplier*sqrt(DBL_EPSILON), reciprocal;
    char norm='1',upper='U',nonunit='N';
    if (!s->p) return XR_OK;
    for (i=0;i<s->qr_p;++i) if (s->qr_ids[i]==s->ids[0]) {start=i;break;}
    if (start>=0) {
        shared=MIN(s->qr_p-start,s->p);
        for (i=0;i<shared;++i) if (s->qr_ids[start+i]!=s->ids[i]) {start=-1;shared=0;break;}
    }
    fresh=!nold || s->qr_updates>=50 || start<0;
    if (!b->qr_basis) return fail(s,XR_INVALID,"native XR QR backend is not configured");
    if (b->qr_basis(b->qr_context,s->S,s->n,s->p,nold,shared,fresh,
                    s->Q,s->R,ld,&used_fresh)) return XR_CALLBACK;
    s->qr_updates=used_fresh ? 0 : s->qr_updates+1;
    retained=s->p;
    for (i=0;i<s->p;++i) if (fabs(AT(s->R,i,i,ld))<=threshold) {retained=i;break;}
    while (retained) {
        b->dtrcon(&norm,&upper,&nonunit,&retained,s->R,&ld,&reciprocal,
                   s->lapack_work,s->iwork,&info);
        if (info==0 && reciprocal>resolution) break;
        --retained;
    }
    s->counters.nrank_deleted+=s->p-retained;
    drop_pairs(s,s->p-retained);
    return XR_OK;
}

static void observed_gram(XRState *s, const XRBackend *b) {
    int i,j,k,l,ld=s->slots;
    /* Only immutable overlaps are cached. The O(p^2) integer lookup below
       avoids Python objects and never introduces an extra oracle action. */
    for (i=0;i<s->p;++i) {
        s->iwork[i]=-1;
        for (j=0;j<s->gram_p;++j)
            if (s->ids[i]==s->gram_ids[j]) {s->iwork[i]=j;break;}
    }
    for (j=0;j<s->p;++j) for (i=0;i<s->p;++i) {
        k=s->iwork[i]; l=s->iwork[j];
        AT(s->C,i,j,ld)=k>=0 && l>=0 ? AT(s->gram,k,l,ld)
            : dot(b,s->n,s->S+(size_t)i*s->n,s->Y+(size_t)j*s->n);
    }
    for (j=0;j<s->p;++j) for (i=0;i<s->p;++i)
        AT(s->gram,i,j,ld)=AT(s->C,i,j,ld);
    memcpy(s->gram_ids,s->ids,(size_t)s->p*sizeof(*s->ids));
    s->gram_p=s->p;
}

static int hermitian_info(XRState *s, const XRParams *p, const XRBackend *b,
                          const double *T, int reverse) {
    int i,j,a,c,info=0,n=s->p,ld=s->slots;
    char lower='L';
    for (i=0;i<n;++i) {
        double ci=AT(s->C,i,i,ld);
        if (ci==0.0 || !isfinite(ci)) return n>0 ? 1 : 0;
        s->diag[i]=sqrt(fabs(ci));
    }
    for (j=0;j<n;++j) for (i=0;i<n;++i) {
        double real=AT(T,i,j,ld)/s->diag[i]/s->diag[j];
        double defect=(AT(s->C,i,j,ld)-AT(s->C,j,i,ld))/s->diag[i]/s->diag[j];
        if (!isfinite(AT(s->C,i,j,ld))) return 1;
        a=reverse?n-1-i:i; c=reverse?n-1-j:j;
        AT(s->H,a,c,ld).real=real;
        AT(s->H,a,c,ld).imag=p->window_hermitian ? defect/p->theta : 0.0;
    }
    b->zpotrf(&lower,&n,s->H,&ld,&info);
    return info;
}

static void latest_model(XRState *s) {
    int i,j,ld=s->slots;
    for (j=0;j<s->p;++j) for (i=0;i<s->p;++i)
        AT(s->T,i,j,ld)=AT(s->C,MIN(i,j),MAX(i,j),ld)+0.0;
}

static int select_model(XRState *s, const XRParams *p, const XRBackend *b) {
    int i,j,omitted=0,nonzero=0,ld=s->slots;
    for (j=0;j<s->p;++j) for (i=0;i<s->p;++i)
        AT(s->selected,i,j,ld)=AT(s->T,i,j,ld);
    if (!p->values) return XR_OK;
    for (i=0;i<s->p;++i) {
        double ci=AT(s->C,i,i,ld);
        double split=(p->split_model?s->pairing[i]/ci:s->euclidean[i])-0.5;
        double term=12.0*split*s->delta[i];
        if (!isfinite(term) || fabs(term)>ci/2.0) {omitted+=(term!=0.0);term=0.0;}
        s->terms[i]=term;
        nonzero|=(term!=0.0);
        AT(s->selected,i,i,ld)-=term;
    }
    s->counters.nF_omitted+=omitted;
    if (nonzero) {
        /* The F gate always retains the observed skew, even in the positive-
           only window ablation; this is the same Python value-model gate. */
        XRParams gate=*p;
        gate.window_hermitian=1;
        if (hermitian_info(s,&gate,b,s->selected,0)==0) ++s->counters.nF_applied;
        else {
            ++s->counters.nF_fallback;
            for (j=0;j<s->p;++j) for (i=0;i<s->p;++i)
                AT(s->selected,i,j,ld)=AT(s->T,i,j,ld);
        }
    }
    return XR_OK;
}

static int equilibrated_solve(XRState *s, const XRBackend *b,
                              const double *A, const double *rhs, double *answer,
                              int positive, int transpose) {
    int i,j,a,c,p=s->p,ld=s->slots,one=1,info=0;
    char lower='L';
    for (i=0;i<p;++i) {
        double scale=sqrt(fabs(AT(A,i,i,ld)));
        s->diag[i]=scale==0.0?1.0:scale;
    }
    for (j=0;j<p;++j) for (i=0;i<p;++i) {
        a=positive?p-1-i:i; c=positive?p-1-j:j;
        AT(s->Awork,i,j,p)=(transpose?AT(A,c,a,ld):AT(A,a,c,ld))/s->diag[a]/s->diag[c];
    }
    for (i=0;i<p;++i) {a=positive?p-1-i:i;s->evals[i]=rhs[a]/s->diag[a];}
    if (positive) {
        b->dpotrf(&lower,&p,s->Awork,&p,&info);
        if (info) return XR_NUMERICAL;
        b->dpotrs(&lower,&p,&one,s->Awork,&p,s->evals,&p,&info);
    } else b->dgesv(&p,&one,s->Awork,&p,s->pivots,s->evals,&p,&info);
    if (info) return XR_NUMERICAL;
    for (i=0;i<p;++i) {a=positive?p-1-i:i;answer[a]=s->evals[i]/s->diag[a];}
    return XR_OK;
}

static int midpoint_bounds(XRState *s, const XRParams *p, const XRBackend *b) {
    int i,j,k=s->p,ld=s->slots,lwork=4*s->slots,info=0;
    double one=1.0,lo,hi;
    char left='L',right='R',upper='U',trans='T',normal='N',nonunit='N',lower='L';
    for (j=0;j<k;++j) for (i=0;i<k;++i)
        AT(s->Bwork,i,j,ld)=AT(s->T,k-1-i,k-1-j,ld);
    b->dtrsm(&left,&upper,&trans,&nonunit,&k,&k,&one,s->R,&ld,s->Bwork,&ld);
    b->dtrsm(&right,&upper,&normal,&nonunit,&k,&k,&one,s->R,&ld,s->Bwork,&ld);
    for (j=0;j<k;++j) for (i=0;i<=j;++i) {
        double v=(AT(s->Bwork,i,j,ld)+AT(s->Bwork,j,i,ld))/2.0;
        AT(s->Bwork,i,j,ld)=AT(s->Bwork,j,i,ld)=v;
    }
    for (j=0;j<k;++j) for (i=0;i<k;++i) AT(s->Awork,i,j,k)=AT(s->Bwork,i,j,ld);
    b->dsyev(&normal,&lower,&k,s->Awork,&k,s->evals,s->lapack_work,&lwork,&info);
    if (info || !(s->evals[0]>0.0) || !isfinite(s->evals[k-1]))
        return fail(s,XR_NUMERICAL,"nonpositive computed Ritz value after rank/window tests");
    lo=s->evals[0]/p->inflation;hi=s->evals[k-1]*p->inflation;
    if (s->has_bounds) {s->lower=MIN(s->lower,lo);s->upper=MAX(s->upper,hi);}
    else {s->lower=lo;s->upper=hi;s->has_bounds=1;}
    return XR_OK;
}

static int consistency(XRState *s, const XRParams *p, const XRBackend *b, double *rho) {
    int i,j,ld=s->slots;
    double low,high,estimate,carmijo;
    gemv(b,s->n,s->p,s->Q,1,s->vwork,0.0,s->rhs);
    for (j=0;j<s->p;++j) for (i=0;i<s->p;++i)
        AT(s->Dwork,i,j,ld)=AT(s->Bwork,i,j,ld)-(i==j?s->lower:0.0);
    if (equilibrated_solve(s,b,s->Dwork,s->rhs,s->coeff,1,0))
        return fail(s,XR_NUMERICAL,"lower shifted-Schur solve failed");
    low=s->lower+s->lower*s->lower*dot(b,s->p,s->rhs,s->coeff);
    for (j=0;j<s->p;++j) for (i=0;i<s->p;++i)
        AT(s->Dwork,i,j,ld)=(i==j?s->upper:0.0)-AT(s->Bwork,i,j,ld);
    if (equilibrated_solve(s,b,s->Dwork,s->rhs,s->coeff,1,0))
        return fail(s,XR_NUMERICAL,"upper shifted-Schur solve failed");
    high=s->upper-s->upper*s->upper*dot(b,s->p,s->rhs,s->coeff);
    estimate=low/2.0+high/2.0;
    if (low>high) {
        ++s->counters.ninterval_empty;
        estimate=MIN(MAX(estimate,s->lower),s->upper);
    }
    if (p->floor && high>0.0) {
        carmijo=2.0*(1.0-p->sigma)-p->eta0;
        estimate=MIN(MAX(estimate,high/carmijo),high);
    }
    *rho=estimate;
    return XR_OK;
}

int xr_model_step(XRState *s, const XRParams *p, const XRBackend *b, XRModelResult *m) {
    int i,j,status,deleted=0,info,ld=s->slots,first_pairs;
    double rho=0.0,dnorm,unorm,gnorm,negative_slope,trial,curvature;
    if (s->n<1 || s->capacity<1 || s->p<0 || s->p>s->slots)
        return fail(s,XR_INVALID,"invalid native XR observation state");
    memset(m,0,sizeof(*m));
    m->u=s->u;m->virtual_x=s->virtual_x;m->virtual_g=s->virtual_g;m->direction=s->direction;
    if (s->p) {
        curvature=dot(b,s->n,s->S+(size_t)(s->p-1)*s->n,s->Y+(size_t)(s->p-1)*s->n);
        if (curvature>0.0 && isfinite(curvature)) s->fresh=curvature;
    }
    drop_pairs(s,MAX(0,s->p-MIN(s->capacity,s->n)));
    if (s->p && (status=prepare_qr(s,p,b))) return status;
    first_pairs=s->p;
    for (i=0;i<s->n;++i) {
        s->virtual_x[i]=s->x[i];s->virtual_g[i]=s->g[i];s->direction[i]=-s->g[i];
    }
    if (s->p) {
        observed_gram(s,b);
        latest_model(s);
        info=hermitian_info(s,p,b,s->T,1);
        deleted=MIN(info==0?0:s->p-info+1,s->p-1);
        if (deleted) {
            int remain=s->p-deleted;
            for (j=0;j<remain;++j) for (i=0;i<remain;++i)
                AT(s->C,i,j,ld)=AT(s->C,i+deleted,j+deleted,ld);
            drop_pairs(s,deleted);
            s->counters.nwindow_deleted+=deleted;
            latest_model(s);
        }
        s->qr_p=s->p;
        memcpy(s->qr_ids,s->ids,(size_t)s->p*sizeof(*s->ids));
        select_model(s,p,b);
        gemv(b,s->n,s->p,s->S,1,s->g,0.0,s->rhs);
        if (equilibrated_solve(s,b,s->selected,s->rhs,s->coeff,1,0))
            return fail(s,XR_NUMERICAL,"positive observed model solve failed");
        for (i=0;i<s->p;++i) s->coeff[i]=-s->coeff[i];
        gemv(b,s->n,s->p,s->S,0,s->coeff,0.0,s->u);
        for (i=0;i<s->n;++i) s->virtual_x[i]=s->x[i]+s->u[i];
        gemv(b,s->n,s->p,s->Y,0,s->coeff,0.0,s->virtual_g);
        for (i=0;i<s->n;++i) s->virtual_g[i]=s->g[i]+s->virtual_g[i];
        if (p->trial==XR_TRIAL_MIDPOINT && (status=midpoint_bounds(s,p,b))) return status;
        memset(s->direction,0,(size_t)s->n*sizeof(double));
        if (s->p<s->n) {
            gemv(b,s->n,s->p,s->Y,1,s->virtual_g,0.0,s->rhs);
            status=equilibrated_solve(s,b,s->C,s->rhs,s->coeff,0,1);
            if (!status) {
                gemv(b,s->n,s->p,s->S,0,s->coeff,0.0,s->direction);
                for (i=0;i<s->n;++i) s->direction[i]=-s->virtual_g[i]+s->direction[i];
            } else for (i=0;i<s->n;++i) s->direction[i]=-s->virtual_g[i];
            dnorm=size(b,s->n,s->direction);
            if (dnorm>0.0) {
                for (i=0;i<s->n;++i) s->vwork[i]=s->direction[i]/dnorm;
                if (p->trial==XR_TRIAL_MIDPOINT) {
                    if ((status=consistency(s,p,b,&rho))) return status;
                } else {
                    rho=fallback(s,p);
                    if (p->trial==XR_TRIAL_LAGGED && s->has_lagged) {
                        double low=AT(s->C,0,0,ld),high=low;
                        for (i=1;i<s->p;++i) {
                            low=MIN(low,AT(s->C,i,i,ld));high=MAX(high,AT(s->C,i,i,ld));
                        }
                        rho=MIN(MAX(s->lagged,low),high);
                    }
                }
                if (!(rho>0.0) || !isfinite(rho))
                    return fail(s,XR_NUMERICAL,"nonpositive computed trial curvature");
                trial=dot(b,s->n,s->g,s->vwork)/rho;
                for (i=0;i<s->n;++i) s->u[i]-=trial*s->vwork[i];
                m->has_rho=1;
            }
        }
    } else {
        s->qr_p=0;
        rho=fallback(s,p);
        for (i=0;i<s->n;++i) s->u[i]=-s->g[i]/rho;
        m->has_rho=1;
    }
    s->window_sum+=s->p;++s->model_calls;s->max_window=MAX(s->max_window,s->p);
    m->first_pairs=first_pairs;m->deleted=deleted;m->rho=rho;
    if (p->safeguard) {
        gnorm=size(b,s->n,s->g);unorm=size(b,s->n,s->u);
        negative_slope=dot(b,s->n,s->g,s->u);
        status=0;
        for (i=0;i<s->n;++i) if (!isfinite(s->u[i])) {status=1;break;}
        if (status || negative_slope>-s->c1*(gnorm*gnorm) || unorm>s->c2*gnorm) {
            double scale=fallback(s,p);
            scale=MIN(MAX(scale,1.0/s->c2),1.0/s->c1);
            for (i=0;i<s->n;++i) s->u[i]=-s->g[i]/scale;
            ++s->counters.nsafe;m->safeguarded=1;
        }
    }
    return XR_OK;
}

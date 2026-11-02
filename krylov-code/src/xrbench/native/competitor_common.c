/* More--Thuente DCSRCH/DCSTEP: C translation of SciPy optimize/_dcsrch.py
   (SciPy BSD-3-Clause, copyright SciPy developers), itself a translation of
   MINPACK-2 (More', Thuente, Averick, Carter). See COMPETITOR_LICENSE.txt.
   The four safeguarded interpolation cases and stage-one modified objective
   are retained. Oracle evaluations and warning fallback are explicit. */
#include "competitor_common.h"
#include <math.h>
#include <string.h>
double cn_get(const CNParams*p,const char*k,double d){for(int i=0;i<p->count;i++)if(!strcmp(p->items[i].key,k))return p->items[i].value;return d;}
int cn_int(const CNParams*p,const char*k,int d){return (int)cn_get(p,k,d);}
double cn_dot(const CNBackend*b,int n,const double*x,const double*y){int one=1;return b->blas.ddot(&n,(double*)x,&one,(double*)y,&one);}
double cn_norm(const CNBackend*b,int n,const double*x){int one=1;return b->blas.dnrm2(&n,(double*)x,&one);}
int cn_finite(int n,const double*x){for(int i=0;i<n;i++)if(!isfinite(x[i]))return 0;return 1;}
static double clip(double x,double lo,double hi){return fmin(fmax(x,lo),hi);}
static void dcstep(double *stx,double *fx,double *dx,double *sty,double *fy,double *dy,
                   double *stp,double fp,double dp,int *brackt,double lo,double hi){
 double p,q,r,theta,s,gamma,stpc,stpq,stpf;
 double sgnd=(dp>0?1:dp<0?-1:0)*(*dx>0?1:*dx<0?-1:0);
 if(fp>*fx){
  theta=3*(*fx-fp)/(*stp-*stx)+*dx+dp;s=fmax(fabs(theta),fmax(fabs(*dx),fabs(dp)));
  gamma=s*sqrt((theta/s)*(theta/s)-(*dx/s)*(dp/s));if(*stp<*stx)gamma=-gamma;
  p=(gamma-*dx)+theta;q=((gamma-*dx)+gamma)+dp;r=p/q;stpc=*stx+r*(*stp-*stx);
  stpq=*stx+((*dx/((*fx-fp)/(*stp-*stx)+*dx))/2)*(*stp-*stx);
  stpf=fabs(stpc-*stx)<=fabs(stpq-*stx)?stpc:stpc+(stpq-stpc)/2;*brackt=1;
 }else if(sgnd<0){
  theta=3*(*fx-fp)/(*stp-*stx)+*dx+dp;s=fmax(fabs(theta),fmax(fabs(*dx),fabs(dp)));
  gamma=s*sqrt((theta/s)*(theta/s)-(*dx/s)*(dp/s));if(*stp>*stx)gamma=-gamma;
  p=(gamma-dp)+theta;q=((gamma-dp)+gamma)+*dx;r=p/q;stpc=*stp+r*(*stx-*stp);
  stpq=*stp+(dp/(dp-*dx))*(*stx-*stp);stpf=fabs(stpc-*stp)>fabs(stpq-*stp)?stpc:stpq;*brackt=1;
 }else if(fabs(dp)<fabs(*dx)){
  theta=3*(*fx-fp)/(*stp-*stx)+*dx+dp;s=fmax(fabs(theta),fmax(fabs(*dx),fabs(dp)));
  gamma=s*sqrt(fmax(0,(theta/s)*(theta/s)-(*dx/s)*(dp/s)));if(*stp>*stx)gamma=-gamma;
  p=(gamma-dp)+theta;q=(gamma+(*dx-dp))+gamma;r=p/q;
  stpc=(r<0&&gamma!=0)?*stp+r*(*stx-*stp):(*stp>*stx?hi:lo);
  stpq=*stp+(dp/(dp-*dx))*(*stx-*stp);
  if(*brackt){stpf=fabs(stpc-*stp)<fabs(stpq-*stp)?stpc:stpq;
   stpf=*stp>*stx?fmin(*stp+.66*(*sty-*stp),stpf):fmax(*stp+.66*(*sty-*stp),stpf);
  }else {stpf=fabs(stpc-*stp)>fabs(stpq-*stp)?stpc:stpq;stpf=clip(stpf,lo,hi);}
 }else{
  if(*brackt){theta=3*(fp-*fy)/(*sty-*stp)+*dy+dp;s=fmax(fabs(theta),fmax(fabs(*dy),fabs(dp)));
   gamma=s*sqrt((theta/s)*(theta/s)-(*dy/s)*(dp/s));if(*stp>*sty)gamma=-gamma;
   p=(gamma-dp)+theta;q=((gamma-dp)+gamma)+*dy;r=p/q;stpf=*stp+r*(*sty-*stp);
  }else stpf=*stp>*stx?hi:lo;
 }
 if(fp>*fx){*sty=*stp;*fy=fp;*dy=dp;}else{if(sgnd<0){*sty=*stx;*fy=*fx;*dy=*dx;}*stx=*stp;*fx=fp;*dx=dp;}
 *stp=stpf;
}
int cn_more_thuente(const CNBackend*b,const CNOracle*o,const double*x,double f0,
 const double*g0,const double*d,double initial,const CNLineParams*p,double*xnew,
 double*fnew,double*gnew,double*w){
 int n=o->n,brackt=0,stage=1,nfev=0,best=0,finite_retry=0,seen_finite=0;
 double ginit=cn_dot(b,n,g0,d),gtest=p->c1*ginit;
 if(!isfinite(f0)||!isfinite(ginit)||ginit>=0)return 0;
 double stp=clip(initial,p->stpmin,p->stpmax),upper=p->stpmax;
 double width=upper-p->stpmin,width1=width/.5,stx=0,sty=0,fx=f0,fy=f0,gx=ginit,gy=ginit;
 double stmin=0,stmax=stp+4*stp,bestf=INFINITY;
 double *xt=w,*gt=w+n,*bestx=w+2*n,*bestg=w+3*n;
 for(;;){
  double f,g;for(int i=0;i<n;i++)xt[i]=x[i]+stp*d[i];
  if(o->fg(o->context,xt,&f,gt))return CN_CALLBACK;
  nfev++;g=cn_dot(b,n,gt,d);
  if(!isfinite(f)||!isfinite(g)){
   if((seen_finite&&nfev>=p->maxfev)||finite_retry++>=52||stp==stx)break;
   upper=fmin(upper,stp);stp=.5*(stp+stx);continue;
  }
  finite_retry=0;seen_finite=1;
  double ftest=f0+stp*gtest;
  if(f<=ftest&&f<bestf){best=1;bestf=f;memcpy(bestx,xt,(size_t)n*sizeof(double));memcpy(bestg,gt,(size_t)n*sizeof(double));}
  if(stage==1&&f<=ftest&&g>=0)stage=2;
  if(f<=ftest&&fabs(g)<=p->c2*(-ginit)){
   memcpy(xnew,xt,(size_t)n*sizeof(double));memcpy(gnew,gt,(size_t)n*sizeof(double));*fnew=f;return 1;
  }
  if((brackt&&(stp<=stmin||stp>=stmax))||(brackt&&stmax-stmin<=p->xtol*stmax)||
    (stp==upper&&f<=ftest&&g<=gtest)||(stp==p->stpmin&&(f>ftest||g>=gtest))||nfev>=p->maxfev)break;
  if(stage==1&&f<=fx&&f>ftest){
   double fm=f-stp*gtest,fxm=fx-stx*gtest,fym=fy-sty*gtest,gm=g-gtest,gxm=gx-gtest,gym=gy-gtest;
   dcstep(&stx,&fxm,&gxm,&sty,&fym,&gym,&stp,fm,gm,&brackt,stmin,stmax);
   fx=fxm+stx*gtest;fy=fym+sty*gtest;gx=gxm+gtest;gy=gym+gtest;
  }else dcstep(&stx,&fx,&gx,&sty,&fy,&gy,&stp,f,g,&brackt,stmin,stmax);
  if(!isfinite(stp))break;
  if(brackt){if(fabs(sty-stx)>=.66*width1)stp=stx+.5*(sty-stx);width1=width;width=fabs(sty-stx);}
  if(brackt){stmin=fmin(stx,sty);stmax=fmax(stx,sty);}else{stmin=stp+1.1*(stp-stx);stmax=stp+4*(stp-stx);}
  stp=clip(stp,p->stpmin,upper);
  if(brackt&&((stp<=stmin||stp>=stmax)||stmax-stmin<=p->xtol*stmax))stp=stx;
 }
 if(best&&p->allow_armijo_fallback){memcpy(xnew,bestx,(size_t)n*sizeof(double));memcpy(gnew,bestg,(size_t)n*sizeof(double));*fnew=bestf;return 1;}return 0;
}

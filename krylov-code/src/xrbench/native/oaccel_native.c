/* O-ACCEL-B, Riseth (2019), equations (3),(10),(21),(30), Algorithm 1.
   Author audit: https://github.com/anriseth/objective_accel_code/ngmres_o.m
   History is expressed relative to the current iterate to avoid cancellation
   under a common translation. Cached D'E follows exact rank-two translations;
   periodic/direct cancellation refreshes preserve equation (10). No gradients
   outside CNOracle are evaluated. */
#include "competitor_common.h"
#include <math.h>
#include <stdlib.h>
#include <string.h>
static void cross(const CNBackend*b,int n,int p,const double*D,const double*E,double*Q,int m){
 char t='T',z='N';double one=1,zero=0;b->blas.dgemm(&t,&z,&p,&p,&n,&one,(double*)D,&n,(double*)E,&n,&zero,Q,&m);
}
int cn_oaccel_execute(const CNParams*p,const CNBackend*b,const CNOracle*o,const double*x0){
 int n=o->n,m=cn_int(p,"wmax",20),precond=cn_int(p,"precond_A",0),maxfev=cn_int(p,"maxfev",20);
 double delta=cn_get(p,"delta",1e-4),eps0=cn_get(p,"eps0",1e-12);
 CNLineParams ls={cn_get(p,"c1",1e-4),cn_get(p,"c2",.1),cn_get(p,"xtol",1e-8),cn_get(p,"stpmin",1e-16),cn_get(p,"stpmax",65536),maxfev,1};
 if(m<1||m>10000||maxfev<1||!(delta>0&&eps0>=0&&ls.c1>0&&ls.c1<ls.c2&&ls.c2<1&&ls.stpmin>=0&&ls.stpmax>ls.stpmin&&ls.xtol>=0))return CN_INVALID;
 /* Persistent histories/cache and all trial/solve vectors allocated once. */
 double*buf=calloc((size_t)(4*m+17)*n+(size_t)2*m*m+5*m,sizeof(double));int*piv=calloc((size_t)m,sizeof(int));
 if(!buf||!piv){free(buf);free(piv);return CN_MEMORY;}
 double*x=buf,*g=x+n,*xp=g+n,*gp=xp+n,*xa=gp+n,*gn=xa+n,*d=gn+n,*s=d+n,*y=s+n,*work=y+n;
 double*D=work+4*n,*E=D+(size_t)n*m,*DP=E+(size_t)n*m,*EP=DP+(size_t)n*m;
 double*Q=EP+(size_t)n*m,*A=Q+(size_t)m*m,*rhs=A+(size_t)m*m,*a=rhs+m,*bb=a+m;
 double f,fp,fn;int status=CN_OK,curw=1,k=0,iter=0;long restarts=0,ls_fail_acc=0,ls_fail_pre=0;
 memcpy(x,x0,(size_t)n*sizeof(double));
 if(o->fg(o->context,x,&f,g)){status=CN_CALLBACK;goto finish;}
 if(!isfinite(f)||!cn_finite(n,g)){if(o->stop(o->context,"non-finite f or g at x0"))status=CN_CALLBACK;goto finish;}
 for(;;){
  double gnorm=cn_norm(b,n,g);if(gnorm==0){if(o->stop(o->context,"g = 0"))status=CN_CALLBACK;break;}
  iter++;k++;int moved=1,restart=0,ls_ok=0;
  if(precond){for(int i=0;i<n;i++)d[i]=-g[i]/gnorm;
   int r=cn_more_thuente(b,o,x,f,g,d,1,&ls,xp,&fp,gp,work);if(r<0){status=r;break;}moved=r;
   if(!r){memcpy(xp,x,(size_t)n*sizeof(double));memcpy(gp,g,(size_t)n*sizeof(double));fp=f;}
  }else{
   double step=fmin(delta,gnorm)/gnorm;for(int i=0;i<n;i++)xp[i]=x[i]-step*g[i];
   if(o->fg(o->context,xp,&fp,gp)){status=CN_CALLBACK;break;}
   int retry=0;while(!isfinite(fp)&&retry++<52){step*=.5;for(int i=0;i<n;i++)xp[i]=x[i]-step*g[i];if(o->f(o->context,xp,&fp)){status=CN_CALLBACK;goto finish;}if(isfinite(fp)&&o->g(o->context,xp,gp)){status=CN_CALLBACK;goto finish;}}
   if(!isfinite(fp)||!cn_finite(n,gp)){moved=0;memcpy(xp,x,(size_t)n*sizeof(double));memcpy(gp,g,(size_t)n*sizeof(double));fp=f;}
  }
  if(!moved){ls_fail_pre++;if(o->note(o->context,"ls_fail_pre",(double)ls_fail_pre)){status=CN_CALLBACK;break;}}
  for(int i=0;i<n;i++){s[i]=xp[i]-x[i];y[i]=gp[i]-g[i];}
  if(iter%32==0)cross(b,n,curw,D,E,Q,m);
  double c=cn_dot(b,n,s,y), sgp=cn_dot(b,n,s,gp);int refresh=0;
  for(int j=0;j<curw;j++){
   a[j]=cn_dot(b,n,D+(size_t)j*n,y);bb[j]=cn_dot(b,n,s,E+(size_t)j*n);
   rhs[j]=-cn_dot(b,n,D+(size_t)j*n,gp)+sgp;
   for(int i=0;i<n;i++)DP[i+(size_t)j*n]=D[i+(size_t)j*n]-s[i];
  }
  for(int j=0;j<curw;j++)for(int i=0;i<curw;i++)A[i+(size_t)j*curw]=Q[i+(size_t)j*m]-a[i]-bb[j]+c;
  for(int j=0;j<curw;j++)if(fabs(A[j+(size_t)j*curw])<1e-8*(fabs(Q[j+(size_t)j*m])+fabs(a[j])+fabs(bb[j])+fabs(c)))refresh=1;
  if(refresh){for(int j=0;j<curw;j++)for(int i=0;i<n;i++)EP[i+(size_t)j*n]=E[i+(size_t)j*n]-y[i];cross(b,n,curw,DP,EP,A,curw);}
  double maxdiag=-INFINITY;for(int j=0;j<curw;j++)maxdiag=fmax(maxdiag,A[j+(size_t)j*curw]);
  double shift=eps0*fmax(maxdiag,eps0);for(int j=0;j<curw;j++)A[j+(size_t)j*curw]+=shift;
  int one=1,info;b->blas.dgesv(&curw,&one,A,&curw,piv,rhs,&curw,&info);
  int has_xa=!info&&cn_finite(curw,rhs);memset(d,0,(size_t)n*sizeof(double));
  if(has_xa){char nt='N';double alpha=1,beta=0;b->blas.dgemv(&nt,&n,&curw,&alpha,DP,&n,rhs,&one,&beta,d,&one);for(int i=0;i<n;i++)xa[i]=xp[i]+d[i];}
  else restart=1;
  double slope=cn_dot(b,n,d,gp);
  if(!isfinite(slope)||slope>=0)restart=1;
  if(!restart){int r=cn_more_thuente(b,o,xp,fp,gp,d,1,&ls,xa,&fn,gn,work);if(r<0){status=r;break;}if(r)ls_ok=1;else{restart=1;ls_fail_acc++;if(o->note(o->context,"ls_fail_acc",(double)ls_fail_acc)){status=CN_CALLBACK;break;}}}
  if(!ls_ok){memcpy(xa,xp,(size_t)n*sizeof(double));memcpy(gn,gp,(size_t)n*sizeof(double));fn=fp;}
  if(restart){restarts++;if(o->note(o->context,"restarts",(double)restarts)){status=CN_CALLBACK;break;}}
  if(o->mark(o->context)){status=CN_CALLBACK;break;}
  if(o->trace){CNParam items[]={{"iteration",iter},{"curw",curw},{"restart",restart},{"ls_ok",ls_ok}};CNTrace tr={"oaccel",items,4,xa,gn,xp,NULL};
   /* x_A is the proposed acceleration before globalization, reconstructed
      from immutable DP and solved coefficients (xa may be the accepted point). */
   if(has_xa){for(int i=0;i<n;i++)d[i]=xp[i];for(int j=0;j<curw;j++)for(int i=0;i<n;i++)d[i]+=DP[i+(size_t)j*n]*rhs[j];tr.x_A=d;}
   if(o->trace(o->context,&tr)){status=CN_CALLBACK;break;}}
  int unchanged=!memcmp(x,xa,(size_t)n*sizeof(double));
  for(int i=0;i<n;i++){s[i]=xa[i]-x[i];y[i]=gn[i]-g[i];}
  if(restart){k=0;curw=1;memset(D,0,(size_t)n*m*sizeof(double));memset(E,0,(size_t)n*m*sizeof(double));memset(Q,0,(size_t)m*m*sizeof(double));}
  else{
   c=cn_dot(b,n,s,y);for(int j=0;j<curw;j++){a[j]=cn_dot(b,n,D+(size_t)j*n,y);bb[j]=cn_dot(b,n,s,E+(size_t)j*n);}
   for(int j=0;j<curw;j++)for(int i=0;i<curw;i++)Q[i+(size_t)j*m]+=c-a[i]-bb[j];
   for(int j=0;j<curw;j++)for(int i=0;i<n;i++){D[i+(size_t)j*n]-=s[i];E[i+(size_t)j*n]-=y[i];}
   if(curw<m)curw++;int j=k%m;memset(D+(size_t)j*n,0,(size_t)n*sizeof(double));memset(E+(size_t)j*n,0,(size_t)n*sizeof(double));
   for(int i=0;i<curw;i++){Q[i+(size_t)j*m]=0;Q[j+(size_t)i*m]=0;}
  }
  memcpy(x,xa,(size_t)n*sizeof(double));memcpy(g,gn,(size_t)n*sizeof(double));f=fn;
  if(unchanged){if(o->stop(o->context,"x unchanged over an iteration (Optim.jl x_abstol = 0)"))status=CN_CALLBACK;break;}
 }
 finish:free(buf);free(piv);return status;
}

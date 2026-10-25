"""Untrusted value-polynomial proposals for the complete contact integral.

The actual filters and root are enclosed by the proved reference trajectory
and root residuals. This routine supplies polynomial witnesses only: its
floating-point summaries and its own interval calculations prove nothing.
"""
import sys
sys.dont_write_bytecode=True
import argparse
from bisect import bisect_right
from fractions import Fraction as F
import json
from pathlib import Path
import re
from .IntegerIntervals import Bounds,outward,ceil_div
from .ResidualPrograms import Polynomials,PolynomialProgram
from .FetchCertificate import ROOT,load_source,fetch
from .PrepareCertificate import prepare_payload,numeric_tokens,exact_number


def compose(P,cs,u):
    """
    Compose a polynomial DAG with the supplied polynomial input by Horner evaluation.
    Coefficients are registered as literal nodes.
    """
    out=[]
    for c in reversed(cs):
        out=P.add([Bounds(c,c)],P.mul(u,out))
        while out and out[-1]==Bounds(0,0):out.pop()
    return out


def contact_program(sigma,inputs,bits,cap):
    """
    Build the denominator, speed and integrated-contact residual expressions with the exact
    operation order required by ContactExpr.
    """
    P=PolynomialProgram(bits,inputs,cap)
    t,pi,r,l,u,g=-1,-2,-3,-4,-5,-6
    tc=P.power(t,3);h=P.sub(P.literal(2),tc);Q=P.mul(tc,h)
    D=P.add(P.literal(2),P.mul(P.literal(sigma),P.add(l,u)))
    V=P.sub(P.mul(P.mul(P.literal(F(1,4)),P.power(pi,2)),P.power(r,2)),P.mul(t,h))
    G=P.sub(P.mul(Q,P.add(l,u)),P.mul(P.literal(2),P.mul(l,u)))
    N=P.mul(P.literal(3),P.sub(P.mul(P.literal(2),G),
                             P.mul(P.add(P.power(l,2),P.power(u,2)),D)))
    E=P.sub(N,P.mul(g,P.mul(D,V)))
    return P,dict(den=D,speed=V,residual=E)


class Series:
    """
    Exact rational series, used only to propose an approximate integrand.
    """
    def __init__(self,n):
        """
        Choose the Taylor-series degree retained by the local proposal arithmetic.
        """
        self.n=n
    def add(self,a,b):
        """
        Add Taylor series coefficientwise, padding missing coefficients with zero through the
        fixed degree.
        """
        return [(a[i] if i<len(a) else F(0))+(b[i] if i<len(b) else F(0))
                for i in range(min(self.n,max(len(a),len(b))))]
    def neg(self,a):
        """
        Negate each series coefficient.
        """
        return [-v for v in a]
    def sub(self,a,b):
        """
        Subtract Taylor series via negation and addition.
        """
        return self.add(a,self.neg(b))
    def mul(self,a,b):
        """
        Compute the finite coefficient convolution through the fixed degree; this is proposal
        arithmetic, not a certified remainder bound.
        """
        out=[F(0)]*min(self.n,len(a)+len(b)-1)
        for i,v in enumerate(a):
            for j,w in enumerate(b[:max(0,self.n-i)]):out[i+j]+=v*w
        return out
    def div(self,a,b):
        """
        Solve the coefficient recurrence for series division, requiring a nonzero constant
        denominator.
        """
        if not b or not b[0]:raise ValueError('Zero proposed series denominator')
        out=[]
        for i in range(self.n):
            out.append(((a[i] if i<len(a) else 0)-
                        sum(b[j]*out[i-j] for j in range(1,min(i+1,len(b)))))/b[0])
        return out
    def compose(self,cs,u):
        """
        Compose a polynomial with a truncated Taylor series through Horner evaluation.
        """
        out=[]
        for c in reversed(cs):out=self.add([c],self.mul(u,out))
        return out


def proposed_integrand(sigma,t,z,l,u,n):
    """
    Propose Taylor coefficients of the contact integrand from local reference jets and filter
    polynomials. Certified model correspondence and residual bounds are established by
    VerifyContact.
    """
    P=Series(n)
    tc=P.mul(P.mul(t,t),t);h=P.sub([F(2)],tc);Q=P.mul(tc,h)
    D=P.add([F(2)],P.mul([sigma],P.add(l,u)))
    pi=F(314159265358979323846264338327950288419716939937510,10**50)
    V=P.sub(P.mul([pi*pi/4],P.mul(z,z)),P.mul(t,h))
    G=P.sub(P.mul(Q,P.add(l,u)),P.mul([F(2)],P.mul(l,u)))
    N=P.mul([F(3)],P.sub(P.mul([F(2)],G),P.mul(P.add(P.mul(l,l),P.mul(u,u)),D)))
    return P.div(N,P.mul(D,V))


def generate(payload,bits=144,limit=None):
    """
    Construct all contact-panel polynomial proposals and their shared residual DAG from the
    pinned trajectory. The output records models and candidate coefficients; Lean supplies
    acceptance.
    """
    S=1<<bits;P=Polynomials(bits)
    reference=list(map(exact_number,numeric_tokens((payload/'embedded/reference/reference.txt').read_text())))
    source=ROOT/'chebyshev2/Certificates/Compact/ReferenceResidualBatches'
    pattern=re.compile(r'^noncomputable def row(\d+) : ResidualCell.Row := ⟨'
        r'(-?\d+),(\d+),(\d+),(true|false),\[([^]]*)\],\[([^]]*)\],\((\d+)/(\d+):ℚ\)')
    rows={}
    for path in sorted(source.glob('Data*.lean')):
        for line in path.read_text().splitlines():
            if not line.startswith('noncomputable def row'):continue
            match=pattern.match(line)
            if not match:raise ValueError('Unexpected reference row source')
            i,a,w,step,refl,p,z,d,den=match.groups()
            row=dict(index=int(i),start=int(a),width=int(w),step=int(step),
                     reflected=refl=='true',p=list(map(int,p.split(','))),
                     z=list(map(int,z.split(','))),delta=F(int(d),int(den)))
            if int(i) in rows:raise ValueError('Duplicate source row')
            rows[int(i)]=row
    if sorted(rows)!=list(range(2519)):raise ValueError('Incomplete source rows')
    if any(r['width']*r['step']!=S for r in rows.values()):raise ValueError('Wrong source scale')
    left=[rows[i] for i in range(1228)]
    # Right row indices are ordered in physical t, not their forward chart v.
    right=[rows[i] for i in reversed(range(1228,2519))]
    leftstarts=[r['start'] for r in left]
    rightstarts=[2*S-r['start']-r['width'] for r in right]
    endpoints=sorted(set(leftstarts+rightstarts+[S]))
    if endpoints[0]!=0 or endpoints[-1]!=S:raise ValueError('Incomplete quadrature domain')
    pi=outward(F(314159265358979323846264338327950288419716939937510,10**50),
                F(314159265358979323846264338327950288419716939937511,10**50),S)
    leftError=ceil_div(S*2,10**14);rightError=ceil_div(S*4,10**14)
    epsilon=F(1,10**10);output=[];maximum=F(0);integral=F(0);ops=None
    pairs=list(zip(endpoints,endpoints[1:]))
    for index,(a,b) in enumerate(pairs[:limit]):
        L=left[bisect_right(leftstarts,a)-1];R=right[bisect_right(rightstarts,a)-1]
        if not L['start']<=a<b<=L['start']+L['width']:raise ValueError('Left containment')
        if not R['start']<=2*S-b<2*S-a<=R['start']+R['width']:raise ValueError('Right containment')
        ul=[(a-L['start'])*L['step'],(b-a)*L['step']]
        ur=[(2*S-a-R['start'])*R['step'],-(b-a)*R['step']]
        ub=lambda cs:[Bounds(c,c) for c in cs]
        z=compose(P,L['z'],ub(ul));l=compose(P,L['p'],ub(ul));u=compose(P,R['p'],ub(ur))
        delta=ceil_div(L['delta'].numerator*S,L['delta'].denominator)
        models=[ub([a,b-a]),[pi],P.add([Bounds(-delta,delta)],z),
                P.add([Bounds(-leftError,leftError)],l),P.add([Bounds(-rightError,rightError)],u)]
        ser=Series(8)
        lq=ser.compose([F(v,S) for v in L['p']],[F(v,S) for v in ul])
        uq=ser.compose([F(v,S) for v in R['p']],[F(v,S) for v in ur])
        zq=ser.compose([F(v,S) for v in L['z']],[F(v,S) for v in ul])
        g=[round(v*S) for v in proposed_integrand(reference[1],[F(a,S),F(b-a,S)],zq,lq,uq,8)]
        for cap in (6,8,10):
            program,outputs=contact_program(reference[1],models+[ub(g)],bits,cap)
            ranges={k:P.range(program.interval(j)) for k,j in outputs.items()}
            D,V,E=ranges['den'],ranges['speed'],ranges['residual']
            if min(D.lo,V.lo)<=0:continue
            error=F(max(-E.lo,E.hi)*S,D.lo*V.lo)
            if error<=epsilon:break
        else:raise ValueError(f'Unaccepted proposed contact panel {index}: {float(error)}')
        if ops is None:ops=program.lean_ops()
        if ops!=program.lean_ops():raise ValueError('Changed contact expression graph')
        maximum=max(maximum,error)
        integral+=F(b-a,S)*sum(F(c,S*(i+1)) for i,c in enumerate(g))
        output.append(dict(start=a,width=b-a,left=L['index'],right=R['index'],
                           ul=ul,ur=ur,g=g,degree=cap,
                           models=[[[v.lo,v.hi] for v in model] for model in models]))
        if (index+1)%256==0:print(f'Proposed {index+1}/{len(pairs)} contact panels',flush=True)
    return dict(format='UNTRUSTED_CONTACT_VALUE_POLYNOMIALS_1',bits=bits,epsilon=str(epsilon),
                panels=output,ops=ops,maximum_proposed_error=str(maximum),
                proposed_integral=str(integral),full_cover=len(output)==len(pairs))


def main():
    """
    Generate and save contact proposals under .lake. This command does not install theorem
    assumptions or assert a mathematical acceptance result.
    """
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--offline',action='store_true');parser.add_argument('--limit',type=int)
    args=parser.parse_args();descriptor=load_source(ROOT/'chebyshev2/Certificates/Source.json')
    receipt=fetch(descriptor,ROOT/'.lake/certificates/chebyshev2',args.offline)
    archive=Path(receipt['archive']);payload,_=prepare_payload(archive,archive.parent)
    proposal=generate(payload,limit=args.limit)
    folder=ROOT/'.lake/certificates/chebyshev2/compact-contact';folder.mkdir(exist_ok=True,parents=True)
    (folder/'proposals.json').write_text(json.dumps(proposal,separators=(',',':'))+'\n')
    print(json.dumps(dict(status='PROPOSED_ONLY',panels=len(proposal['panels']),
        maximum_proposed_error=float(F(proposal['maximum_proposed_error'])),
        proposed_integral=float(F(proposal['proposed_integral'])),
        kernel_accepted=False),indent=2),flush=True)


if __name__=='__main__':main()

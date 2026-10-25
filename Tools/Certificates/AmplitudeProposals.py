"""Untrusted cancellation-preserving amplitude-integral polynomials."""
import sys
sys.dont_write_bytecode=True
import json
from fractions import Fraction as F
from pathlib import Path
from .ContactProposals import Series
from .IntegerIntervals import Bounds
from .ResidualPrograms import PolynomialProgram,Polynomials
from .FetchCertificate import ROOT,load_source,fetch
from .PrepareCertificate import prepare_payload,numeric_tokens,exact_number


def root_series(P,a,b,k,bits):
    """
    Propose the positive root of k*r^3-a*r-b; all checks are elsewhere.
    """
    S=1<<bits;lo=0;hi=S
    f=lambda x:k*F(x,S)**3-a[0]*F(x,S)-b[0]
    while f(hi)<=0:hi*=2
    while hi-lo>1:
        mid=(lo+hi)//2
        if f(mid)<0:lo=mid
        else:hi=mid
    out=[F(lo+hi,2*S)];slope=3*k*out[0]**2-a[0]
    if slope<=0:raise ValueError('Nonpositive proposed root-series slope')
    for n in range(1,P.n):
        cube=P.mul(P.mul(out,out),out)
        ax=P.mul(a,out)
        residual=k*(cube[n] if n<len(cube) else 0)-(ax[n] if n<len(ax) else 0)-(b[n] if n<len(b) else 0)
        out.append(-residual/slope)
    return out


def amplitude_program(sigma,base,omega,inputs,bits,cap):
    """
    Build the calibration-root and amplitude-quadrature residual DAG using the same
    panel/reference inputs as the contact certificate.
    """
    P=PolynomialProgram(bits,inputs,cap)
    H,g,t,pi,l,u=-1,-2,-3,-4,-6,-7
    tc=P.power(t,3);h=P.sub(P.literal(2),tc);Q=P.mul(tc,h)
    k=P.mul(P.literal(F(1,4)),P.power(pi,2))
    D=P.add(P.literal(2),P.mul(P.literal(sigma),P.add(l,u)))
    G=P.sub(P.mul(Q,P.add(l,u)),P.mul(P.literal(2),P.mul(l,u)))
    z=P.mul(t,H)
    root=P.sub(P.mul(D,P.sub(P.sub(P.mul(k,P.power(z,3)),P.mul(P.literal(3),P.mul(Q,z))),
                          P.mul(P.literal(2*base),Q))),P.mul(P.mul(P.literal(2*omega),k),G))
    quad=P.sub(g,P.mul(P.literal(6),P.mul(tc,H)))
    return P,dict(k=k,den=D,root=root,quad=quad)


def main():
    """
    Load the pinned reference and contact proposals, compute amplitude-panel proposals, and
    save them under .lake for VerifyAmplitude. No result is accepted solely by this Python
    computation.
    """
    descriptor=load_source(ROOT/'chebyshev2/Certificates/Source.json')
    receipt=fetch(descriptor,ROOT/'.lake/certificates/chebyshev2',True)
    archive=Path(receipt['archive']);payload,_=prepare_payload(archive,archive.parent)
    reference=list(map(exact_number,numeric_tokens((payload/'embedded/reference/reference.txt').read_text())))
    contact=json.loads((ROOT/'.lake/certificates/chebyshev2/compact-contact/proposals.json').read_text())
    bits=contact['bits'];S=1<<bits;PA=Polynomials(bits);proposals=[];maximum=F(0);total=F(0)
    pi=F(314159265358979323846264338327950288419716939937510,10**50);k=pi*pi/4
    ops=None
    for i,row in enumerate(contact['panels']):
        P=Series(13);models=[[Bounds(*v) for v in m] for m in row['models']]
        t=[F(row['start'],S),F(row['width'],S)]
        l=[F(v.lo+v.hi,2*S) for v in models[3]];u=[F(v.lo+v.hi,2*S) for v in models[4]]
        tc=P.mul(P.mul(t,t),t);h=P.sub([F(2)],tc);Q=P.mul(tc,h)
        D=P.add([F(2)],P.mul([reference[1]],P.add(l,u)))
        G=P.sub(P.mul(Q,P.add(l,u)),P.mul([F(2)],P.mul(l,u)))
        gamma=P.div(G,D)
        if row['start']==0:
            gammaOverCube=gamma[3:]+[F(0)]*3
            gammaOverCube=[v/(t[1]**3) for v in gammaOverCube]
        else:gammaOverCube=P.div(gamma,tc)
        alpha=P.mul([F(3)],P.mul(t,h))
        beta=P.add(P.mul([2*reference[2]],h),P.mul([2*k*reference[3]],gammaOverCube))
        H=[round(v*S) for v in root_series(Series(8),alpha,beta,k,bits)]
        Hq=[F(v,S) for v in H]
        g=[round(v*S) for v in P.mul([F(6)],P.mul(tc,Hq))]
        contactG=[Bounds(v,v) for v in row['g']]
        # Reuse the entire contact prefix, including its unused approximation.
        inputModels=[[Bounds(v,v) for v in H],[Bounds(v,v) for v in g]]+models+[contactG]
        for cap in (6,8,10,13):
            program,outputs=amplitude_program(reference[1],reference[2],reference[3],inputModels,bits,cap)
            ranges={key:PA.range(program.interval(j)) for key,j in outputs.items()}
            K,D,E,T=ranges['k'],ranges['den'],ranges['root'],ranges['quad']
            lower=PA.range(inputModels[0]).lo
            if min(K.lo,D.lo)<=0 or lower<S//2:continue
            err=F(24*max(-E.lo,E.hi)*S,D.lo*K.lo)+F(max(-T.lo,T.hi),S)
            if err<=F(1,10**10):break
        else:raise ValueError(f'Unaccepted proposed amplitude panel {i}: {float(err)}')
        if ops is None:ops=program.lean_ops()
        if ops!=program.lean_ops():raise ValueError('Changed amplitude graph')
        maximum=max(maximum,err);total+=F(row['width'],S)*sum(F(c,S*(j+1)) for j,c in enumerate(g))
        proposals.append(dict(start=row['start'],width=row['width'],left=row['left'],right=row['right'],
                              H=H,g=g,degree=cap,models=[[[v.lo,v.hi] for v in m] for m in inputModels]))
        if (i+1)%256==0:print('Proposed amplitude panels:',i+1,flush=True)
    output=dict(format='UNTRUSTED_AMPLITUDE_VALUE_POLYNOMIALS_1',bits=bits,panels=proposals,ops=ops,
                maximum_proposed_error=str(maximum),proposed_integral=str(total),kernel_accepted=False)
    folder=ROOT/'.lake/certificates/chebyshev2/compact-amplitude';folder.mkdir(exist_ok=True,parents=True)
    (folder/'proposals.json').write_text(json.dumps(output,separators=(',',':'))+'\n')
    print(json.dumps(dict(status='PROPOSED_ONLY',panels=len(proposals),maximum_proposed_error=float(maximum),
                         proposed_integral=float(total),kernel_accepted=False),indent=2),flush=True)


if __name__=='__main__':main()

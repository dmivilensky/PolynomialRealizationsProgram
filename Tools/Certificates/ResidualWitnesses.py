"""Generate untrusted reference residual witnesses for the batch verifier.

The batch verifier connects all actual ODE cells, initial values and seams.
"""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as F
import json

from .FetchCertificate import ROOT
from .PrepareCertificate import numeric_tokens,exact_number
from .IntegerIntervals import Bounds,outward,ceil_div
from .ResidualPrograms import residual_polynomials,residual_program,Polynomials


def integers(xs):
    """
    Render integer coefficient data as a Lean list literal.
    """
    return '['+','.join(str(x) for x in xs)+']'


def generate(payload, cells, bits):
    """
    Emit reference-row polynomial/checkpoint data and kernel-decidable row/block acceptance
    claims. Inputs come from the pinned trajectory; the generated theorem bodies invoke the
    proved Lean checker.
    """
    ref=list(map(exact_number,numeric_tokens((payload/'embedded/reference/reference.txt').read_text())))
    lines=(payload/'data/reference/support-filter-flow.txt').read_text().splitlines()
    if lines[:2]!=['QUADRATIC_FLOW 1','128 12 2519'] or len(lines)!=45346:
        raise ValueError('Unexpected flow format')
    S=1<<bits
    pi=outward(F(314159265358979323846264338327950288419716939937510,10**50),
                F(314159265358979323846264338327950288419716939937511,10**50),S)
    rows=[]; ops=None; maximum=F(0)
    cache=ROOT/'.lake/certificates/chebyshev2/compact-residual/polynomial-proposals.json'
    proposals=json.loads(cache.read_text()) if cache.exists() else None
    if proposals and (proposals.get('format')!='UNTRUSTED_POLYNOMIAL_PROPOSALS_1' or
                      proposals.get('bits')!=bits or len(proposals.get('rows',[]))!=2519):
        proposals=None
    arithmetic=Polynomials(bits)
    for i in cells:
        off=3+18*i
        a,b=map(exact_number,lines[off].split())
        saved=[tuple(map(exact_number,line.split())) for line in lines[off+5:off+18]]
        if proposals:
            old=proposals['rows'][i]
            expected=arithmetic.midpoint((u+v)/2*(b-a)**j for j,(u,v) in enumerate(saved))
            if (old['start']!=a*S or old['width']!=(b-a)*S or old['step']!=1/(b-a) or
                old['reflected']!=(a>=1) or old['p']!=[v.lo for v in expected] or len(old['z'])!=13):
                raise ValueError('Proposal does not match the archive cell')
            z=[Bounds(v,v) for v in old['z']]
            pd=[Bounds(v.lo*j*old['step'],v.lo*j*old['step']) for j,v in enumerate(expected) if j]
            t0,dt=(2-a,a-b) if a>=1 else (a,b-a)
            r=dict(t=[outward(t0,t0,S),outward(dt,dt,S)],p=expected,z=z,pd=pd,
                   z_range=arithmetic.range(z),p_range=arithmetic.range(expected))
        else:
            r=residual_polynomials(ref,a,b,saved,bits)
        step=1/(b-a)
        if step.denominator!=1 or (a*S).denominator!=1 or ((b-a)*S).denominator!=1:
            raise ValueError('Non-dyadic cell')
        L,U=r['z_range'].lo,r['z_range'].hi
        for cap in (6,8,10,13):
            program,outputs=residual_program(ref,[r['t'],[pi],r['z'],r['p'],r['pd']],bits,cap)
            rng={key:program.polys.range(program.interval(j)) for key,j in outputs.items()}
            D,K=rng['den'].lo,rng['k'].lo
            if min(D,K,L)<=0:continue
            N=max(-rng['root'].lo,rng['root'].hi)
            delta=ceil_div(N*S**4,D*K*L*L)
            E=max(-rng['ode'].lo,rng['ode'].hi)
            G=max(-rng['factor'].lo,rng['factor'].hi)
            eta=F(6*(E*S*S+G*delta*(2*U+delta)),K*L*L)
            if 2*delta<=L and r['p_range'].lo>=0 and eta<=F(1,10**14):break
        else:raise ValueError(f'Cell {i} fails proposed budget: {float(eta)}')
        if ops is None:ops=program.lean_ops()
        if program.lean_ops()!=ops or len(program.nodes)!=81:
            raise ValueError('Inconsistent residual source graph')
        maximum=max(maximum,eta)
        p=[v.lo for v in r['p']]; z=[v.lo for v in r['z']]
        from collections import Counter
        consumers=Counter(k for (op,args),_ in program.nodes if op!='literal' for k in args if k>=0)
        selected={j for j,n in consumers.items() if n>1}|set(outputs.values())
        cps=[]
        for j,(_,model) in enumerate(program.nodes):
            cps.append('some ['+','.join(f'Poly.Taylor.box ({v.lo}) {v.hi-v.lo}' for v in model)+']'
                       if j in selected else 'none')
        checkpoints='['+','.join(cps)+']'
        rows.append(f'⟨{int(a*S)},{int((b-a)*S)},{int(step)},'
                    f'{str(a>=1).lower()},{integers(p)},{integers(z)},({delta}/{S}:ℚ),{cap},{checkpoints}⟩')
        if len(rows)%128==0: print(f'Proposed {len(rows)}/{len(cells)} residual witnesses',flush=True)
    text='''import chebyshev2.Numerics.IntegerResidualCell
import chebyshev2.Certificates.DualInputs.ReferenceModel
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace chebyshev2.Certificates.Compact.ReferenceResiduals
open chebyshev2.Numerics chebyshev2.Numerics.IntegerCertificate chebyshev2.Certificates.DualInputs
'''
    text+=f'noncomputable def scale : Nat := {S}\n'
    text+=f'noncomputable def piBounds : Bounds := ⟨{pi.lo},{pi.hi}⟩\n'
    text+=f'noncomputable def ops : List Op := {ops}\n'
    text+='noncomputable def eta : ℚ := 1/10^14\n'
    text+='''theorem pi_mem : piBounds.Mem scale Real.pi :=
  rationalIntervalCheck_sound (by decide +kernel)
    (a := piHigh.lo) (b := piHigh.hi) (by decide +kernel) mem_piHigh.1 mem_piHigh.2
theorem shapeK : codeExpressionCheck ops 72 ResidualExpr.k=true := by decide +kernel
theorem shapeD : codeExpressionCheck ops 30 (ResidualExpr.profileParts reference).1=true := by decide +kernel
theorem shapeRoot : codeExpressionCheck ops 16 (ResidualExpr.rootResidual reference)=true := by decide +kernel
theorem shapeFactor : codeExpressionCheck ops 12 ResidualExpr.factor=true := by decide +kernel
theorem shapeODE : codeExpressionCheck ops 0 (ResidualExpr.odeResidual sigma)=true := by decide +kernel
'''
    blocks=[]
    for j in range(0,len(rows),16):
        n=j//16; name=f'block{n}';blocks.append(name)
        indices=list(range(j,min(j+16,len(rows))))
        for i in indices:
            text+=f'noncomputable def row{i} : ResidualCell.Row := {rows[i]}\n'
            text+=f'theorem rowCheck{i} : ResidualCell.check scale ops piBounds eta row{i}=true := by decide +kernel\n'
        text+=f'noncomputable def {name} : List ResidualCell.Row := ['+','.join(f'row{i}' for i in indices)+']\n'
        text+=f'theorem checks{n} : {name}.all (ResidualCell.check scale ops piBounds eta)=true := by\n'
        text+=f'  simp only [{name},List.all_cons,List.all_nil,Bool.and_true'+(',Bool.and_eq_true' if len(indices)>1 else '')+']\n'
        proof=f'rowCheck{indices[-1]}'
        for i in reversed(indices[:-1]):proof=f'⟨rowCheck{i},{proof}⟩'
        text+='  exact '+proof+'\n'
        text+=f'''run_cmd do
  Lean.Elab.Command.liftIO <| IO.println "Kernel accepted {min(j+16,len(rows))}/{len(rows)} actual RHS residual cells"
  Lean.Elab.Command.liftIO <| (← IO.getStdout).flush
'''
    text+='noncomputable def rows : List ResidualCell.Row := '+ '++'.join(blocks)+'\n'
    text+='theorem combineChecked {as bs : List ResidualCell.Row}\n    (ha : ∀ r∈as,ResidualCell.check scale ops piBounds eta r=true)\n    (hb : ∀ r∈bs,ResidualCell.check scale ops piBounds eta r=true) :\n    ∀ r∈as++bs,ResidualCell.check scale ops piBounds eta r=true := by\n  intro r hr\n  rcases List.mem_append.mp hr with h|h\n  · exact ha r h\n  · exact hb r h\n\ntheorem checkedBlock (rs : List ResidualCell.Row)\n    (h : rs.all (ResidualCell.check scale ops piBounds eta)=true) :\n    ∀ r∈rs,ResidualCell.check scale ops piBounds eta r=true :=\n  List.all_eq_true.mp h\n\n'
    text+='theorem checks : ∀ r∈rows,ResidualCell.check scale ops piBounds eta r=true :=\n'
    proof='checkedBlock block0 checks0'
    for j in range(1,len(blocks)):proof=f'combineChecked ({proof}) (checkedBlock block{j} checks{j})'
    text+='  '+proof+'\n'
    text+='''theorem actual_rhs_residual {r : ResidualCell.Row} (hr : r∈rows)
    {x : ℝ} (hx : x∈Set.Icc (0:ℝ) 1)
    (ht : (ResidualCell.values scale r 0).eval x∈Set.Icc (0:ℝ) 1) :
    0≤(ResidualCell.values scale r 3).eval x ∧
    |(ReferenceJetSource.referenceData reference).normalizedVelocity ((ResidualCell.values scale r 0).eval x)*
      ((Real.pi^2/4)*(((ResidualCell.values scale r 0).eval x)*
        (ReferenceJetSource.referenceData reference).normalizedRoot ((ResidualCell.values scale r 0).eval x))^2-
        2*(ResidualCell.values scale r 3).eval x-(sigma:ℝ)*((ResidualCell.values scale r 3).eval x)^2)-
      (ResidualCell.values scale r 4).eval x|≤(eta:ℝ) :=
  ResidualCell.check_sound (by decide +kernel) pi_mem reference sigma eta
    shapeK shapeD shapeRoot shapeFactor shapeODE (checks r hr) hx ht
end chebyshev2.Certificates.Compact.ReferenceResiduals
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name,info) in env.constants.toList do
    if (`chebyshev2.Certificates.Compact.ReferenceResiduals).isPrefixOf (Lean.privateToUserName name) then
      if info.isUnsafe then throwError "unsafe residual declaration: {name}"
      for ax in ← Lean.collectAxioms name do
        unless [``propext,``Classical.choice,``Quot.sound].contains ax do
          throwError "forbidden residual axiom: {name}: {ax}"
'''
    return text,dict(cells=len(cells),maximum_proposed_eta=str(maximum),source_bytes=len(text.encode()))

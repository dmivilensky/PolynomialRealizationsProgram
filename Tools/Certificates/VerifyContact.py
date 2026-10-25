"""Kernel-check contact-integral value panels from the pinned archive.

Proposed models, their composition with the actual reference trajectories,
and the complete cleared-denominator residual are checked independently.
No saved quadrature result is used as a premise.
"""
import sys
sys.dont_write_bytecode=True
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor,as_completed
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import subprocess
import time
from .IntegerIntervals import Bounds,ceil_div
from .ContactProposals import contact_program
from .FetchCertificate import ROOT,load_source,fetch
from .PrepareCertificate import prepare_payload,numeric_tokens,exact_number


from .SourceWitnesses import install_source

def ints(xs):
    """
    Render the integer coefficients of a proposed contact polynomial as a Lean literal list.
    """
    return '['+','.join(map(str,xs))+']'
def model(xs):
    """
    Render interval coefficient bounds as Lean Taylor boxes using a lower endpoint and
    nonnegative width.
    """
    return '['+','.join(f'Poly.Taylor.box ({v.lo}) {v.hi-v.lo}' for v in xs)+']'


def generate(proposal,sigma,limit,check=False):
    """
    Emit the shared contact-expression program, per-panel model data and kernel-check
    propositions. Require agreement with the source program and recover root uncertainty from
    the checked reference row.
    """
    bits=proposal['bits'];S=1<<bits
    if bits!=144 or proposal['format']!='UNTRUSTED_CONTACT_VALUE_POLYNOMIALS_1':
        raise ValueError('Unsupported contact proposals')
    epsilon=F(1,10**12)
    prefix=ROOT/'chebyshev2/Certificates/Compact';folder=prefix/'ContactBatches';folder.mkdir(exist_ok=True)
    common='''set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace chebyshev2.Certificates.Compact.ContactValues
open chebyshev2.Numerics chebyshev2.Numerics.IntegerCertificate
'''
    shared='''import chebyshev2.Numerics.ContactModelSound
import chebyshev2.Numerics.ValueQuadrature
import chebyshev2.Certificates.Compact.ReferenceResidualShared
'''+common
    shared+='''noncomputable def scale : Nat := ReferenceResiduals.scale
noncomputable def piBounds : Bounds := ReferenceResiduals.piBounds
noncomputable def epsilon : ℚ := 1/10^12
'''
    shared+=f'noncomputable def leftRadius : Int := {ceil_div(S*2,10**14)}\n'
    shared+=f'noncomputable def rightRadius : Int := {ceil_div(S*4,10**14)}\n'
    shared+=f'noncomputable def ops : List Op := {proposal["ops"]}\n'
    shared+='''theorem shapeD : codeExpressionCheck ops 26 (ContactExpr.gammaDen DualInputs.sigma)=true := by decide +kernel
theorem shapeV : codeExpressionCheck ops 18 ContactExpr.speed=true := by decide +kernel
theorem shapeE : codeExpressionCheck ops 0 (ContactExpr.residual DualInputs.sigma)=true := by decide +kernel
end chebyshev2.Certificates.Compact.ContactValues
'''
    paths=[]
    def write(path,text):
        """
        Install or compare one generated source while retaining its maintained article
        overview.
        """
        install_source(path,text,check)
        paths.append(path)
    write(prefix/'ContactShared.lean',shared)
    panels=proposal['panels'][:limit]
    proofs=[]
    for begin in range(0,len(panels),32):
        number=begin//32;part=panels[begin:begin+32]
        reference_shards=sorted({p[key]//64 for p in part for key in ('left','right')})
        data='import chebyshev2.Certificates.Compact.ContactShared\n'
        for shard in reference_shards:
            data+=f'import chebyshev2.Certificates.Compact.ReferenceResidualBatches.Data{shard:03}\n'
        data+=common
        proof=f'import chebyshev2.Certificates.Compact.ContactBatches.Data{number:03}\n'+common
        for i,p in enumerate(part,begin):
            models=[[Bounds(*v) for v in m] for m in p['models']]+[[Bounds(c,c) for c in p['g']]]
            program,outputs=contact_program(sigma,models,bits,p['degree'])
            if program.lean_ops()!=proposal['ops']:raise ValueError('Changed source program')
            rng={k:program.polys.range(program.interval(v)) for k,v in outputs.items()}
            D,V,E=rng['den'],rng['speed'],rng['residual']
            if min(D.lo,V.lo)<=0 or F(max(-E.lo,E.hi)*S,D.lo*V.lo)>epsilon:
                raise ValueError('Failed proposed numerical budget')
            consumers=Counter(k for (op,args),_ in program.nodes if op!='literal' for k in args if k>=0)
            selected={j for j,n in consumers.items() if n>1}|set(outputs.values())
            cps='['+','.join('some '+model(m) if j in selected else 'none'
                for j,(_,m) in enumerate(program.nodes))+']'
            # The input uncertainty is recomputed from the reference row's
            # checked delta; the modelCheck below rejects any different value.
            # Composition rounding can widen the constant coefficient too.
            # Recover the radius directly from the reference source row.
            refpath=prefix/f'ReferenceResidualBatches/Data{p["left"]//64:03}.lean'
            import re
            line=next(x for x in refpath.read_text().splitlines()
                      if x.startswith(f'noncomputable def row{p["left"]} :'))
            match=re.search(r'\],\((\d+)/(\d+):ℚ\),',line)
            if match is None:raise ValueError('Missing reference root budget')
            rootRadius=ceil_div(int(match[1])*S,int(match[2]))
            row=f'⟨[{",".join(model(m) for m in models)}],{p["degree"]},{cps}⟩'
            data+=f'noncomputable def panel{i} : ContactPolynomial.Panel := '+f'''{{
  start := {p['start']}
  width := {p['width']}
  left := ReferenceResiduals.row{p['left']}
  right := ReferenceResiduals.row{p['right']}
  rootRadius := {rootRadius}
  g := {ints(p['g'])}
  row := {row}
}}
'''
            proof+=f'''theorem modelCheck{i} : panel{i}.modelCheck scale piBounds leftRadius rightRadius=true := by decide +kernel
theorem residualCheck{i} : ContactPolynomial.check scale ops epsilon panel{i}.row=true := by decide +kernel
'''
        name=f'block{number}'
        data+=f'noncomputable def {name} : List ContactPolynomial.Panel := ['+','.join(f'panel{i}' for i in range(begin,begin+len(part)))+']\n'
        data+='end chebyshev2.Certificates.Compact.ContactValues\n'
        proof+='end chebyshev2.Certificates.Compact.ContactValues\n'
        write(folder/f'Data{number:03}.lean',data)
        write(folder/f'Batch{number:03}.lean',proof)
        proofs.append(f'chebyshev2.Certificates.Compact.ContactBatches.Batch{number:03}')
    return paths,proofs,len(panels)


def main():
    """
    Compare regenerated contact witnesses or build/replay their batches. Full mathematical
    correspondence and coverage are proved in the separate contact proof/integral modules.
    """
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true',help='Compare installed witnesses without writing sources or replaying proofs')
    parser.add_argument('--offline',action='store_true');parser.add_argument('--limit',type=int,default=1291)
    parser.add_argument('--timeout',type=int,default=1800)
    parser.add_argument('--jobs',type=int,default=2,choices=[1,2])
    args=parser.parse_args();folder=ROOT/'.lake/certificates/chebyshev2/compact-contact'
    if args.check:
        descriptor=load_source(ROOT/'chebyshev2/Certificates/Source.json')
        receipt=fetch(descriptor,ROOT/'.lake/certificates/chebyshev2',args.offline)
        archive=Path(receipt['archive']);payload,_=prepare_payload(archive,archive.parent)
        reference=list(map(exact_number,numeric_tokens((payload/'embedded/reference/reference.txt').read_text())))
        proposal=json.loads((folder/'proposals.json').read_text())
        paths,_,count=generate(proposal,reference[1],args.limit,check=True)
        print(f'Compared {len(paths)} installed sources ({count} panels); no proof replay requested.',flush=True)
        return
    report=dict(status='RUNNING',accepted_contact_value_checks=0,actual_contact_integral_verified=False,
                scope="reference-only")
    path=folder/'report.json';start=time.monotonic()
    def save():
        """
        Write an operational progress report; this report is never a mathematical input.
        """
        path.write_text(json.dumps(report,indent=2)+'\n')
    def accept(module,label):
        """
        Build and independently kernel-replay one generated module, storing diagnostics under
        .lake.
        """
        for suffix,command in [('build',['lake','build','+'+module]),
            ('replay',['lake','env','lean','--run','Tools/Verification/Replay.lean',module])]:
            with (folder/f'{label}-{suffix}.log').open('w') as log:
                subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
    save()
    try:
        descriptor=load_source(ROOT/'chebyshev2/Certificates/Source.json')
        receipt=fetch(descriptor,ROOT/'.lake/certificates/chebyshev2',args.offline)
        archive=Path(receipt['archive']);payload,_=prepare_payload(archive,archive.parent)
        ref=list(map(exact_number,numeric_tokens((payload/'embedded/reference/reference.txt').read_text())))
        proposal=json.loads((folder/'proposals.json').read_text())
        paths,proofs,count=generate(proposal,ref[1],args.limit)
        report['generated_source_sha256']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
        tools=[Path(__file__).resolve(),ROOT/'Tools/Certificates/ContactProposals.py',
          ROOT/'Tools/Certificates/ResidualPrograms.py',ROOT/'Tools/Certificates/IntegerIntervals.py',
          ROOT/'chebyshev2/Certificates/Source.json']
        tools+=list((ROOT/'chebyshev2/Numerics').glob('Integer*.lean'))
        tools+=[ROOT/f'chebyshev2/Numerics/{n}.lean' for n in ('PolynomialIntegral','PolynomialAffine',
          'ReferenceValueBounds','ContactPolynomial','ContactCheck','ContactModels','ContactModelSound')]
        tools+=list((ROOT/'chebyshev2/Certificates/Compact/ReferenceResidualBatches').glob('Data*.lean'))
        report['tool_sha256']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in tools}
        save()
        accept('chebyshev2.Certificates.Compact.ContactShared','shared')
        def batch(i,module):
            """
            Check one contact batch with the same build/replay routine used for serial
            acceptance.
            """
            accept(module.replace('.Batch','.Data'),f'data-{i:03}')
            accept(module,f'batch-{i:03}')
            return min(32,count-i*32)
        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            futures=[executor.submit(batch,i,module) for i,module in enumerate(proofs)]
            for future in as_completed(futures):
                report['accepted_contact_value_checks']+=future.result();save()
                print(f'Kernel and fresh replay accepted {report["accepted_contact_value_checks"]}/{count} contact value checks',flush=True)
        for file,digest in {**report['generated_source_sha256'],**report['tool_sha256']}.items():
            if hashlib.sha256((ROOT/file).read_bytes()).hexdigest()!=digest:raise ValueError('Changed source: '+file)
        report['status']='CHECKS_PASS'
    except (OSError,ValueError,subprocess.SubprocessError) as error:
        report.update(status='FAIL',error=str(error));raise
    finally:report['elapsed_seconds']=time.monotonic()-start;save()


if __name__=='__main__':main()

"""Kernel-check amplitude quadrature, reusing the contact trajectory models."""
import sys
sys.dont_write_bytecode=True
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor,as_completed
import hashlib
import json
from pathlib import Path
import subprocess
import time
from .AmplitudeProposals import amplitude_program
from .IntegerIntervals import Bounds
from .VerifyContact import model,ints
from .FetchCertificate import ROOT,load_source,fetch
from .PrepareCertificate import prepare_payload,numeric_tokens,exact_number
from .SourceWitnesses import install_source


def generate(proposal,contact,reference,limit,check=False):
    """
    Emit amplitude models and kernel-check propositions linked to the identical contact panels.
    Reject any differing start, width or source-row indices; the shared DAG must also match
    exactly.
    """
    if proposal['format']!='UNTRUSTED_AMPLITUDE_VALUE_POLYNOMIALS_1' or proposal['bits']!=144:
        raise ValueError('Unexpected amplitude proposals')
    root=ROOT/'chebyshev2/Certificates/Compact';folder=root/'AmplitudeBatches';folder.mkdir(exist_ok=True)
    paths=[]
    def write(p,t):
        """
        Install or compare a generated amplitude source and record its path for
        source-integrity checks.
        """
        install_source(p,t,check)
        paths.append(p)
    header='''set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace chebyshev2.Certificates.Compact.AmplitudeValues
open chebyshev2.Numerics chebyshev2.Numerics.IntegerCertificate
'''
    shared='''import chebyshev2.Numerics.AmplitudeCheck
import chebyshev2.Certificates.Compact.ContactShared
'''+header+f'noncomputable def ops : List Op := {proposal["ops"]}\n'
    shared+='''noncomputable def scale : Nat := ContactValues.scale
noncomputable def epsilon : ℚ := 1/10^10
theorem shapeK : codeExpressionCheck ops 33 AmplitudeExpr.k=true := by decide +kernel
theorem shapeD : codeExpressionCheck ops 29 (AmplitudeExpr.den DualInputs.sigma)=true := by decide +kernel
theorem shapeE : codeExpressionCheck ops 5 (AmplitudeExpr.rootResidual DualInputs.sigma DualInputs.base DualInputs.omega)=true := by decide +kernel
theorem shapeQ : codeExpressionCheck ops 0 AmplitudeExpr.quadratureResidual=true := by decide +kernel
end chebyshev2.Certificates.Compact.AmplitudeValues
'''
    write(root/'AmplitudeShared.lean',shared);proofs=[];ps=proposal['panels'][:limit]
    for n,begin in enumerate(range(0,len(ps),32)):
        data=f'import chebyshev2.Certificates.Compact.ContactBatches.Data{n:03}\nimport chebyshev2.Certificates.Compact.AmplitudeShared\n'+header
        proof=f'import chebyshev2.Certificates.Compact.AmplitudeBatches.Data{n:03}\n'+header
        for i,p in enumerate(ps[begin:begin+32],begin):
            cp=contact['panels'][i]
            if any(p[k]!=cp[k] for k in ('start','width','left','right')):raise ValueError('Different source panel')
            ms=[[Bounds(v,v) for v in p['H']],[Bounds(v,v) for v in p['g']]]
            ms+=[[Bounds(*v) for v in m] for m in cp['models']]
            ms+=[[Bounds(v,v) for v in cp['g']]]
            P,out=amplitude_program(reference[1],reference[2],reference[3],ms,144,p['degree'])
            if P.lean_ops()!=proposal['ops']:raise ValueError('Changed amplitude graph')
            consumers=Counter(k for (op,args),_ in P.nodes if op!='literal' for k in args if k>=0)
            selected={j for j,n in consumers.items() if n>1}|set(out.values())
            cps='['+','.join('some '+model(m) if j in selected else 'none'
                for j,(_,m) in enumerate(P.nodes))+']'
            data+=f'''noncomputable def panel{i} : AmplitudePolynomial.Panel := {{
  base := ContactValues.panel{i}
  H := {ints(p['H'])}
  g := {ints(p['g'])}
  degree := {p['degree']}
  checkpoints := {cps}
}}
'''
            proof+=f'theorem check{i} : AmplitudePolynomial.check scale ops epsilon panel{i}=true := by decide +kernel\n'
        data+=f'noncomputable def block{n} : List AmplitudePolynomial.Panel := ['+','.join(f'panel{i}' for i in range(begin,min(begin+32,len(ps))))+']\n'
        data+='end chebyshev2.Certificates.Compact.AmplitudeValues\n';proof+='end chebyshev2.Certificates.Compact.AmplitudeValues\n'
        write(folder/f'Data{n:03}.lean',data);write(folder/f'Batch{n:03}.lean',proof)
        proofs.append(f'chebyshev2.Certificates.Compact.AmplitudeBatches.Batch{n:03}')
    return paths,proofs,len(ps)


def main():
    """
    Compare witnesses or build/replay amplitude batches. The actual integral bounds use the
    proved amplitude model bridge and complete interval coverage, not the saved acceptance
    report.
    """
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true',help='Compare installed witnesses without writing sources or replaying proofs')
    parser.add_argument('--offline',action='store_true');parser.add_argument('--limit',type=int,default=1291)
    parser.add_argument('--jobs',type=int,default=2,choices=[1,2]);parser.add_argument('--timeout',type=int,default=1800)
    args=parser.parse_args();folder=ROOT/'.lake/certificates/chebyshev2/compact-amplitude';path=folder/'report.json'
    if args.check:
        descriptor=load_source(ROOT/'chebyshev2/Certificates/Source.json')
        receipt=fetch(descriptor,ROOT/'.lake/certificates/chebyshev2',args.offline)
        archive=Path(receipt['archive']);payload,_=prepare_payload(archive,archive.parent)
        reference=list(map(exact_number,numeric_tokens((payload/'embedded/reference/reference.txt').read_text())))
        proposal=json.loads((folder/'proposals.json').read_text())
        contact=json.loads((folder.parent/'compact-contact/proposals.json').read_text())
        paths,_,count=generate(proposal,contact,reference,args.limit,check=True)
        print(f'Compared {len(paths)} installed sources ({count} panels); no proof replay requested.',flush=True)
        return
    report=dict(status='RUNNING',accepted_amplitude_value_checks=0,actual_amplitude_integral_verified=False)
    start=time.monotonic()
    def save():
        """
        Persist progress and hashes for operational inspection only.
        """
        path.write_text(json.dumps(report,indent=2)+'\n')
    def accept(module,label):
        """
        Require both a successful Lake build and an independent kernel replay for one module.
        """
        for suffix,command in [('build',['lake','build','+'+module]),
            ('replay',['lake','env','lean','--run','Tools/Verification/Replay.lean',module])]:
            with (folder/f'{label}-{suffix}.log').open('w') as log:
                subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
    save()
    try:
        source=load_source(ROOT/'chebyshev2/Certificates/Source.json')
        receipt=fetch(source,ROOT/'.lake/certificates/chebyshev2',args.offline)
        archive=Path(receipt['archive']);payload,_=prepare_payload(archive,archive.parent)
        reference=list(map(exact_number,numeric_tokens((payload/'embedded/reference/reference.txt').read_text())))
        proposal=json.loads((folder/'proposals.json').read_text())
        contact=json.loads((folder.parent/'compact-contact/proposals.json').read_text())
        paths,proofs,count=generate(proposal,contact,reference,args.limit)
        report['generated_source_sha256']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
        files=list((ROOT/'chebyshev2/Numerics').glob('*.lean'))+[Path(__file__).resolve(),
            ROOT/'Tools/Certificates/AmplitudeProposals.py',ROOT/'Tools/Certificates/VerifyContact.py',
            ROOT/'Tools/Certificates/ResidualPrograms.py',ROOT/'Tools/Certificates/IntegerIntervals.py']
        report['tool_sha256']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files};save()
        accept('chebyshev2.Certificates.Compact.AmplitudeShared','shared')
        def batch(i,module):
            """
            Accept one amplitude batch and return its label after both checks succeed.
            """
            accept(module.replace('.Batch','.Data'),f'data-{i:03}')
            accept(module,f'batch-{i:03}')
            return min(32,count-i*32)
        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            futures=[executor.submit(batch,i,module) for i,module in enumerate(proofs)]
            for future in as_completed(futures):
                report['accepted_amplitude_value_checks']+=future.result();save()
                print(f'Kernel and fresh replay accepted {report["accepted_amplitude_value_checks"]}/{count} amplitude checks',flush=True)
        for file,digest in {**report['generated_source_sha256'],**report['tool_sha256']}.items():
            if hashlib.sha256((ROOT/file).read_bytes()).hexdigest()!=digest:raise ValueError('Changed source: '+file)
        report['status']='CHECKS_PASS'
    except (OSError,ValueError,subprocess.SubprocessError) as error:
        report.update(status='FAIL',error=str(error));raise
    finally:report['elapsed_seconds']=time.monotonic()-start;save()


if __name__=='__main__':main()

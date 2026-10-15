"""Bounded-memory kernel acceptance of the complete reference trajectory.

Numerical data are generated from the pinned archive. Each cell has a short
kernel proof; bounded batches are freshly replayed before their count is saved.
"""
import sys
sys.dont_write_bytecode=True
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time
from FetchCertificate import ROOT,fetch,load_source
from PrepareCertificate import prepare_payload
from ResidualWitnesses import generate
from SourceWitnesses import install_source


def split_source(content, batch_blocks):
    """
    Split complete generated rows into data and proof modules with a bounded number of 16-cell
    blocks per batch. The combined source imports every batch; layout/count checks prevent a
    missing cell.
    """
    namespace='«2610.05164v2».Certificates.Compact.ReferenceResiduals'
    header=content[:content.index('noncomputable def row0')]
    definitions=re.findall(r'^noncomputable def row\d+[^\n]*\n',content,re.M)
    row_checks=re.findall(r'^theorem rowCheck\d+[^\n]*\n',content,re.M)
    blocks=re.findall(r'^noncomputable def block\d+[^\n]*\n',content,re.M)
    checks=re.findall(r'^theorem checks\d+[^\n]*\n  simp only[^\n]*\n  exact[^\n]*\n',content,re.M)
    rows=re.search(r'^noncomputable def rows[^\n]*\n',content,re.M).group()
    if len(definitions)!=2519 or len(row_checks)!=2519 or len(blocks)!=158 or len(checks)!=158:
        raise ValueError('Unexpected generated declaration layout')
    prefix='«2610.05164v2».Certificates.Compact.ReferenceResidualBatches.'
    shared='«2610.05164v2».Certificates.Compact.ReferenceResidualShared'
    sources={ROOT/'2610.05164v2/Certificates/Compact/ReferenceResidualShared.lean':header+f'end {namespace}\n'}
    proof_modules=[]; data_modules=[]
    settings='set_option autoImplicit false\nset_option warningAsError true\nset_option maxHeartbeats 0\nset_option maxRecDepth 200000\nnamespace «2610.05164v2».Certificates.Compact.ReferenceResiduals\nopen «2610.05164v2».Numerics.IntegerCertificate\n'
    for first in range(0,len(blocks),batch_blocks):
        last=min(first+batch_blocks,len(blocks));number=f'{first//batch_blocks:03}'
        data_name='Data'+number; proof_name='Batch'+number
        data_modules.append(prefix+data_name);proof_modules.append(prefix+proof_name)
        data='import '+shared+'\n'+settings
        data+=''.join(definitions[first*16:min(last*16,2519)])+''.join(blocks[first:last])
        data+=f'end {namespace}\n'
        proof='import '+prefix+data_name+'\n'+settings
        proof+=''.join(row_checks[first*16:min(last*16,2519)])+''.join(checks[first:last])
        proof+=f'end {namespace}\n'
        sources[ROOT/f'2610.05164v2/Certificates/Compact/ReferenceResidualBatches/{data_name}.lean']=data
        sources[ROOT/f'2610.05164v2/Certificates/Compact/ReferenceResidualBatches/{proof_name}.lean']=proof
    data='\n'.join('import '+m for m in data_modules)+'\n'+settings+rows+f'end {namespace}\n'
    sources[ROOT/'2610.05164v2/Certificates/Compact/ReferenceResidualData.lean']=data
    rest=content[content.index('theorem combineChecked'):]
    main='\n'.join('import '+m for m in proof_modules)+'\n'
    main+='import «2610.05164v2».Certificates.Compact.ReferenceResidualData\n'+settings
    main+='open «2610.05164v2».Numerics «2610.05164v2».Certificates.DualInputs\n'+rest
    sources[ROOT/'2610.05164v2/Certificates/Compact/ReferenceResiduals.lean']=main
    return sources,list(zip(data_modules,proof_modules))


def main():
    """
    Regenerate the complete 2,519-cell source or compare it offline. Acceptance mode builds and
    independently replays each batch and its actual-trajectory bridge; saved counters are only
    progress reports.
    """
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--offline',action='store_true')
    p.add_argument('--check',action='store_true',help='Compare regenerated sources without replaying accepted numerical proofs')
    p.add_argument('--batch-blocks',type=int,default=4,choices=[1,2,4])
    p.add_argument('--timeout',type=int,default=1200)
    args=p.parse_args()
    if args.check:
        descriptor=load_source(ROOT/'2610.05164v2/Certificates/Source.json')
        receipt=fetch(descriptor,ROOT/'.lake/certificates/2610.05164v2',args.offline)
        archive=Path(receipt['archive']);payload,_=prepare_payload(archive,archive.parent)
        content,_=generate(payload,list(range(2519)),144)
        sources,_=split_source(content,args.batch_blocks)
        for path,text in sources.items():
            install_source(path,text,True)
        print(f'Compared {len(sources)} installed sources with the pinned archive; no proof replay was requested.',flush=True)
        return
    folder=ROOT/'.lake/certificates/2610.05164v2/compact-residual-batches';folder.mkdir(parents=True,exist_ok=True)
    report_path=folder/'report.json'
    report=dict(status='RUNNING',accepted_actual_rhs_residual_cells=0,
                actual_reference_trajectory_verified=False,actual_ode_chains_verified=False,
                scope="reference-only")
    def save():
        """
        Persist progress for inspection. No Lean statement reads this status report as a
        premise.
        """
        report_path.write_text(json.dumps(report,indent=2)+'\n')
    save();started=time.monotonic()
    tools=[Path(__file__),ROOT/'Scripts/ResidualWitnesses.py',ROOT/'Scripts/ResidualPrograms.py',
           ROOT/'Scripts/ReferenceJets.py',ROOT/'Scripts/IntegerIntervals.py',
           *sorted((ROOT/'2610.05164v2/Numerics').glob('Integer*.lean')),
           ROOT/'2610.05164v2/Numerics/ReferenceResidualIdentity.lean']
    hashes={str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in tools}
    def run(command,label):
        """
        Run one checked subprocess with a bounded timeout and a dedicated diagnostic log.
        """
        with (folder/(label+'.log')).open('w') as log:
            subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
    def accept(module,label):
        """
        Build a module and replay its compiled declarations through Lean's stock kernel. Both
        steps must succeed before reporting acceptance.
        """
        run(['lake','build','+'+module],label+'-build')
        run(['lake','env','lean','--run','Scripts/Replay.lean',module],label+'-replay')
    try:
        descriptor=load_source(ROOT/'2610.05164v2/Certificates/Source.json')
        receipt=fetch(descriptor,ROOT/'.lake/certificates/2610.05164v2',args.offline)
        archive=Path(receipt['archive']);payload,_=prepare_payload(archive,archive.parent)
        content,metrics=generate(payload,list(range(2519)),144)
        sources,modules=split_source(content,args.batch_blocks)

        for path,text in sources.items():
            path.parent.mkdir(parents=True,exist_ok=True)
            install_source(path,text)
        generated_hashes={str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources}
        report.update(metrics=metrics,generated_source_bytes=sum(len(s.encode()) for s in sources.values()),
                      generated_source_sha256=generated_hashes,tool_sha256=hashes)
        save()
        accept('«2610.05164v2».Certificates.Compact.ReferenceResidualShared','shared')
        for i,(data_module,proof_module) in enumerate(modules):
            print(f'Checking batch {i+1}/{len(modules)}',flush=True)
            accept(data_module,f'data-{i:03}')
            accept(proof_module,f'batch-{i:03}')
            report['accepted_actual_rhs_residual_cells']=min((i+1)*args.batch_blocks*16,2519)
            save()
            print(f'Kernel and fresh replay accepted {report["accepted_actual_rhs_residual_cells"]}/2519 cells',flush=True)
        accept('«2610.05164v2».Certificates.Compact.ReferenceResidualData','data')
        accept('«2610.05164v2».Certificates.Compact.ReferenceTrajectoryData','trajectory-data')
        accept('«2610.05164v2».Certificates.Compact.ReferenceResiduals','residuals')
        accept('«2610.05164v2».Certificates.Compact.ReferenceTrajectory','trajectory')
        for path,digest in hashes.items():
            if hashlib.sha256((ROOT/path).read_bytes()).hexdigest()!=digest:
                raise ValueError('Tool changed during acceptance: '+path)
        for path,digest in generated_hashes.items():
            if hashlib.sha256((ROOT/path).read_bytes()).hexdigest()!=digest:
                raise ValueError('Generated proof changed during acceptance: '+path)
        report.update(status='PASS',actual_reference_trajectory_verified=True,
                      actual_ode_chains_verified=True,scope='Complete actual reference chain only')
    except (OSError,ValueError,subprocess.SubprocessError) as error:
        report.update(status='FAIL',error=str(error));raise
    finally:
        report['elapsed_seconds']=time.monotonic()-started;save()
    print(json.dumps({k:v for k,v in report.items() if not k.endswith('sha256')},indent=2))


if __name__=='__main__':main()

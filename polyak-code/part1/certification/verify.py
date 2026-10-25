"""Cold, explicit verification of all 24 baseline and three analytic suites."""
from concurrent.futures import ProcessPoolExecutor, as_completed
from importlib import import_module, metadata
from pathlib import Path
import gzip
import hashlib
import json
import platform
import time
import traceback
import numpy as np
from .report import Collector, canonical_bytes
from .precision import local_precision
from .paths import ROOT, GENERATED, HEAVY_BALL

GROUPS = {
    "base": ("base",),
    "upper": ("upper_factorization","upper_derivative","upper_critical"),
    "lower": ("startup_identities","startup_regions"),
    "struct": ("a7_involution","a7_thresholds","a7_minpolys","a7_cycles",
               "a7_threshold_kc","a8_kkt","a8_elim","a8_onewave","a8_curves",
               "a8_regular","a8_u5","a9_asym","a9_kc_slopes","a9_kappa1","a9_kappa1_bound"),
    "extensions": ("extended_derivative","p2_switch_elimination"),
    "regimes": ("regimes",),
    "analytic": ("p5_critical","linear_gap","p2_rational"),
}


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True,exist_ok=True)
    raw = canonical_bytes(value)
    if path.suffix == ".gz":
        path.write_bytes(gzip.compress(raw,mtime=0))
    else:
        path.write_bytes(raw)


def read_json(path):
    path = Path(path)
    raw = path.read_bytes()
    return json.loads(gzip.decompress(raw) if path.suffix == ".gz" else raw)


def versions():
    return {"python":platform.python_version(), **{n:metadata.version(n) for n in
            ("sympy","mpmath","python-flint","numpy","scipy","matplotlib")}}


def source_hashes():
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(ROOT.rglob("*.py"))}


def requirements_hash():
    return hashlib.sha256((HEAVY_BALL/"requirements.txt").read_bytes()).hexdigest()


def run_regimes(ctx, slabs, independent=True):
    from .algebra.systems import build
    from .branch_checks import check_p1, check_p2, check_central
    from .interval import run
    if independent:
        import_module(".checks.p2_field",__package__).run(ctx)
    families = (("p1",0,.733,[.125,-.25]),
                ("p2",1.02358,1.03330,[.51156,-.5038,.2797,.0516,.04556,.36489]),
                ("central",0,.023582,[.51466,-.25854,.23189,2.579,2.1051,.374348,.596502]))
    for family,a,b,guess in families:
        if family=="p2" and not independent:
            continue
        system = build(family)
        ctx.check(all(e.is_polynomial(system.parameter,*system.variables) for e in system.equations),
                  family+": source system is polynomial")
        checker = {"p1":lambda:check_p1(system.dual,ctx),
                   "p2":lambda:check_p2(system.variables,ctx),
                   "central":lambda:check_central(system.dual,ctx)}[family]()
        boxes = run(system.equations,system.parameter,system.variables,
                    np.linspace(a,b,slabs+1),guess,check=checker,name=family,collector=ctx)
        ctx.artifacts[family+"_boxes.json"] = boxes
    import_module(".checks.regime_signs",__package__).run(ctx,independent=independent)
    if independent:
        import_module(".checks.endpoints",__package__).run(ctx)
    else:
        from .endpoints import check
        check(ctx)


@local_precision(bits=160,digits=40)
def _run_group(group, output, slabs, profile="complete"):
    artifacts, records = {}, []
    for name in GROUPS[group]:
        if profile=="proof" and name=="p2_switch_elimination":
            continue
        ctx = Collector(name,artifacts=artifacts)
        start = time.monotonic()
        try:
            if name == "regimes":
                run_regimes(ctx,slabs,independent=profile=="complete")
            else:
                import_module(".checks."+name,__package__).run(ctx)
            result = ctx.result()
        except Exception as exc:
            result = {**ctx.result(),"passed":False,"error":repr(exc),"traceback":traceback.format_exc()}
        result["seconds"] = round(time.monotonic()-start,3)
        records.append(result)
        write_json(Path(output)/"checks"/(name+".json"),result)
        if not result["passed"]:
            break
    for key,value in artifacts.items():
        if key.endswith("_boxes.json"):
            write_json(Path(output)/"continuation"/(key+".gz"),value)
    return group, records


def verify(output, jobs=4, slabs=4000, groups=None, profile="proof"):
    if not __debug__:
        raise RuntimeError("verification must not run under python -O")
    if not 1 <= jobs <= 8 or slabs < 1:
        raise ValueError("jobs must be 1..8 and slabs must be positive")
    if profile not in ("proof", "complete"):
        raise ValueError("unknown verification profile")
    output = Path(output).resolve()
    selected = list(groups or GROUPS)
    if len(selected)!=len(set(selected)) or any(group not in GROUPS for group in selected):
        raise ValueError("verification groups must be distinct known group names")
    results = {}
    with ProcessPoolExecutor(max_workers=jobs) as pool:
        futures = [pool.submit(_run_group,g,str(output),slabs,profile) for g in selected]
        for future in as_completed(futures):
            group, records = future.result()
            results[group] = records
            for record in records:
                print(("PASS " if record["passed"] else "FAIL ")+record["suite"],flush=True)
    ordered = [r for g in selected for r in results[g]]
    expected = sum(len(GROUPS[g]) for g in selected)-int(profile=="proof" and "extensions" in selected)
    manifest = {"schema":"polyak-verification-v1","passed":len(ordered)==expected and
                all(r["passed"] for r in ordered),"versions":versions(),
                "layout":"heavy-ball-certification-v1", "historical":False,
                "requirements_sha256":requirements_hash(),
                "sources_sha256":source_hashes(),"slabs_per_family":slabs,
                "baseline_suites":24,"analytic_suites":3,"selected_groups":selected,"profile":profile,
                "independent_cross_checks":profile=="complete",
                "results":[{k:v for k,v in r.items() if k not in ("checks","notes","traceback")} for r in ordered],
                "check_evaluations":sum(c["evaluations"] for r in ordered for c in r["checks"])}
    write_json(output/"manifest.json",manifest)
    return manifest

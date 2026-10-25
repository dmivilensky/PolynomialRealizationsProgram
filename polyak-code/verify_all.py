"""Run every verification of the paper from source and record the results.

Usage:  python verify_all.py [--jobs 4] [--figures] [--part1-only | --part2-only]

The Part I programs are copied into a fresh temporary directory and executed there, so that every
intermediate algebraic object (pickles, continuation boxes) is regenerated. Printed exact Boolean
checks are promoted to assertions by a small harness. The Part II programs and the spiral programs
are executed in place; part2/plateaus/run_plateaus.py verifies the thirty-five rows of Table 2
in parallel processes. With --figures the figure scripts are run afterwards (figures/make_all.py).
A failed identity, sign check, interval inclusion or branch connection gives a nonzero exit status.
Results are written to verification/manifest.json and verification/<script>.log.
The explicit Part I certificate checks, exact export and JSON-only proof
archive always run after successful paper checks. The --part1-only path skips
Part II and uses the complete certificate profile, including independent P2
continuation. It does not draw figures and writes verification/part1/ reports.
Part II also automatically packages its selected exact witnesses. The
--part2-only path recomputes those five examples and their mathematical archive
without rerunning Part I or drawing figures.
"""
from pathlib import Path
import argparse
import concurrent.futures
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'verification'

PART1 = {
    'spiral': ['base/base_check.py'],
    'dual': ['upper/upper_sym.py'],
    'lower': ['lower/a3_identities.py', 'lower/a3_regions.py'],
    'struct': ['struct/' + s + '.py' for s in (
        'a7_involution', 'a7_thresholds', 'a7_minpolys', 'a7_cycles', 'a7_threshold_kc',
        'a8_kkt', 'a8_elim', 'a8_onewave', 'a8_curves', 'a8_regular', 'a9_asym', 'a9_kappa1')],
    'regimes': ['regimes/verify_regimes.py'],
    'analytic': ['analytic/p5_critical.py', 'analytic/p2_rational.py'],
}
DIRECT = ['part1/spiral/spiral_kernel.py', 'part1/spiral/spiral_subopt.py',
          'part2/general_identities.py', 'part2/convexity.py', 'part2/threshold_identities.py',
          'part2/prop13_check.py', 'part2/convgap_check.py', 'part2/exact_313.py', 'part2/plateaus/run_plateaus.py']

HARNESS = r'''
import builtins, runpy, sys
from sympy.logic.boolalg import BooleanFalse
original_print = builtins.print
def checked_print(*args, **kwargs):
    def check(x):
        if x is False or isinstance(x, BooleanFalse):
            raise AssertionError('A printed exact Boolean check is false: ' + repr(args))
        if isinstance(x, (list, tuple)):
            for y in x: check(y)
    for x in args: check(x)
    original_print(*args, **kwargs)
builtins.print = checked_print
runpy.run_path(sys.argv[1], run_name='__main__')
'''


def run(cmd, cwd, log):
    start = time.monotonic()
    with log.open('w') as f:
        proc = subprocess.run(cmd, cwd=cwd, stdout=f, stderr=subprocess.STDOUT)
    text = log.read_text()
    passed = proc.returncode == 0 and 'FAIL' not in text.replace('FAILED_ALLOWED', '')
    return passed, proc.returncode, round(time.monotonic() - start, 2)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--figures', action='store_true')
    selected_part = parser.add_mutually_exclusive_group()
    selected_part.add_argument('--part1-only', action='store_true',
                        help='verify only Part I and automatically export/package the complete proof data')
    selected_part.add_argument('--part2-only', action='store_true',
                        help='recompute the five selected Part II examples and automatically package exact witnesses')
    parser.add_argument('--certification-profile', choices=('proof', 'complete'),
                        help='certificate profile; default complete for --part1-only, proof otherwise')
    args = parser.parse_args()
    if not 1 <= args.jobs <= 8:
        parser.error('--jobs must be in 1..8')
    if (args.part1_only or args.part2_only) and args.figures:
        parser.error('part-only verification does not run figure programs')
    start = time.monotonic()
    started = datetime.now(timezone.utc).isoformat()
    if args.part2_only:
        output_dir = OUT / 'part2'
        output_dir.mkdir(parents=True, exist_ok=True)
        ok, code, sec = run([sys.executable, '-u', '-m', 'part2.certification', 'regen'],
                            ROOT, output_dir / 'certification_regen.log')
        result = dict(passed=ok, scope='part2', started_utc=started,
                      finished_utc=datetime.now(timezone.utc).isoformat(),
                      seconds=sec, results=[dict(script='part2.certification regen',
                                               passed=ok, exit_code=code, seconds=sec)])
        (output_dir / 'manifest.json').write_text(json.dumps(result, indent=2)+'\n')
        print('PART II DATA GENERATED' if ok else 'PART II GENERATION FAILED', flush=True)
        return 0 if ok else 1
    profile = args.certification_profile or ('complete' if args.part1_only else 'proof')
    direct = [rel for rel in DIRECT if not args.part1_only or rel.startswith('part1/')]
    output_dir = OUT / 'part1' if args.part1_only else OUT
    if not __debug__:
        raise RuntimeError('Do not run the verification with python -O')
    output_dir.mkdir(parents=True, exist_ok=True)
    sources = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in sorted((ROOT / 'part1').rglob('*.py') if args.part1_only else ROOT.glob('part*/**/*.py'))}
    versions = {}
    for name in ('sympy', 'mpmath', 'python-flint', 'numpy', 'scipy', 'matplotlib'):
        try:
            versions[name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            versions[name] = None
    results = []
    with tempfile.TemporaryDirectory(prefix='hb_two_answers_') as tmp:
        tmp = Path(tmp)
        shutil.copytree(ROOT / 'part1' / 'hb_an', tmp / 'hb_an',
                        ignore=shutil.ignore_patterns('*.pkl', '*.out', '__pycache__'))

        def run_group(item):
            name, scripts = item
            out = []
            for rel in scripts:
                p = tmp / 'hb_an' / rel
                passed, code, sec = run([sys.executable, '-u', '-c', HARNESS, str(p)], p.parent, output_dir / (p.stem + '.log'))
                out.append(dict(script='part1/hb_an/' + rel, passed=passed, exit_code=code, seconds=sec))
                print(('PASS  ' if passed else 'FAIL  ') + 'part1/hb_an/' + rel, f'({sec} s)', flush=True)
                if p.stem == 'verify_regimes' and passed:
                    for boxes in p.parent.glob('*_boxes.json'):
                        shutil.copy2(boxes, output_dir / boxes.name)
                if not passed:
                    break
            return out

        def run_direct(rel):
            p = ROOT / rel
            extra = ['--jobs', str(max(1, args.jobs))] if p.name == 'run_plateaus.py' else []
            passed, code, sec = run([sys.executable, '-u', str(p), *extra], p.parent, output_dir / (p.stem + '.log'))
            print(('PASS  ' if passed else 'FAIL  ') + rel, f'({sec} s)', flush=True)
            return [dict(script=rel, passed=passed, exit_code=code, seconds=sec)]

        with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
            futures = [pool.submit(run_group, it) for it in PART1.items()]
            futures += [pool.submit(run_direct, rel) for rel in direct]
            for f in futures:
                results += f.result()
    expected = sum(map(len, PART1.values())) + len(direct)
    passed = len(results) == expected and all(r['passed'] for r in results)
    if passed:
        for command in ('regen',):
            extra = ['--jobs', str(args.jobs), '--profile', profile]
            ok, code, sec = run([sys.executable, '-u', '-m', 'part1.certification', command, *extra],
                                ROOT, output_dir / ('certification_' + command + '.log'))
            results.append(dict(script='part1.certification ' + command,
                                passed=ok, exit_code=code, seconds=sec))
            print(('PASS  ' if ok else 'FAIL  ') + 'part1.certification ' + command,
                  f'({sec} s)', flush=True)
            passed = passed and ok
            if not ok:
                break
    if passed and not args.part1_only:
        ok, code, sec = run([sys.executable, '-u', '-m', 'part2.certification', 'regen'],
                            ROOT, output_dir / 'part2_certification_regen.log')
        results.append(dict(script='part2.certification regen',
                            passed=ok, exit_code=code, seconds=sec))
        print(('PASS  ' if ok else 'FAIL  ') + 'part2.certification regen', f'({sec} s)', flush=True)
        passed = passed and ok
    if args.figures:
        ok, code, sec = run([sys.executable, '-u', str(ROOT / 'figures' / 'make_all.py')], ROOT / 'figures',
                            output_dir / 'figures.log')
        results.append(dict(script='figures/make_all.py', passed=ok, exit_code=code, seconds=sec))
        print(('PASS  ' if ok else 'FAIL  ') + 'figures/make_all.py', f'({sec} s)', flush=True)
        passed = passed and ok
    manifest = dict(passed=passed, scope='part1' if args.part1_only else 'all',
                    certification_profile=profile, started_utc=started,
                    finished_utc=datetime.now(timezone.utc).isoformat(),
                    seconds=round(time.monotonic()-start, 3),
                    python=sys.version, versions=versions, sources_sha256=sources, results=results)
    (output_dir / 'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
    print('ALL CHECKS PASSED' if passed else 'VERIFICATION FAILED')
    return 0 if passed else 1


if __name__ == '__main__':
    sys.exit(main())

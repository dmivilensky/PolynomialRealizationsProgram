"""Check an entire article with at most two simultaneous Lean processes."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
PAPERS = ("2606.16671v2", "2610.05164v2")


def main():
    """
    Check article correspondence, then ask Lake for the dirty frontier until the complete
    verification target is current. Requerying preserves cached proofs and catches newly
    unblocked descendants.
    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paper", choices=(*PAPERS, "all"))
    parser.add_argument("--jobs", type=int, choices=(1, 2), default=2)
    args = parser.parse_args()
    papers = PAPERS if args.paper == "all" else (args.paper,)
    subprocess.run(["python3", "Scripts/CheckCorrespondence.py", *papers], cwd=ROOT, check=True)
    targets = ["PolynomialRealizationsProgram"] if args.paper == "all" else [f"«{args.paper}».Check"]
    logs = ROOT / ".lake" / "checks" / args.paper
    logs.mkdir(parents=True, exist_ok=True)

    def query(group, label):
        """
        Ask Lake to check dependency traces without building. Only the explicit out-of-date
        diagnostic is recoverable; other errors stop the check.
        """
        result = subprocess.run(["lake", "--no-build", "build", *("+" + m for m in group)],
                                cwd=ROOT, capture_output=True, text=True)
        output = result.stdout + result.stderr
        (logs / f"{label}.log").write_text(output)
        errors = re.findall(r"^error: (.*)$", output, re.M)
        if any(e != "target is out-of-date and needs to be rebuilt" for e in errors):
            raise RuntimeError(f"Lake dependency query failed; see {logs / (label + '.log')}")
        return result.returncode, output

    def build(module):
        """
        Build one frontier module and retain its diagnostic log. Its prerequisites are already
        cached; a nonzero result is a failed check.
        """
        path = logs / (module + ".log")
        with path.open("w") as log:
            result = subprocess.run(["lake", "build", "+" + module], cwd=ROOT, stdout=log,
                                    stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f"Lean failed: {module}; see {path}")
        return module

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while True:
            code, output = query(targets, "package")
            if code == 0:
                print(output, end="")
                return
            # Lake reports a dirty frontier whose prerequisites are cached.
            # Requery after each batch: blocked descendants may become dirty next.
            ready = sorted(set(re.findall(r"✖[^\n]* Building ([^\s]+)", output)))
            if not ready:
                raise RuntimeError(f"No rebuildable target; see {logs / 'package.log'}")
            for name in pool.map(build, ready[:args.jobs]):
                print(f"Checked {name}", flush=True)


if __name__ == "__main__":
    main()

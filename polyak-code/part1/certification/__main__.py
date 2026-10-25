"""Part I mathematical verification and exact-data interchange."""
import argparse
import json
from pathlib import Path
import sys


def parser():
    result = argparse.ArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)
    verify = commands.add_parser("verify", help="cold exact and Arb verification")
    verify.add_argument("--out", type=Path)
    verify.add_argument("--jobs", type=int, default=4)
    verify.add_argument("--slabs", type=int, default=4000)
    verify.add_argument("--group", action="append")
    verify.add_argument("--profile", choices=["proof", "complete"], default="proof")
    export = commands.add_parser("export", help="export freshly verified mathematical data")
    export.add_argument("--out", type=Path)
    export.add_argument("--verification", type=Path)
    check = commands.add_parser("check-bundle", help="validate exact data and content hashes")
    check.add_argument("path", nargs="?", type=Path)
    regen = commands.add_parser("regen", help="cold verify and export without drawing figures")
    regen.add_argument("--out", type=Path)
    regen.add_argument("--jobs", type=int, default=4)
    regen.add_argument("--slabs", type=int, default=4000)
    regen.add_argument("--profile", choices=["proof", "complete"], default="proof")
    package = commands.add_parser("package", help="package mathematical data as proof.tar.xz")
    package.add_argument("--out", type=Path)
    return result


def main(argv=None):
    args = parser().parse_args(argv)
    from .paths import GENERATED, PROOF
    if args.command == "verify":
        from .verify import verify
        record = verify(args.out or GENERATED / "verification", args.jobs,
                        args.slabs, args.group, args.profile)
        result = {"passed": record["passed"], "suites": len(record["results"]),
                  "check_evaluations": record["check_evaluations"]}
    elif args.command == "export":
        from .export import export_bundle
        result = export_bundle(args.out, args.verification)
    elif args.command == "check-bundle":
        from .export import check_bundle
        result = check_bundle(args.path or PROOF / "proof.tar.xz")
    elif args.command == "regen":
        from .reproduce import regenerate
        result = regenerate(args.out, args.jobs, args.slabs, args.profile)
    else:
        from .reproduce import package
        result = package(args.out)
    print(json.dumps(result, sort_keys=True, allow_nan=False))
    return 0 if result.get("passed", True) else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)

"""Check registered Lean source directories with a configurable process limit."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import re
import subprocess

from .ArticleCoverage import check as check_article
from .CheckCorrespondence import check
from .PrepareSources import prepare
from .Project import select_projects, sync_aggregate, workspace_sources


def main():
    """
    Prepare declared exact source inputs, check article correspondence, then ask Lake for
    the dirty frontier until the complete verification target is current. Requerying
    preserves cached proofs and catches newly unblocked descendants.
    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", nargs="?", default="all", help="Source directory or all (default)")
    parser.add_argument("--list", action="store_true", help="List selected Check modules without building")
    parser.add_argument("--offline", action="store_true",
                        help="Use cached certificate archives and Python environments; never install packages")
    parser.add_argument("--require-complete", action="store_true",
                        help="Require a complete reviewed article correspondence, beyond import coverage")
    replays = parser.add_mutually_exclusive_group()
    replays.add_argument("--replay", action="store_true",
                         help="Independently replay all owned proofs with the stock kernel after building")
    replays.add_argument("--replay-scope", action="append", help="Replay this package-relative namespace; repeat for a union of "
                         "subdirectory; reuse previously checked compiled dependencies")
    parser.add_argument("--archive", help="Use a local pinned certificate archive for one selected package")
    parser.add_argument("--jobs", type=int, default=2,
                        help="Maximum concurrent Lean processes (default: 2)")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if args.replay_scope is not None and len(args.replay_scope) == 1:
        args.replay_scope = args.replay_scope[0]
    try:
        projects = select_projects([args.directory])
        if args.replay_scope is not None:
            if args.directory == "all" or len(projects) != 1:
                raise ValueError("--replay-scope requires one explicitly selected package")
            from .Replay import replay_manifest
            replay_manifest(projects[0], args.replay_scope, allow_preparation=True)
        if args.archive is not None and (args.directory == "all" or len(projects) != 1):
            raise ValueError("--archive requires one explicitly selected package")
        if args.list:
            for project in projects:
                print(f"{project.relative}: {project.check_module}")
            return
        workspace = projects[0].workspace
        for project in projects:
            prepare(project, offline=args.offline, archive=args.archive)
        if args.replay_scope is not None:
            # Generated source groups can be empty immediately after Clean.
            # Require the complete actual replay union after restoring them.
            replay_manifest(projects[0], args.replay_scope)
        if args.directory == "all":
            sync_aggregate(projects)
        for project in projects:
            check(project)
            check_article(project, require_complete=args.require_complete)
    except (OSError, ValueError, KeyError) as error:
        parser.exit(1, f"Source check failed: {error}\n")
    targets = [project.check_module for project in projects]
    if args.directory == "all" and "Verification.All" in workspace_sources(workspace):
        targets = ["Verification.All"]
    logs = workspace / ".lake" / "checks" / ("all" if args.directory == "all" else projects[0].relative)
    logs.mkdir(parents=True, exist_ok=True)

    def query(group, label):
        """
        Ask Lake to check dependency traces without building. Only the explicit out-of-date
        diagnostic is recoverable; other errors stop the check.
        """
        result = subprocess.run(["lake", "--no-build", "build", *("+" + m for m in group)],
                                cwd=workspace, capture_output=True, text=True)
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
            result = subprocess.run(["lake", "build", "+" + module], cwd=workspace, stdout=log,
                                    stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f"Lean failed: {module}; see {path}")
        return module

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        pending = set()
        running = {}
        while True:
            if not pending and len(running) < args.jobs:
                code, output = query(targets, "package")
                if code == 0:
                    # A target can become current just before its Lake process exits.
                    # Still collect every process result before reporting success.
                    for future in running:
                        print(f"Checked {future.result()}", flush=True)
                    print(output, end="")
                    if args.replay or args.replay_scope is not None:
                        from .Replay import replay
                        for project in projects:
                            replay(project, args.replay_scope)
                    return
                ready = set(re.findall(r"✖[^\n]* Building ([^\s]+)", output))
                pending = ready - set(running.values())
                if not pending and not running:
                    raise RuntimeError(f"No rebuildable target; see {logs / 'package.log'}")
            # Keep the queue outside the executor: completed modules can unblock
            # descendants while an independent, expensive certificate is running.
            for name in sorted(pending)[:args.jobs - len(running)]:
                running[pool.submit(build, name)] = name
                pending.remove(name)
            completed, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in sorted(completed, key=running.get):
                print(f"Checked {future.result()}", flush=True)
                del running[future]


if __name__ == "__main__":
    main()

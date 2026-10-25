"""Replay compiled proofs for any registered Lean source directory without rebuilding."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

from .Project import name_parts, select_projects
from .PrepareSources import registered_sources


def replay_manifest(project, scope=None, *, allow_preparation=False):
    """Select all owned modules, or one strict namespace subtree.

    A scoped replay checks that subtree against its compiled dependencies. Those
    dependencies are not replayed again. The stock helper rejects any baseline
    that already contains declarations belonging to the selected namespace.
    Filesystem components are retained verbatim, including dotted directory names.
    """
    if scope is None:
        roots = [project.parts]
    else:
        scopes = [scope] if isinstance(scope, str) else list(scope)
        if not scopes:
            raise ValueError("Replay scopes must be nonempty")
        roots = []
        for selected in scopes:
            relative = Path(selected)
            if (not selected or relative.is_absolute() or not relative.parts
                    or ".." in relative.parts):
                raise ValueError("Replay scope must be a nonempty package-relative subdirectory")
            directory = (project.directory / relative).resolve()
            package = project.directory.resolve()
            if (directory == package or not directory.is_relative_to(package)
                    or not directory.is_dir()):
                raise ValueError(f"Replay scope must be an existing strict package subdirectory: {selected}")
            root = directory.relative_to(project.source_root).parts
            if not any(name_parts(project.source_module(path))[:len(root)] == root
                       for path in project.sources):
                # A clean source group retains its local descriptors while all
                # of its Lean literals are disposable. Check validates the
                # resulting modules again after automatic preparation.
                declared = project.directory / "Certificates"
                regenerable = (allow_preparation and directory.is_relative_to(declared)
                               and any(p.is_relative_to(directory) and p.is_file()
                                       for p in registered_sources(project)))
                if not regenerable:
                    raise ValueError(f"Replay scope contains no owned Lean modules: {selected}")
            if root not in roots:
                roots.append(root)
        # A parent scope already owns its descendants. Preserve exact module
        # components while removing redundant ownership roots.
        roots = [root for root in roots if not any(
            root != parent and root[:len(parent)] == parent for parent in roots)]
    modules = [parts for path in project.sources
               if any((parts := name_parts(project.source_module(path)))[:len(root)] == root
                      for root in roots)]
    manifest = {"modules": modules}
    # Keep the original single-root manifest format for existing callers.
    manifest["root" if len(roots) == 1 else "roots"] = roots[0] if len(roots) == 1 else roots
    return manifest


def replay(project, scope=None):
    """Pass exact module components to the stock-kernel replay helper."""
    manifest = replay_manifest(project, scope)
    if scope is not None:
        print(f"{project.relative}: replaying {len(manifest['modules'])} scoped modules "
              f"under {scope}; other compiled dependencies are the baseline.", flush=True)
    helper = Path(__file__).with_suffix(".lean")
    with tempfile.TemporaryDirectory(prefix="lean-replay-") as temporary:
        path = Path(temporary) / "modules.json"
        path.write_text(json.dumps(manifest))
        subprocess.run(["lake", "env", "lean", "--run", str(helper), "--package", str(path)],
                       cwd=project.workspace, check=True)


def main():
    """Replay one source directory or every discovered package using the same directory selector."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", nargs="?", default="all", help="Source directory or all (default)")
    parser.add_argument("--scope", action="append", help="Replay this package-relative namespace subdirectory; repeat for a union; "
                        "reuse previously checked compiled dependencies")
    args = parser.parse_args()
    try:
        projects = select_projects([args.directory])
        if args.scope is not None and (args.directory == "all" or len(projects) != 1):
            raise ValueError("--scope requires one explicitly selected package")
        scope = args.scope[0] if args.scope is not None and len(args.scope) == 1 else args.scope
        for project in projects:
            replay(project, scope)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Kernel replay failed: {error}\n")


if __name__ == "__main__":
    main()

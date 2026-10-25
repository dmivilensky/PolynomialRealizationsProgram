"""Prepare declared exact source data before checking a discovered Lean directory.

The tools' registry selects a converter.
Archives retain the shared fetcher's mandatory size and SHA-256 checks. Preparation
generates proof inputs; only the subsequent Lean check verifies their mathematics.
"""
from pathlib import Path
import re
import subprocess
import sys

from Tools.Certificates.FetchCertificate import fetch, load_source, verify_archive
from Tools.Certificates.Registry import PREPARATIONS
from .CertificateEnvironment import interpreter


def registered_sources(project):
    """List registered source groups, including groups with cleaned generated inputs."""
    directory = project.directory / "Certificates"
    result = {}
    for relative, hook in PREPARATIONS.get(project.relative, {}).items():
        path = project.directory / relative
        if (Path(relative).is_absolute() or ".." in Path(relative).parts or
                path.name != "Source.json" or not path.is_relative_to(directory)):
            raise ValueError(f"Invalid tools-owned certificate registration: {relative}")
        result[path] = hook
    for descriptor in result:
        if any(parent.is_symlink() for parent in (descriptor, *descriptor.parents)
               if parent.is_relative_to(directory)):
            raise ValueError("Preparation descriptors must not use symlinked paths")
    return result


def _prepare_one(project, descriptor, hook, offline=False, archive=None):
    """Run a workspace-local converter after mandatory source byte checks."""
    if not descriptor.is_file():
        raise ValueError(f"Missing registered Source.json: {descriptor}")
    if (not isinstance(hook, dict) or "module" not in hook or
            set(hook) - {"module", "requirements"}):
        raise ValueError(f"{descriptor}: expected a module and optional requirements")
    module = hook["module"]
    if not isinstance(module, str) or not re.fullmatch(
            r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*", module, re.ASCII):
        raise ValueError(f"{descriptor}: invalid preparation module name")
    implementation = project.workspace.joinpath(*module.split(".")).with_suffix(".py").resolve()
    if not implementation.is_relative_to(project.workspace) or not implementation.is_file():
        raise ValueError(f"{descriptor}: preparation module is not a local workspace file: {module}")
    source = load_source(descriptor)
    print(f"{project.relative}: preparing exact certificate inputs with {module}", flush=True)
    if archive is None:
        relative = descriptor.parent.relative_to(project.directory / "Certificates")
        receipt = fetch(source, project.workspace / ".lake" / "certificates" / project.relative / relative,
                        offline=offline, root=project.workspace)
        archive_path = receipt["archive"]
    else:
        local = Path(archive).resolve()
        verify_archive(local, source)
        archive_path = str(local)
    python = (interpreter(project.workspace, hook["requirements"], offline=offline)
              if "requirements" in hook else sys.executable)
    result = subprocess.run(
        [python, "-m", module, "--source", str(descriptor.resolve()),
         "--archive", archive_path], cwd=project.workspace)
    if result.returncode:
        raise ValueError(f"{project.relative}: certificate preparation failed ({module}, "
                         f"exit {result.returncode})")


def prepare(project, offline=False, archive=None):
    """Prepare registered groups in order; --archive overrides only the primary."""
    directory = project.directory / "Certificates"
    primary = directory / "Source.json"
    registrations = registered_sources(project)
    if archive is not None and primary not in registrations:
        raise ValueError(f"{project.relative}: --archive requires a registered primary Source.json")
    # Root before nested groups is deterministic and preserves old packages.
    for descriptor in sorted(registrations, key=lambda path: (
            len(path.relative_to(directory).parts), str(path))):
        _prepare_one(project, descriptor, registrations[descriptor], offline=offline,
                     archive=archive if descriptor == primary else None)

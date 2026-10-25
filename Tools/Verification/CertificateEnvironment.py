"""Select a Python interpreter for a local, exactly pinned preparation hook."""
import hashlib
from importlib import metadata
import json
import os
from pathlib import PurePosixPath
import re
import subprocess
import sys


def pinned_requirements(workspace, relative):
    """Read only simple name==version pins from a workspace-local requirements file."""
    if (not isinstance(relative, str) or not relative or
            PurePosixPath(relative).is_absolute() or
            any(part in ("", ".", "..") for part in relative.split("/"))):
        raise ValueError("Preparation requirements must name a relative workspace file")
    path = (workspace / relative).resolve()
    if not path.is_relative_to(workspace) or not path.is_file():
        raise ValueError(f"Preparation requirements are not a local workspace file: {relative}")
    raw = path.read_bytes()
    pins = {}
    for number, line in enumerate(raw.decode("utf-8").splitlines(), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        match = re.fullmatch(
            r"([A-Za-z0-9][A-Za-z0-9._-]*)==([A-Za-z0-9][A-Za-z0-9.!+_-]*)", line)
        if match is None:
            raise ValueError(f"{path}:{number}: expected a simple exact name==version pin")
        name, version = match.groups()
        name = re.sub(r"[-_.]+", "-", name).lower()
        if name in pins:
            raise ValueError(f"{path}:{number}: duplicate requirement: {name}")
        pins[name] = version
    if not pins:
        raise ValueError(f"Preparation requirements contain no exact pins: {path}")
    return path, raw, pins


def current_matches(pins):
    """Inspect installed distribution versions without importing preparation packages."""
    try:
        return all(metadata.version(name) == version for name, version in pins.items())
    except metadata.PackageNotFoundError:
        return False


def environment_matches(executable, pins):
    """Check an existing isolated environment with a metadata-only Python subprocess."""
    probe = """import importlib.metadata as metadata
import json
import sys
try:
    matches = all(metadata.version(name) == version
                  for name, version in json.loads(sys.argv[1]).items())
except metadata.PackageNotFoundError:
    matches = False
sys.exit(0 if matches else 1)
"""
    try:
        result = subprocess.run([str(executable), "-I", "-c", probe, json.dumps(pins)],
                                capture_output=True, text=True)
    except OSError:
        return False
    return result.returncode == 0


def interpreter(workspace, requirements, offline=False):
    """Reuse matching pins or prepare a cached venv; offline mode never installs anything."""
    path, raw, pins = pinned_requirements(workspace, requirements)
    if current_matches(pins):
        return sys.executable
    identity = hashlib.sha256(raw).hexdigest()
    version = f"{sys.version_info.major}.{sys.version_info.minor}"
    environment = workspace / ".lake" / "certificates" / "environments" / f"{version}-{identity}"
    executable = environment / ("Scripts/python.exe" if os.name == "nt" else "bin/python")
    if executable.is_file() and environment_matches(executable, pins):
        return str(executable)
    if offline:
        raise ValueError(f"Offline certificate preparation needs the exact versions from {path}; "
                         f"neither the current Python nor the cached environment {environment} "
                         "has them. Prepare the environment once without --offline.")
    print(f"Preparing pinned certificate environment: {environment}", flush=True)
    environment.parent.mkdir(parents=True, exist_ok=True)
    result = subprocess.run([sys.executable, "-m", "venv", str(environment)], cwd=workspace)
    if result.returncode:
        raise ValueError(f"Could not create certificate environment: {environment}")
    result = subprocess.run(
        [str(executable), "-m", "pip", "--disable-pip-version-check", "install", "-r", str(path)],
        cwd=workspace)
    if result.returncode:
        raise ValueError(f"Could not install pinned certificate requirements: {path}")
    if not environment_matches(executable, pins):
        raise ValueError(f"Certificate environment does not match the exact versions in {path}")
    return str(executable)

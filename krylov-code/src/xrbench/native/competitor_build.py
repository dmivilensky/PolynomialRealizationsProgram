"""Strict-FP compiler/cache for the full-C competitor executors.

Uses the same flags and SciPy LP64 capsule ABI as native XR. Compilation occurs
at module import, outside the oracle timer. The cache is outside the repository.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import subprocess
import sys
import sysconfig
from pathlib import Path

import numpy as np

from xrbench.native.build import HERE, _fingerprint

_loaded = None
_metadata = None


def load_native():
    global _loaded, _metadata
    if _loaded is not None:
        return _loaded
    import fcntl

    metadata = _fingerprint()
    sources = ["competitor_bridge.c", "competitor_common.c", "oaccel_native.c"]
    defines = []
    for file, flag in [("mslbfgs_native.c", "HAVE_MS"), ("sc_native.c", "HAVE_SC"),
                       ("sc_native_debug.c", "HAVE_SC_DEBUG")]:
        if (HERE / file).exists():
            sources.append(file)
            defines.append("-D" + flag)
    metadata = dict(metadata, module="competitor", sources=sources, defines=defines)
    key = hashlib.sha256(json.dumps(metadata, sort_keys=True).encode()).hexdigest()
    directory = Path(os.environ.get("XR_KERNEL_CACHE", "/tmp/clc-xr-kernels")) / key
    directory.mkdir(parents=True, exist_ok=True)
    extension = directory / ("_competitor_native" + sysconfig.get_config_var("EXT_SUFFIX"))
    with (directory / "build.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if not extension.is_file():
            temporary = extension.with_name(extension.name + f".{os.getpid()}.tmp")
            command = metadata["compiler"] + metadata["flags"] + defines + ["-shared"]
            if sys.platform == "darwin":
                command += ["-undefined", "dynamic_lookup"]
            command += ["-I" + sysconfig.get_paths()["include"], "-I" + np.get_include(), "-I" + str(HERE)]
            command += [str(HERE / name) for name in sources] + ["-o", str(temporary)]
            if sys.platform != "darwin":
                command += ["-lm"]
            completed = subprocess.run(command, capture_output=True, text=True)
            (directory / "build.log").write_text(completed.stdout + completed.stderr)
            if completed.returncode:
                temporary.unlink(missing_ok=True)
                raise ImportError("Competitor C compilation failed:\n" + completed.stderr[-10000:])
            temporary.replace(extension)
            (directory / "build.json").write_text(json.dumps(metadata, indent=2) + "\n")
    name = "xrbench._competitor_native"
    spec = importlib.util.spec_from_file_location(name, extension)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    sys.modules[name] = module
    _loaded = module
    _metadata = dict(metadata, build_key=key,
                     extension_sha256=hashlib.sha256(extension.read_bytes()).hexdigest(),
                     blas_abi="SciPy Cython capsules, LP64 int32, runtime signature checked")
    return module


def backend_metadata():
    load_native()
    return dict(_metadata)

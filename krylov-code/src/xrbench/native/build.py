"""Build/load XR's CPython extension outside the repository, with strict FP.

The scientific source hash includes these C sources. This additional build key
also fixes Python/NumPy ABI, SciPy version, compiler and flags. Imports build
before the campaign starts its oracle timer; solve never invokes a compiler.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import platform
import shlex
import subprocess
import sys
import sysconfig
from pathlib import Path

import numpy as np
import scipy

HERE = Path(__file__).resolve().parent
MODULE = "xrbench._xr_native"
_loaded = None
_metadata = None


def _fingerprint():
    compiler_setting = os.environ.get("CC")
    if sys.platform == "darwin" and not compiler_setting:
        compiler_setting = subprocess.check_output(["xcrun", "--find", "clang"], text=True).strip()
    compiler = shlex.split(compiler_setting or sysconfig.get_config_var("CC") or "cc")
    version = subprocess.run(compiler + ["--version"], check=True, capture_output=True, text=True)
    flags = [
        "-O3",
        "-std=c11",
        "-fPIC",
        "-Wall",
        "-Wextra",
        "-Werror",
        "-fno-fast-math",
        "-ffp-contract=off",
    ]
    if sys.platform == "darwin":
        sdk = (
            os.environ.get("SDKROOT")
            or subprocess.check_output(["xcrun", "--show-sdk-path"], text=True).strip()
        )
        flags += ["-isysroot", sdk]
    files = {
        path.name: hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(HERE.iterdir())
        if path.suffix in {".c", ".h"}
    }
    if (
        not {"xr_model.c", "xr_executor.c", "xr_bridge.c", "xr_native.h", "xr_executor.h"}
        <= files.keys()
    ):
        raise ImportError("Incomplete XR C source package")
    return dict(
        compiler=compiler,
        compiler_version=version.stdout.splitlines()[0],
        flags=flags,
        python_abi=sysconfig.get_config_var("SOABI"),
        machine=platform.machine(),
        platform=sys.platform,
        numpy=np.__version__,
        scipy=scipy.__version__,
        c_int_bytes=np.dtype(np.intc).itemsize,
        source_files=files,
    )


def load_native():
    global _loaded, _metadata
    if _loaded is not None:
        return _loaded
    if os.name != "posix":
        raise ImportError("The XR native build currently supports POSIX C compilers (macOS/Linux)")
    import fcntl

    metadata = _fingerprint()
    key = hashlib.sha256(json.dumps(metadata, sort_keys=True).encode()).hexdigest()
    cache = Path(os.environ.get("XR_KERNEL_CACHE", "/tmp/clc-xr-kernels"))
    directory = cache / key
    directory.mkdir(parents=True, exist_ok=True)
    extension = directory / ("_xr_native" + sysconfig.get_config_var("EXT_SUFFIX"))
    with (directory / "build.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if not extension.is_file():
            temporary = extension.with_name(extension.name + f".{os.getpid()}.tmp")
            command = metadata["compiler"] + metadata["flags"]
            command += ["-shared"]
            if sys.platform == "darwin":
                command += ["-undefined", "dynamic_lookup"]
            command += [
                "-I" + sysconfig.get_paths()["include"],
                "-I" + np.get_include(),
                "-I" + str(HERE),
            ]
            command += [str(HERE / name) for name in ("xr_bridge.c", "xr_executor.c", "xr_model.c")]
            command += ["-o", str(temporary)]
            if sys.platform != "darwin":
                command += ["-lm"]
            completed = subprocess.run(command, capture_output=True, text=True)
            (directory / "build.log").write_text(completed.stdout + completed.stderr)
            if completed.returncode:
                temporary.unlink(missing_ok=True)
                raise ImportError("XR C compilation failed:\n" + completed.stderr[-6000:])
            temporary.replace(extension)
            (directory / "build.json").write_text(json.dumps(metadata, indent=2) + "\n")
    specification = importlib.util.spec_from_file_location(MODULE, extension)
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    sys.modules[MODULE] = module
    _loaded = module
    _metadata = dict(
        metadata,
        build_key=key,
        extension_sha256=hashlib.sha256(extension.read_bytes()).hexdigest(),
        blas_abi="SciPy Cython capsules, LP64 int32, runtime signature checked",
    )
    return module


def backend_metadata():
    load_native()
    return dict(_metadata)


if __name__ == "__main__":
    load_native()
    print(json.dumps(backend_metadata(), indent=2))

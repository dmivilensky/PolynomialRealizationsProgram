# Native solvers and external data

Native dependencies, decoded CUTEst problems, Python environments and LIBSVM
arrays live outside `krylov-code`. `env.sh` sets the native locations and one
thread for each BLAS/OpenMP runtime.

## Compilers and Python

Use Linux or macOS with Python, a C11 compiler, Git, GNU Fortran and `ar`.
The pinned dependency set in `requirements.txt` requires Python 3.12 or later;
Python 3.13 matches the experiment environment. On macOS, install Xcode Command
Line Tools and Homebrew GCC; PyCUTEst locates the GNU Fortran runtime through
Homebrew. The setup script uses the existing system toolchain.

Create an external Python environment and install requirements as described
in the [README](../README.md). Then, from `krylov-code`:

```sh
bash scripts/setup_cutest.sh --install
source env.sh
bash scripts/setup_cutest.sh --check
```

Installation downloads and builds CUTEst/SIFDecode, selects the required SIF
families and compiles a small ROSENBR interface. Run it before starting solver
workers. Check mode inspects tools, libraries, decoder paths and SIF inputs;
it performs no downloads, builds or solves.

Primary installation references: [CUTEst](https://github.com/ralna/CUTEst),
[SIFDecode](https://github.com/ralna/SIFDecode),
[MASTSIF](https://github.com/ralna/SIF), and
[PyCUTEst](https://jfowkes.github.io/pycutest/).

## Storage

| Variable | Default | Contents |
|---|---|---|
| `XR_PYTHON` | `/tmp/clc-xr-venv/bin/python` | External Python interpreter. |
| `XR_NATIVE_DIR` | `/tmp/clc-xr-native` | CUTEst libraries, SIF sources and decoded interfaces. |
| `XR_KERNEL_CACHE` | `/tmp/clc-xr-kernels` | Compiled XR/competitor extensions and build records. |
| `XR_LIBSVM_DATA` | `/tmp/clc-xr-libsvm` | Downloads, prepared dense/CSR arrays and receipts. |

Choose persistent external directories for long-lived installations; operating
systems can clean `/tmp`. `CC`, `CXX`, `FC` select compilers, and `XR_BUILD_JOBS`
controls dependency-build parallelism. GNU Fortran must be available as
`gfortran` because PyCUTEst invokes it directly.

`env.sh` respects explicit `CUTEST`, `SIFDECODE`, `MASTSIF` and `PYCUTEST_CACHE`
settings. Unset inherited overrides when moving the native installation.
Setup rejects destinations inside the code directory. Source and build
checks protect existing external installations from incompatible reuse.

## C kernels

The XR and competitor extensions compile on first import, before solver
timing. Optional explicit prebuilds are:

```sh
PYTHONPATH=src "$XR_PYTHON" -B -m xrbench.native.build
PYTHONPATH=src "$XR_PYTHON" -B -c 'from xrbench.native.competitor_build import load_native; load_native()'
```

The extensions call installed SciPy Cython BLAS/LAPACK capsules and check their
LP64 integer ABI. Incremental QR uses compiled SciPy routines. Strict flags
include `-Wall -Wextra -Werror -fno-fast-math -ffp-contract=off`.
The external cache is keyed by sources, compiler, ABI and numerical libraries;
builds are atomic and locked. Import reports unsupported capsules or failed
compilation directly. Independent Python references support numerical tests.

## LIBSVM

```sh
"$XR_PYTHON" -B scripts/prepare_libsvm.py all
"$XR_PYTHON" -B scripts/prepare_libsvm.py check
```

Downloading resumes partial files. Dense epsilon is prepared as a memory map;
sparse datasets use CSR arrays. Receipts contain source and prepared-array
hashes. Data loading, normalization and warm-up precede solver timing.

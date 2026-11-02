# shellcheck shell=bash
# Environment for xrbench (source it: `source env.sh`).
# Persistent, machine-local installation; caller-provided paths take precedence.
# BASH_SOURCE in bash, $0 while sourced in zsh (also used via problems.cutest.ensure_env).
_xr_root="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")" && pwd)"
_xr_native="${XR_NATIVE_DIR:-/tmp/clc-xr-native}"
export CUTEST="${CUTEST:-$_xr_native/cutest}"
export SIFDECODE="${SIFDECODE:-$_xr_native/cutest}"
export MASTSIF="${MASTSIF:-$_xr_native/src/mastsif}"
export PYCUTEST_CACHE="${PYCUTEST_CACHE:-$_xr_native/pycutest_cache}"
unset _xr_native
unset _xr_root
# PyCUTEst builds a C extension for each problem via setuptools. Use the Xcode
# compiler and SDK rather than an unrelated Homebrew LLVM found earlier in PATH.
if [ "$(uname -s)" = Darwin ]; then
  export CC="${CC:-$(xcrun --find clang)}"
  export CXX="${CXX:-$(xcrun --find clang++)}"
  export SDKROOT="${SDKROOT:-$(xcrun --sdk macosx --show-sdk-path)}"
  export MACOSX_DEPLOYMENT_TARGET="${MACOSX_DEPLOYMENT_TARGET:-$(sw_vers -productVersion | cut -d. -f1-2)}"
fi
# Parallel jobs, one BLAS thread each.
export OMP_NUM_THREADS=1
export OPENBLAS_NUM_THREADS=1
export MKL_NUM_THREADS=1
export VECLIB_MAXIMUM_THREADS=1
export BLIS_NUM_THREADS=1

"""Test environment: one BLAS thread and optional native CUTEst defaults."""

import os
from pathlib import Path

import pytest

for key in (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "BLIS_NUM_THREADS",
):
    os.environ[key] = "1"


@pytest.fixture
def native_cutest():
    """Native regressions run when CUTEst is installed; algebra tests stay portable."""
    from xrbench.problems.cutest import ensure_env

    ensure_env()
    if not (Path(os.environ["CUTEST"]) / "include/cutest.h").exists():
        pytest.skip("Optional native CUTEst installation is unavailable")
    pytest.importorskip("pycutest")

"""Full-batch, strongly convex logistic objectives on pinned public data.

Source: LIBSVM data collection (Chang and Lin); original data provenance is
linked by libsvm.json. External preparation normalizes nonzero feature rows;
the appended intercept has the same positive L2 penalty as every coefficient.
Only actual f/g requests are evaluated; no optimum or Hessian is supplied.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path

import numpy as np
from scipy import sparse
from scipy.special import expit

CATALOG = Path(__file__).with_suffix(".json")


def catalog():
    return json.loads(CATALOG.read_text())


def data_root():
    return Path(os.environ.get("XR_LIBSVM_DATA", "/tmp/clc-xr-libsvm")).resolve()


def data_receipts():
    """Pin prepared data once per manifest, before any solver is measured."""
    out = {}
    for spec in catalog()["datasets"]:
        receipt = data_root() / spec["name"] / "receipt.json"
        value = json.loads(receipt.read_text())
        if (value["rows"], value["features"]) != (spec["rows"], spec["features"]):
            raise ValueError("LIBSVM prepared shape disagrees with catalog")
        out[spec["name"]] = value
    return out


def receipt_hash(name):
    return hashlib.sha256((data_root() / name / "receipt.json").read_bytes()).hexdigest()


def validate_prepared_data(expected):
    """Refuse changed receipts/arrays before any job can become a failure row."""
    for name, receipt in expected.items():
        folder = data_root() / name
        if json.loads((folder / "receipt.json").read_text()) != receipt:
            raise ValueError("Frozen LIBSVM data receipt changed: " + name)
        for filename, digest in receipt["arrays"].items():
            checksum = hashlib.sha256()
            with (folder / filename).open("rb") as stream:
                for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
                    checksum.update(block)
            if checksum.hexdigest() != digest:
                raise ValueError("Frozen LIBSVM data array changed: " + name + "/" + filename)


class LogisticProblem:
    convex = True
    err_from_f = False
    fstar = None

    def __init__(self, dataset, regularization):
        spec = next(s for s in catalog()["datasets"] if s["name"] == dataset)
        folder = data_root() / dataset
        self.receipt = json.loads((folder / "receipt.json").read_text())
        self.regularization = float(regularization)
        if not np.isfinite(self.regularization) or self.regularization <= 0:
            raise ValueError("Logistic regularization must be finite and positive")
        self.n = spec["features"] + 1
        self.samples = spec["rows"]
        if (self.receipt["rows"], self.receipt["features"]) != (self.samples, self.n - 1):
            raise ValueError("Prepared LIBSVM shape mismatch")
        self.y = np.load(folder / "labels.npy", mmap_mode="r")
        if spec["storage"] == "dense":
            self.A = np.load(folder / "matrix.npy", mmap_mode="r")
        else:
            self.A = sparse.csr_matrix(
                (np.load(folder / "data.npy", mmap_mode="r"),
                 np.load(folder / "indices.npy", mmap_mode="r"),
                 np.load(folder / "indptr.npy", mmap_mode="r")),
                shape=(self.samples, self.n - 1), copy=False,
            )
        if self.A.shape != (self.samples, self.n - 1) or self.y.shape != (self.samples,):
            raise ValueError("Invalid prepared LIBSVM arrays")
        # Page in the identical external design before timing every solver.
        # This reads no objective/gradient and does not reveal curvature.
        values = self.A if spec["storage"] == "dense" else self.A.data
        self._data_warmup_sum = float(np.sum(values))
        self._data_warmup_sum += float(np.sum(self.y))
        if spec["storage"] == "csr":
            self._data_warmup_sum += float(np.sum(self.A.indices)) + float(np.sum(self.A.indptr))
        # Share the forward design product between separate f(x), g(x)
        # requests, just as fg(x) does. Keep only one immutable point key and
        # one read-only sample vector; a function request computes no gradient.
        self._margin_key = None
        self._cached_margin = None
        self.x0 = np.zeros(self.n)
        self.name = f"LIBSVM-{dataset}-lambda{self.regularization:g}"
        self.meta = dict(source="LIBSVM", dataset=dataset, samples=self.samples,
                         regularization=self.regularization, storage=spec["storage"],
                         receipt_sha256=receipt_hash(dataset), convex_quadratic=False)

    def _margin(self, x):
        point = np.asarray(x, dtype=np.float64)
        # Full-point bytes include the regularized intercept and cannot alias
        # a caller's mutable workspace. Byte equality also preserves the
        # shared oracle's distinction between positive and negative zero.
        key = point.tobytes()
        if key != self._margin_key:
            margin = self.y * (self.A @ point[:-1] + point[-1])
            margin.setflags(write=False)
            self._cached_margin = margin
            self._margin_key = key
        return self._cached_margin

    def _gradient(self, x, margin):
        coefficients = -self.y * expit(-margin) / self.samples
        g = np.empty(self.n)
        g[:-1] = self.A.T @ coefficients
        g[-1] = np.sum(coefficients)
        g += self.regularization * x
        return g

    def f(self, x):
        return float(np.mean(np.logaddexp(0.0, -self._margin(x)))
                     + 0.5 * self.regularization * np.dot(x, x))

    def grad(self, x):
        return self._gradient(x, self._margin(x))

    def fg(self, x):
        margin = self._margin(x)
        value = float(np.mean(np.logaddexp(0.0, -margin))
                      + 0.5 * self.regularization * np.dot(x, x))
        return value, self._gradient(x, margin)

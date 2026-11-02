#!/usr/bin/env python3
"""Download official LIBSVM training data and prepare external mmap arrays.

Downloads survive interruption as .partial files; each completed source and
prepared array is SHA256-pinned. No data/matrix is written inside the checkout.
Run before freezing an experiment manifest. Parsing is serial and bounded in
memory even for epsilon; a receipt is committed only after all arrays exist.
"""

from __future__ import annotations

import argparse
import bz2
import hashlib
import json
import subprocess
import sys
import time
from array import array
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
BASE_URL = "https://www.csie.ntu.edu.tw/~cjlin/libsvmtools/datasets/binary/"


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def download(spec, folder):
    raw = folder / "raw"
    raw.mkdir(parents=True, exist_ok=True)
    target = raw / spec["file"]
    if target.is_file():
        return target
    part = target.with_name(target.name + ".partial")
    cmd = ["curl", "--http1.1", "--fail", "--location",
           "--connect-timeout", "30", "--speed-limit", "1024", "--speed-time", "120",
           "--continue-at", "-", "--output", str(part), BASE_URL + spec["file"]]
    print("Downloading", spec["name"], flush=True)
    # curl's built-in retry restores the output to the offset at invocation.
    # A server disconnect after a long transfer would therefore discard that
    # attempt's entire progress. A fresh process resolves -C - from the actual
    # retained file size, including bytes received before the disconnect.
    for attempt in range(8):
        result = subprocess.run(cmd, check=False)
        if result.returncode == 0:
            part.replace(target)
            return target
        if attempt == 7:
            raise subprocess.CalledProcessError(result.returncode, cmd)
        retained = part.stat().st_size if part.exists() else 0
        print(f"Download interrupted ({result.returncode}); retained {retained} bytes; "
              f"resume attempt {attempt + 2}/8 in 5 seconds", flush=True)
        time.sleep(5)


def verify(folder, receipt):
    for filename, digest in receipt["arrays"].items():
        if sha(folder / filename) != digest:
            raise ValueError("Prepared array checksum mismatch: " + filename)


def prepare(spec, folder, source):
    import numpy as np

    target = folder / spec["name"]
    target.mkdir(exist_ok=True)
    rp = target / "receipt.json"
    source_sha = sha(source)
    if rp.is_file():
        receipt = json.loads(rp.read_text())
        if receipt["raw_sha256"] != source_sha:
            raise ValueError("Previously prepared source checksum changed")
        verify(target, receipt)
        print("Verified", spec["name"], flush=True)
        return
    rows, columns = spec["rows"], spec["features"]
    labels = np.lib.format.open_memmap(target / "labels.npy", mode="w+", dtype="float64", shape=(rows,))
    dense = spec["storage"] == "dense"
    if dense:
        matrix = np.lib.format.open_memmap(target / "matrix.npy", mode="w+", dtype="float64", shape=(rows, columns))
        matrix[:] = 0
    else:
        values, indices, indptr = array("d"), array("i"), array("i", [0])
    opener = bz2.open if source.suffix == ".bz2" else open
    count = 0
    started = time.monotonic()
    with opener(source, "rt", encoding="ascii") as stream:
        for line in stream:
            if not line.strip():
                continue
            if count >= rows:
                raise ValueError("More source rows than declared")
            tokens = np.fromstring(line.replace(":", " "), sep=" ")
            if tokens.size < 1 or tokens.size % 2 != 1 or not np.all(np.isfinite(tokens)):
                raise ValueError("Invalid LIBSVM source row")
            labels[count] = tokens[0]
            jraw = tokens[1::2]
            js = jraw.astype(np.int32) - 1
            vs = tokens[2::2]
            if (not np.all(jraw == js + 1) or np.any(js < 0) or np.any(js >= columns)
                    or np.any(np.diff(js) <= 0)):
                raise ValueError("Non-increasing or out-of-range feature index")
            norm = float(np.linalg.norm(vs))
            if norm > 0:
                vs = vs / norm
            if dense:
                matrix[count, js] = vs
            else:
                keep = vs != 0
                values.frombytes(vs[keep].astype("float64").tobytes())
                indices.frombytes(js[keep].astype("int32").tobytes())
                indptr.append(len(values))
            count += 1
            if count % 20000 == 0:
                print(f"{spec['name']}: {count}/{rows} rows, {time.monotonic()-started:.1f}s", flush=True)
    if count != rows:
        raise ValueError(f"Expected {rows} rows, found {count}")
    classes = np.unique(labels)
    if classes.size != 2:
        raise ValueError("Expected two finite label values")
    labels[:] = np.where(labels == classes[1], 1., -1.)
    labels.flush()
    filenames = ["labels.npy"]
    if dense:
        matrix.flush()
        filenames.append("matrix.npy")
        nnz = int(np.count_nonzero(matrix))
        del matrix
    else:
        for name, contents in (("data", values), ("indices", indices), ("indptr", indptr)):
            np.save(target / (name + ".npy"), np.asarray(contents))
            filenames.append(name + ".npy")
        nnz = len(values)
    receipt = dict(version=1, dataset=spec["name"], rows=rows, features=columns,
                   nnz=nnz, storage=spec["storage"], source_url=BASE_URL + spec["file"],
                   raw_sha256=source_sha, negative_label=float(classes[0]), positive_label=float(classes[1]),
                   normalization="nonzero feature rows divided by their Euclidean norm; regularized intercept added at evaluation",
                   arrays={name: sha(target / name) for name in filenames})
    temporary = rp.with_suffix(".tmp")
    temporary.write_text(json.dumps(receipt, indent=2) + "\n")
    temporary.replace(rp)
    print("Prepared", spec["name"], "nnz", nnz, flush=True)


def main():
    from xrbench.problems.libsvm import catalog, data_root

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("download", "prepare", "check", "all"))
    parser.add_argument("--dataset", action="append")
    args = parser.parse_args()
    folder = data_root()
    if folder.is_relative_to(ROOT):
        parser.error("XR_LIBSVM_DATA must be outside the repository")
    folder.mkdir(parents=True, exist_ok=True)
    specs = catalog()["datasets"]
    if args.dataset:
        if set(args.dataset) - {s["name"] for s in specs}:
            parser.error("Unknown dataset")
        specs = [s for s in specs if s["name"] in args.dataset]
    for spec in specs:
        if args.action == "check":
            receipt = json.loads((folder / spec["name"] / "receipt.json").read_text())
            verify(folder / spec["name"], receipt)
            print("Verified", spec["name"], flush=True)
        else:
            source = download(spec, folder)
            if args.action in {"all", "prepare"}:
                prepare(spec, folder, source)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Render every completed release series without executing an optimizer.

Measured histories, manifests and producer scripts are immutable inputs. The
pinned producers retain their original source hashes; their generated report
reproduction blocks are adjusted here to the actual release paths and workers.
Run from krylov-code: python -B scripts/render_release.py --output artifacts/run
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import shlex
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
PRODUCERS = ("settings_study", "supplement", "local_study")


def _load_script(name):
    path = ROOT / "scripts" / (name + ".py")
    spec = importlib.util.spec_from_file_location("xr_release_renderer_" + name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _read_json(path):
    return json.loads(Path(path).read_text())


def _complete_jobs(rows, manifest, label):
    actual = [row["job_id"] for row in rows]
    expected = [job["id"] for job in manifest["jobs"]]
    if len(set(actual)) != len(actual) or len(set(expected)) != len(expected):
        raise ValueError(f"{label}: duplicate observed or scheduled job IDs")
    if set(actual) != set(expected):
        raise ValueError(f"{label}: every scheduled job is required before release rendering")


def _inputs(base):
    """Refuse incomplete inputs before generating any release artifact."""
    from xrbench.campaign import read_history, validate_history

    main = _read_json(base / "full/manifest.json")
    rows = read_history(base / "full/history.jsonl")
    validate_history(rows, main)
    _complete_jobs(rows, main, "Main campaign")
    scripts = {name: _load_script(name) for name in PRODUCERS}
    settings = _read_json(base / "settings/logs/manifest.json")
    settings_rows = read_history(base / "settings/logs/history.jsonl")
    scripts["settings_study"].validate_frozen(settings)
    scripts["settings_study"].validate_rows(settings_rows, settings, complete=True)
    supplement = _read_json(base / "supplement/logs/manifest.json")
    supplement_rows = read_history(base / "supplement/logs/history.jsonl")
    scripts["supplement"].validate_frozen(supplement)
    _complete_jobs(supplement_rows, supplement, "Supplement")
    local = _read_json(base / "local/logs/manifest.json")
    local_rows = [
        json.loads(line) for line in (base / "local/logs/history.jsonl").read_text().splitlines()
    ]
    if scripts["local_study"].validate(local, local_rows):
        raise ValueError(
            "Local study: every scheduled trajectory is required before release rendering"
        )
    for label, manifest in (("Settings", settings), ("Supplement", supplement)):
        if Path(manifest["base_directory"]).resolve() != (base / "full").resolve():
            raise ValueError(f"{label}: the pinned main inputs belong to another release")
    return dict(
        main=main,
        rows=rows,
        settings=settings,
        supplement=supplement,
        local=local,
        local_rows=local_rows,
        scripts=scripts,
    )


def _fingerprints(base):
    paths = [base / "full" / name for name in ("manifest.json", "history.jsonl")]
    paths += [
        base / phase / "logs" / name
        for phase in ("settings", "supplement", "local")
        for name in ("manifest.json", "history.jsonl")
    ]
    paths += [ROOT / "scripts" / (name + ".py") for name in PRODUCERS]
    return {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}


def _argument(path):
    path = Path(path).resolve()
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def _reproduction_block(text, commands):
    """Replace one fenced sh block under Reproduction, preserving all other bytes."""
    heading = re.search(r"(?m)^## Reproduction[ \t]*$", text)
    if heading is None:
        raise ValueError("Generated report lacks its Reproduction section")
    following = re.search(r"(?m)^## ", text[heading.end() :])
    end = heading.end() + following.start() if following else len(text)
    section = text[heading.end() : end]
    blocks = list(re.finditer(r"(?ms)^```sh[ \t]*\n.*?^```[ \t]*(?=\n|$)", section))
    if len(blocks) != 1:
        raise ValueError("Expected exactly one reproduction shell block")
    block = blocks[0]
    replacement = "```sh\n" + "\n".join(commands) + "\n```"
    start, stop = heading.end() + block.start(), heading.end() + block.end()
    return text[:start] + replacement + text[stop:]


def _correct_reproduction(base, phase, manifest):
    script = "settings_study" if phase == "settings" else "supplement"
    arguments = ["python", "-B", f"scripts/{script}.py"]
    run = arguments + [
        "run",
        "--main",
        _argument(base / "full"),
        "--output",
        _argument(base / phase),
    ]
    if phase == "supplement":
        run += ["--workers", str(manifest["workers"])]
    commands = [
        f"# Run from krylov-code; use {manifest['workers']} worker(s) and one BLAS thread.",
        shlex.join(run),
        shlex.join(arguments + ["resume", "--output", _argument(base / phase)]),
        shlex.join(["python", "-B", "scripts/render_release.py", "--output", _argument(base)]),
    ]
    path = base / phase / "REPORT.md"
    path.write_text(_reproduction_block(path.read_text(), commands))


def render_release(output):
    """Use only existing render/validation APIs; no execute/run/worker API is called."""
    from xrbench.campaign import materialize_aliases
    from xrbench.study import render

    base = Path(output).resolve()
    before = _fingerprints(base)
    inputs = _inputs(base)
    main = inputs["main"]
    summaries = {
        "full": render(
            materialize_aliases(inputs["rows"], main),
            base / "full",
            expected_methods=main["methods"],
            expected_problems=main["problems"],
        )
    }
    for phase, name in (("settings", "settings_study"), ("supplement", "supplement")):
        summaries[phase] = inputs["scripts"][name].render(base / phase)
        _correct_reproduction(base, phase, inputs[phase])
    summaries["local"] = inputs["scripts"]["local_study"].render(
        base / "local", inputs["local"], inputs["local_rows"]
    )
    if _fingerprints(base) != before:
        raise RuntimeError("Rendering changed a frozen manifest, history or measured producer")
    return dict(
        render_only=True, output=str(base), series=list(summaries), frozen_inputs_unchanged=True
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts/run")
    args = parser.parse_args()
    print(json.dumps(render_release(args.output), indent=2))


if __name__ == "__main__":
    main()

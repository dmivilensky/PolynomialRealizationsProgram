#!/usr/bin/env python3
"""One resumable, sequential release: primary, settings, supplement and local.

The screen launcher owns terminal persistence; this runner owns a file lock,
phase logs, source validation, cancellation and continuation of saved jobs.
"""

from __future__ import annotations

import argparse
import fcntl
import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
ACTIVE = None


def stop(signum, _frame):
    # Unwind the outer Popen.wait first: waiting recursively inside a signal
    # handler can deadlock on Popen's non-reentrant waitpid lock.
    raise SystemExit(128 + signum)


def command(args):
    global ACTIVE
    print(time.strftime("%Y-%m-%d %H:%M:%S"), "RUN", *map(str, args), flush=True)
    ACTIVE = subprocess.Popen([str(x) for x in args], cwd=ROOT, start_new_session=True)
    try:
        code = ACTIVE.wait()
    except BaseException:
        if ACTIVE.poll() is None:
            try:
                os.killpg(ACTIVE.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            except PermissionError:
                ACTIVE.terminate()
            try:
                ACTIVE.wait(timeout=15)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(ACTIVE.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                except PermissionError:
                    ACTIVE.kill()
                ACTIVE.wait(timeout=5)
        raise
    finally:
        ACTIVE = None
    if code:
        raise subprocess.CalledProcessError(code, args)


def write_state(base, phase, status):
    value = dict(phase=phase, status=status, updated=time.time(), pid=os.getpid())
    tmp = base / "logs/state.tmp"
    tmp.write_text(json.dumps(value, indent=2) + "\n")
    tmp.replace(base / "logs/state.json")


def stop_runner(base):
    """Signal the validated runner itself: closing screen may leave it alive."""
    with (base / "logs/runner.lock").open("a+") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            pass
        else:
            print("No active marathon writer")
            return
        lock.seek(0)
        pid = int(lock.read().strip())
        description = subprocess.check_output(["ps", "-p", str(pid), "-o", "command="], text=True)
        if str(Path(__file__).resolve()) not in description or str(base) not in description:
            raise ValueError("Runner PID no longer identifies this marathon; refusing to signal")
        os.kill(pid, signal.SIGTERM)
        for _ in range(200):
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                time.sleep(0.1)
            else:
                print("Runner and its active worker group stopped; saved results retained")
                return
        raise RuntimeError("Runner did not release its writer lock after termination")


def run(base):
    python = [sys.executable, "-B", "-u"]
    # Data preparation is separately resumable; caller may complete it first.
    write_state(base, "data", "running")
    command(python + [ROOT / "scripts/prepare_libsvm.py", "all"])
    command(python + [ROOT / "scripts/prepare_libsvm.py", "check"])
    stages = [
        (
            "full",
            base / "full/manifest.json",
            python
            + ["-m", "xrbench", "run", "--workers", "1", "--libsvm", "--output", base / "full"],
            python + ["-m", "xrbench", "resume", "--output", base / "full"],
        ),
        (
            "settings",
            base / "settings/logs/manifest.json",
            python
            + [
                ROOT / "scripts/settings_study.py",
                "run",
                "--main",
                base / "full",
                "--output",
                base / "settings",
            ],
            python + [ROOT / "scripts/settings_study.py", "resume", "--output", base / "settings"],
        ),
        (
            "supplement",
            base / "supplement/logs/manifest.json",
            python
            + [
                ROOT / "scripts/supplement.py",
                "run",
                "--workers",
                "1",
                "--main",
                base / "full",
                "--output",
                base / "supplement",
            ],
            python + [ROOT / "scripts/supplement.py", "resume", "--output", base / "supplement"],
        ),
        (
            "local",
            base / "local/logs/manifest.json",
            python + [ROOT / "scripts/local_study.py", "run", "--output", base / "local"],
            python + [ROOT / "scripts/local_study.py", "run", "--output", base / "local"],
        ),
    ]
    for phase, manifest, fresh, resume in stages:
        write_state(base, phase, "running")
        command(resume if manifest.exists() else fresh)
        history = base / phase / ("history.jsonl" if phase == "full" else "logs/history.jsonl")
        rows = [json.loads(line) for line in history.read_text().splitlines()]
        technical = [r for r in rows if r.get("status") in {"setup_error", "worker_failure"}]
        if technical:
            raise RuntimeError(
                f"{phase}: {len(technical)} technical failures require review; saved observations retained"
            )
        write_state(base, phase, "complete")
    write_state(base, "render", "running")
    command(python + [ROOT / "scripts/render_release.py", "--output", base])
    write_state(base, "render", "complete")
    write_state(base, "audit", "running")
    command(python + [ROOT / "scripts/release_audit.py", "--output", base])
    command(python + [ROOT / "scripts/paper_assets.py", "--run", base])
    write_state(base, "all", "complete")
    print("All measured series and generated artifacts complete.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("run", "status", "stop"))
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts/run")
    args = parser.parse_args()
    base = args.output.resolve()
    (base / "logs").mkdir(parents=True, exist_ok=True)
    if args.action == "stop":
        stop_runner(base)
        return
    if args.action == "status":
        state = base / "logs/state.json"
        print(state.read_text() if state.exists() else "No run started")
        for phase in ("full", "settings", "supplement", "local"):
            folder = base / phase
            history = folder / ("history.jsonl" if phase == "full" else "logs/history.jsonl")
            if history.exists():
                print(phase, "saved lines", sum(1 for _ in history.open()))
        return
    for name in (
        "OMP_NUM_THREADS",
        "OPENBLAS_NUM_THREADS",
        "MKL_NUM_THREADS",
        "VECLIB_MAXIMUM_THREADS",
        "BLIS_NUM_THREADS",
    ):
        os.environ[name] = "1"
    os.environ["PYTHONPATH"] = str(ROOT / "src")
    os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
    for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(sig, stop)
    with (base / "logs/runner.lock").open("a+") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            parser.error("Another process owns the marathon writer lock")
        lock.seek(0)
        lock.truncate()
        lock.write(str(os.getpid()) + "\n")
        lock.flush()
        try:
            run(base)
        except BaseException:
            write_state(base, "interrupted", "resume_required")
            raise


if __name__ == "__main__":
    main()

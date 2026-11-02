"""A disconnected transfer must keep its newly received bytes on retry."""

import importlib.util
import subprocess
from pathlib import Path

import pytest


def downloader():
    path = Path(__file__).parents[1] / "scripts/prepare_libsvm.py"
    spec = importlib.util.spec_from_file_location("libsvm_download_test", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_disconnected_transfer_resumes_new_bytes(tmp_path, monkeypatch):
    module = downloader()
    partial = tmp_path / "raw/data.bz2.partial"
    partial.parent.mkdir()
    partial.write_bytes(b"old")
    offsets = []

    def transfer(cmd, *, check):
        assert check is False
        assert "--retry" not in cmd and "--retry-all-errors" not in cmd
        assert cmd[cmd.index("--continue-at") + 1] == "-"
        assert Path(cmd[cmd.index("--output") + 1]) == partial
        offsets.append(partial.stat().st_size)
        with partial.open("ab") as stream:
            stream.write(b"new" if len(offsets) == 1 else b"tail")
        return subprocess.CompletedProcess(cmd, 18 if len(offsets) == 1 else 0)

    monkeypatch.setattr(module.subprocess, "run", transfer)
    monkeypatch.setattr(module.time, "sleep", lambda _: None)
    target = module.download({"name": "data", "file": "data.bz2"}, tmp_path)
    assert offsets == [3, 6]
    assert target.read_bytes() == b"oldnewtail"
    assert not partial.exists()


def test_exhausted_retries_leave_resumable_file(tmp_path, monkeypatch):
    module = downloader()
    partial = tmp_path / "raw/data.bz2.partial"

    def transfer(cmd, *, check):
        with partial.open("ab") as stream:
            stream.write(b"x")
        return subprocess.CompletedProcess(cmd, 18)

    monkeypatch.setattr(module.subprocess, "run", transfer)
    monkeypatch.setattr(module.time, "sleep", lambda _: None)
    with pytest.raises(subprocess.CalledProcessError):
        module.download({"name": "data", "file": "data.bz2"}, tmp_path)
    assert partial.read_bytes() == b"x" * 8
    assert not (tmp_path / "raw/data.bz2").exists()

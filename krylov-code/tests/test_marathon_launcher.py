"""Detached start must fork, and live macOS sockets must block a duplicate."""

import os
import subprocess
import sys
from pathlib import Path

import pytest


@pytest.mark.parametrize("already_active", [False, True])
def test_start_handles_screen_socket_exit_status(tmp_path, already_active):
    fake_bin = tmp_path / "bin"
    fake_bin.mkdir()
    fake_screen = fake_bin / "screen"
    fake_screen.write_text(
        '#!/bin/sh\n'
        'if [ "$1" = "-ls" ]; then\n'
        '  printf "%s\\n" "$XR_TEST_SOCKET_LIST"\n'
        '  exit 1\n'
        'fi\n'
        'printf "%s\\n" "$@" > "$XR_TEST_SCREEN_LOG"\n'
    )
    fake_screen.chmod(0o755)
    log = tmp_path / "screen-args.txt"
    session = "xr-launcher-test"
    env = dict(os.environ, PATH=str(fake_bin) + os.pathsep + os.environ["PATH"],
               XR_PYTHON=sys.executable, XR_SCREEN_SESSION=session,
               XR_MARATHON_OUTPUT=str(tmp_path / "output"),
               XR_TEST_SOCKET_LIST=f"\t1234.{session}\t(Detached)" if already_active else "",
               XR_TEST_SCREEN_LOG=str(log))
    script = Path(__file__).parents[1] / "scripts/marathon.sh"
    result = subprocess.run(["bash", str(script), "start"], env=env,
                            text=True, capture_output=True, timeout=10)
    if already_active:
        assert result.returncode == 1
        assert "Screen session already active" in result.stderr
        assert not log.exists(), "A duplicate server must never be launched"
    else:
        assert result.returncode == 0, result.stderr
        assert log.read_text().splitlines() == ["-dmS", session, "bash", str(script), "_run"]
        assert "Started " + session in result.stdout

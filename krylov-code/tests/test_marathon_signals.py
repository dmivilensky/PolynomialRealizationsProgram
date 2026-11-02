"""A real interrupted Popen.wait must unwind before child-group cleanup."""

import os
import signal
import subprocess
import sys
import time
from pathlib import Path


def test_interrupted_wait_cleans_up_actual_child_group(tmp_path):
    script = Path(__file__).parents[1] / "scripts/marathon.py"
    child_file = tmp_path / "child.pid"
    payload = f"""
import importlib.util,signal,sys
spec=importlib.util.spec_from_file_location('marathon_signal_test',{str(script)!r})
m=importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
signal.signal(signal.SIGTERM,m.stop)
m.command([sys.executable,'-c',"import os,time;open({str(child_file)!r},'w').write(str(os.getpid()));time.sleep(60)"])
"""
    controller = subprocess.Popen([sys.executable, "-B", "-c", payload],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    child_pid = None
    try:
        deadline = time.monotonic() + 5
        while not child_file.exists() and time.monotonic() < deadline:
            time.sleep(.01)
        assert child_file.exists(), "Controller never started the worker"
        child_pid = int(child_file.read_text())
        controller.send_signal(signal.SIGTERM)
        _, stderr = controller.communicate(timeout=5)
        assert controller.returncode == 128 + signal.SIGTERM, stderr.decode()
        try:
            os.kill(child_pid, 0)
        except ProcessLookupError:
            pass
        else:
            raise AssertionError("Interrupted controller left its worker alive")
    finally:
        if controller.poll() is None:
            controller.kill()
            controller.wait()
        if child_pid:
            try:
                os.kill(child_pid, signal.SIGKILL)
            except ProcessLookupError:
                pass

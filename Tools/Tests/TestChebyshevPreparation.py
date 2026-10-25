"""Check acquisition gates and invalidation of the Chebyshev II preparation cache."""
from contextlib import redirect_stdout
import hashlib
import io
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

from Tools.Certificates import ChebyshevPrepare as preparation


class ChebyshevPreparationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="chebyshev-preparation-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        patch = mock.patch.object(preparation, "ROOT", self.root)
        patch.start()
        self.addCleanup(patch.stop)
        self.source = self.root / "chebyshev2/Certificates/Source.json"
        self.source.parent.mkdir(parents=True)
        self.archive = self.root / "external-proof.tar.xz"
        self.archive.write_bytes(b"pinned mathematical data")
        descriptor = {"format": "POLYNOMIAL_REALIZATIONS_CERTIFICATE_SOURCE",
                      "repository": "example/source", "revision": "a" * 40,
                      "archive_path": "results/proof.tar.xz",
                      "archive_bytes": self.archive.stat().st_size,
                      "archive_sha256": hashlib.sha256(self.archive.read_bytes()).hexdigest()}
        self.source.write_text(json.dumps(descriptor))
        self.witness = self.source.with_name("Witness.lean")
        self.witness.write_text("example : 1 = 1 := rfl\n")
        tools = self.root / "Tools/Certificates"
        tools.mkdir(parents=True)
        (tools / "Generator.py").write_text("# fixture\n")

    def test_mismatched_archive_never_runs_reconstruction(self):
        self.archive.write_bytes(b"x" * self.archive.stat().st_size)
        with mock.patch.object(preparation.subprocess, "run") as run:
            with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
                preparation.prepare(self.source, self.archive)
        run.assert_not_called()

    def test_cache_rechecks_changed_witnesses_and_tools(self):
        with mock.patch.object(preparation.subprocess, "run",
                               return_value=SimpleNamespace(returncode=0)) as run, \
                redirect_stdout(io.StringIO()):
            first = preparation.prepare(self.source, self.archive)
            self.assertFalse(first["cached"])
            self.assertEqual(run.call_count, len(preparation.STEPS))
            self.assertTrue(preparation.prepare(self.source, self.archive)["cached"])
            self.assertEqual(run.call_count, len(preparation.STEPS))
            self.witness.write_text("example : 2 = 2 := rfl\n")
            self.assertFalse(preparation.prepare(self.source, self.archive)["cached"])
            self.assertEqual(run.call_count, 2 * len(preparation.STEPS))
            (self.root / "Tools/Certificates/Generator.py").write_text("# changed\n")
            self.assertFalse(preparation.prepare(self.source, self.archive)["cached"])
            self.assertEqual(run.call_count, 3 * len(preparation.STEPS))

    def test_failed_comparison_never_creates_success_receipt(self):
        with mock.patch.object(preparation.subprocess, "run",
                               return_value=SimpleNamespace(returncode=1)), \
                redirect_stdout(io.StringIO()):
            with self.assertRaisesRegex(ValueError, "reconstruction failed"):
                preparation.prepare(self.source, self.archive)
        self.assertFalse(list((self.root / ".lake").rglob("preparation.json")))


if __name__ == "__main__":
    unittest.main()

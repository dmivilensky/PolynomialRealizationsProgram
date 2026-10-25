"""Rehashed but mathematically false Part II proposals must fail in Lean."""
import copy
from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import unittest

from Tools.Certificates.PolyakPartII import Payload, Rational, Trig


class PartIIMathematicsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.workspace = Path(__file__).resolve().parents[2]
        archive = cls.workspace / "polyak-code/part2/proof/proof.tar.xz"
        if shutil.which("lake") is None or not archive.is_file():
            raise unittest.SkipTest("Fresh Part II archive and Lake are required")
        cls.original = Payload.read_archive(archive)

    def reject_in_lean(self, group, mutate, converter, output, diagnostic):
        folder = self.workspace / ".lake/checks/polyak/stage22-negative"
        folder.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix=group+"-", dir=folder) as temporary:
            root = Path(temporary)
            proposal = copy.deepcopy(self.original["groups"][group])
            mutate(proposal)
            raw = dict(self.original["raw"])
            raw[group+".json"] = json.dumps({"schema": Payload.SCHEMA, "kind": group,
                                             "data": proposal}, sort_keys=True).encode()
            manifest = copy.deepcopy(self.original["manifest"])
            manifest["members"][group+".json"] = {
                "bytes": len(raw[group+".json"]),
                "sha256": hashlib.sha256(raw[group+".json"]).hexdigest()}
            raw["manifest.json"] = json.dumps(manifest).encode()
            archive = root / "proof.tar.xz"
            with tarfile.open(archive, "w:xz") as stream:
                for name, value in sorted(raw.items()):
                    member = tarfile.TarInfo(name)
                    member.size = len(value)
                    stream.addfile(member, io.BytesIO(value))
            # Transport identity and schema are valid. Only mathematical
            # acceptance can detect this deliberate change.
            received = Payload.read_archive(archive)
            converter.generate(received["groups"][group], root)
            result = subprocess.run([
                "lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                str(root / output)], cwd=self.workspace,
                capture_output=True, text=True, timeout=180)
            log = result.stdout + result.stderr
            (folder / (group+"-rejected.log")).write_text(log)
            self.assertNotEqual(result.returncode, 0, log)
            self.assertNotIn("unknown module", log)
            self.assertNotIn("object file", log)
            self.assertIn(diagnostic, log)

    def test_wrong_source_coefficient_fails_exact_identity_after_valid_transport(self):
        def mutate(payload):
            value = Fraction(*payload["thirteen"]["xi_coefficients"][0]) + 1
            payload["thirteen"]["xi_coefficients"][0] = [value.numerator, value.denominator]
        self.reject_in_lean("rational", mutate, Rational,
                            "polyak/Certificates/PartII/Rational/Polynomials.lean",
                            "unsolved goals")

    def test_false_trigonometric_enclosure_fails_kernel_arithmetic(self):
        def mutate(payload):
            point = next(p for p in payload["points"] if (p["j"], p["k"]) == (0, 13))
            point["sin"] = [[1, 1], [2, 1]]
        self.reject_in_lean("trigonometry", mutate, Trig,
                            "polyak/Certificates/PartII/Trigonometry/Bounds.lean",
                            "(kernel) application type mismatch")


if __name__ == "__main__":
    unittest.main()

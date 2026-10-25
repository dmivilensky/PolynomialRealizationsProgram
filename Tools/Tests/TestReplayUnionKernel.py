"""Exercise union ownership with real, tiny Lean artifacts and no article rebuild."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class ReplayUnionKernelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.workspace = Path(__file__).resolve().parents[2]
        if shutil.which("lake") is None:
            raise unittest.SkipTest("Lake toolchain is unavailable")
        found = subprocess.run(["lake", "env", "which", "lean"], cwd=cls.workspace,
                               capture_output=True, text=True, check=True)
        cls.lean = found.stdout.strip()
        cls.helper = cls.workspace / "Tools/Verification/Replay.lean"

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="replay-union-kernel-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.environment = {**os.environ, "LEAN_PATH": str(self.root)}
        sources = {
            "First/A": "namespace First\ndef a : Nat := 1\ntheorem a_eq : a = 1 := rfl\nend First\n",
            "Second/B": "import First.A\ntheorem second_eq : First.a = 1 := First.a_eq\n",
            "Outside/Back": "import First.A\ntheorem outside_eq : First.a = 1 := First.a_eq\n",
            "Second/C": "import Outside.Back\ntheorem third_eq : First.a = 1 := outside_eq\n",
        }
        for module, text in sources.items():
            source = self.root / f"{module}.lean"
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text(text)
            subprocess.run([self.lean, "-R", str(self.root), str(source),
                            "-o", str(source.with_suffix(".olean"))],
                           env=self.environment, capture_output=True, text=True, check=True)

    def replay(self, roots, modules, legacy=False):
        manifest = {"modules": [module.split(".") for module in modules]}
        manifest["root" if legacy else "roots"] = roots[0] if legacy else roots
        path = self.root / "manifest.json"
        path.write_text(json.dumps(manifest))
        return subprocess.run([self.lean, "--run", str(self.helper), "--package", str(path)],
                              env=self.environment, capture_output=True, text=True)

    def test_union_replays_cross_root_dependencies_with_stock_kernel(self):
        result = self.replay([["First"], ["Second"]], ["Second.B", "First.A"])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Kernel package replay passed for 2 modules", result.stdout)
        self.assertLess(result.stdout.index("starting First.A"), result.stdout.index("starting Second.B"))

    def test_any_owned_root_in_external_baseline_is_rejected(self):
        result = self.replay([["First"], ["Second"]], ["First.A", "Second.C"])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("declaration present in external replay baseline", result.stdout + result.stderr)
        self.assertIn("First.a", result.stdout + result.stderr)

    def test_legacy_single_root_manifest_still_replays(self):
        result = self.replay([["First"]], ["First.A"], legacy=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Kernel package replay passed for 1 modules", result.stdout)


if __name__ == "__main__":
    unittest.main()

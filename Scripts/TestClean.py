"""Exercise the distribution cleaner in an isolated temporary repository.

The cleaner deletes directory trees, so the important boundary is preservation:
proof sources, generated Lean witnesses, Git metadata and outside symlink targets
must survive. This test never runs cleanup against the actual project.
"""
from pathlib import Path
import tempfile
import unittest

import Clean


class CleanTests(unittest.TestCase):
    """
    Check deletion boundaries rather than merely repeating the path selector.
    """

    def test_preserves_distribution_and_external_targets(self):
        """
        Delete artifacts in a fixture and verify all indispensable files survive.

        A disposable symlink points outside the fake repository. Removing it must leave its
        target intact; .git contents and an unknown file also survive.
        """
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary)
            root = parent / "repository"
            root.mkdir()
            keep = (".git/config", "lake-manifest.json", "Article.pdf",
                    "Paper/Theorem.lean", "Paper/Data000.lean", "Scripts/Generator.py",
                    "unknown-file.txt")
            for name in keep:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("preserve")
            outside = parent / "outside"
            outside.mkdir()
            (outside / "sentinel").write_text("preserve")
            (root / ".lake").symlink_to(outside, target_is_directory=True)
            (root / ".VSCodeCounter").mkdir()
            (root / ".VSCodeCounter/report.json").write_text("discard")
            (root / "Paper/.DS_Store").write_text("discard")
            (root / "Scripts/__pycache__").mkdir()
            (root / "Scripts/__pycache__/cache.pyc").write_bytes(b"discard")
            original = Clean.ROOT
            try:
                Clean.ROOT = root
                selected = Clean.disposable_paths()
                self.assertTrue(all((root / name).read_text() == "preserve" for name in keep))
                for path in selected:
                    Clean.clean(path)
                self.assertTrue(all((root / name).read_text() == "preserve" for name in keep))
                self.assertEqual((outside / "sentinel").read_text(), "preserve")
                self.assertFalse(Clean.disposable_paths())
                with self.assertRaises(ValueError):
                    Clean.clean(root)
                with self.assertRaises(ValueError):
                    Clean.clean(root / ".git/config")
                with self.assertRaises(ValueError):
                    Clean.clean(outside)
            finally:
                Clean.ROOT = original


if __name__ == "__main__":
    unittest.main()

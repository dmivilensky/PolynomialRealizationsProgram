"""Exercise the distribution cleaner in an isolated temporary repository.

The cleaner deletes directory trees, so the important boundary is preservation:
handwritten proofs, other packages’ witnesses, Git metadata and outside symlink targets
must survive. This test never runs cleanup against the actual project.
"""
from pathlib import Path
import tempfile
import unittest

from Tools.Maintenance import Clean


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
                    "Paper/Theorem.lean", "Paper/Data000.lean", "Tools/Certificates/Generator.py",
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
            (root / "Tools/Certificates/__pycache__").mkdir()
            (root / "Tools/Certificates/__pycache__/cache.pyc").write_bytes(b"discard")
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

    def test_polyak_cleanup_preserves_contract_and_handwritten_proofs(self):
        """Drop precisely regenerable inputs, including those outside Certificates."""
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "repository"
            root.mkdir()
            keep = ("polyak/Certificates/Source.json",
                    "polyak/Certificates/README.md",
                    "polyak/Certificates/FutureHandwritten.lean",
                    "polyak/Certificates/PartII/Source.json",
                    "polyak/Certificates/PartII/FutureHandwritten.lean",
                    "polyak/ArticleMap.md", "polyak/Article.lean",
                    "Tools/Certificates/Registry.py",
                    "polyak-code/part1/proof/proof.tar.xz",
                    "polyak-code/part2/proof/proof.tar.xz",
                    "polyak/Boundary/P5/Results.lean",
                    "chebyshev2/Certificates/Data.lean")
            outputs = Clean.POLYAK_OUTPUTS | Clean.POLYAK_PARTII_OUTPUTS
            for name in (*keep, *outputs):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("fixture")
            original = Clean.ROOT
            try:
                Clean.ROOT = root
                for path in Clean.disposable_paths():
                    Clean.clean(path)
                self.assertTrue(all((root / name).is_file() for name in keep))
                self.assertTrue(all(not (root / name).exists()
                                    for name in outputs))
                self.assertFalse(Clean.disposable_paths())
            finally:
                Clean.ROOT = original

    def test_polyak_symlinked_parent_is_not_followed(self):
        """A Certificates symlink must not expose external outputs to deletion."""
        with tempfile.TemporaryDirectory() as temporary:
            parent = Path(temporary)
            root, outside = parent / "repository", parent / "outside"
            (root / "polyak").mkdir(parents=True)
            outside.mkdir()
            sentinel = outside / "P2Codes.lean"
            sentinel.write_text("preserve")
            (root / "polyak/Certificates").symlink_to(outside, target_is_directory=True)
            original = Clean.ROOT
            try:
                Clean.ROOT = root
                for path in Clean.disposable_paths():
                    Clean.clean(path)
                self.assertEqual(sentinel.read_text(), "preserve")
            finally:
                Clean.ROOT = original


if __name__ == "__main__":
    unittest.main()

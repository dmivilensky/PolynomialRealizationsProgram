"""Exercise source discovery, coverage and actual Lean verification for new packages."""
from contextlib import redirect_stdout
import io
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from Tools.Verification.CheckCorrespondence import check, check_showcase, imports
from Tools.Verification.Project import discover_projects, resolve_project

ROOT = Path(__file__).resolve().parents[2]


class ProjectTests(unittest.TestCase):
    """Check custom Lake layouts, manual showcases and import coverage failures."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="verification-layout-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        (self.root / "lakefile.toml").write_text('''name = "layoutfixture"
srcDir = "src"
[[lean_lib]]
name = "IndependentLibrary"
srcDir = "proofs"
roots = ["Research.NewTopic"]
''')
        self.folder = self.root / "src/proofs/Research/NewTopic"
        self.folder.mkdir(parents=True)
        (self.folder / "Basic.lean").write_text('''namespace Research.NewTopic
theorem identity (n : Nat) : n = n := rfl
end Research.NewTopic
''')
        (self.folder / "Check.lean").write_text('import Research.NewTopic.Basic\n')

    def test_new_namespace_custom_source_dirs_and_missing_sibling_root(self):
        projects = discover_projects(self.root)
        self.assertEqual(len(projects), 1)
        project = projects[0]
        self.assertEqual(project.check_module, "Research.NewTopic.Check")
        self.assertEqual(project.relative, "src/proofs/Research/NewTopic")
        self.assertEqual(len(project.sources), 2)
        with redirect_stdout(io.StringIO()):
            check(project)

    def test_unimported_source_is_rejected(self):
        (self.folder / "Detached.lean").write_text('def detached : Nat := 0\n')
        with self.assertRaisesRegex(ValueError, "Sources outside the full check.*Detached"):
            check(resolve_project(self.folder))

    def test_internal_check_is_not_a_separate_complete_package(self):
        internal = self.folder / "Numerics"
        internal.mkdir()
        (internal / "Check.lean").write_text('def numericalCheck : Bool := true\n')
        projects = discover_projects(self.root)
        self.assertEqual([project.directory for project in projects], [self.folder])
        # Internal checks remain available for explicit, targeted verification.
        self.assertEqual(resolve_project(internal).module, "Research.NewTopic.Numerics")

    def test_manual_showcase_needs_no_paper_source(self):
        (self.folder / "Article.lean").write_text('''import Research.NewTopic.Basic
#check @Research.NewTopic.identity
''')
        self.assertEqual(check_showcase(resolve_project(self.folder)), (0, 1))
        (self.folder / "ArticleMap.md").write_text('''| Article | Lean | Coverage |
| --- | --- | --- |
| Hand-checked result | [identity](Basic.lean) | [Manual PDF reference](../missing-paper.pdf) |
''')
        (self.folder / "Check.lean").write_text('import Research.NewTopic.Article\n')
        project = resolve_project(self.folder)
        with redirect_stdout(io.StringIO()):
            check(project)
        table = self.folder / "ArticleMap.md"
        table.write_text(table.read_text().replace("[identity]", "[different]"))
        with self.assertRaisesRegex(ValueError, "differs from the ordered showcase"):
            check_showcase(project)

    def test_comments_and_strings_do_not_hide_actual_unfinished_proofs(self):
        path = self.folder / "Imports.lean"
        path.write_text('''/- import Fake /- import Nested -/ -/
import Research.NewTopic.Basic
-- import NotAnImport
def sample : String := "import Wrong sorry admit native_decide"
''')
        self.assertEqual(imports(path), ["Research.NewTopic.Basic"])
        (self.folder / "Check.lean").write_text('import Research.NewTopic.Imports\n')
        project = resolve_project(self.folder)
        with redirect_stdout(io.StringIO()):
            check(project)
        path.write_text(path.read_text() + '\nexample : False := by sorry\n')
        with self.assertRaisesRegex(ValueError, "Unfinished or native-trust proof"):
            check(project)


class VerificationIntegrationTests(unittest.TestCase):
    """Build and replay unrelated packages through the public directory commands."""

    def test_unknown_and_dotted_packages_build_and_replay(self):
        with tempfile.TemporaryDirectory(prefix="verification-integration-") as temporary:
            root = Path(temporary).resolve()
            (root / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
            (root / "lakefile.toml").write_text('''name = "verificationfixture"
[[lean_lib]]
name = "Verification"
srcDir = "Tools"
roots = ["Verification.Audit", "Verification.All"]
[[lean_lib]]
name = "NewTopic"
srcDir = "Proofs"
roots = ["NewTopic.Check"]
globs = ["NewTopic.+"]
[[lean_lib]]
name = "«2468.13579v1»"
srcDir = "Proofs"
roots = ["«2468.13579v1»", "«2468.13579v1».Check"]
''')
            tools = root / "Tools/Verification"
            tools.mkdir(parents=True)
            shutil.copyfile(ROOT / "Tools/Verification/Audit.lean", tools / "Audit.lean")
            (tools / "All.lean").write_text("import Verification.Audit\n")
            for stem, module in [("NewTopic", "NewTopic"), ("2468.13579v1", "«2468.13579v1»")]:
                folder = root / "Proofs" / stem
                folder.mkdir(parents=True)
                (folder / "Basic.lean").write_text(f'''namespace {module}
theorem identity (n : Nat) : n = n := rfl
end {module}
''')
                (folder / "Check.lean").write_text(f'''import {module}.Basic
import Verification.Audit
run_cmd Verification.audit `{module} "Proofs/{stem}"
''')
            environment = os.environ.copy()
            environment["PYTHONPATH"] = str(ROOT) + os.pathsep + environment.get("PYTHONPATH", "")
            environment["PYTHONDONTWRITEBYTECODE"] = "1"

            def run(module, *arguments):
                result = subprocess.run([sys.executable, "-B", "-m", "Tools.Verification." + module, *arguments],
                                        cwd=root, env=environment, capture_output=True, text=True, timeout=180)
                logs = ""
                if result.returncode:
                    logs = "\n".join(path.read_text() for path in (root / ".lake/checks").rglob("*.log"))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr + logs)
                return result.stdout

            run("Check", "all", "--jobs", "1")
            aggregate = (tools / "All.lean").read_text()
            self.assertIn("import NewTopic.Check", aggregate)
            self.assertIn("import «2468.13579v1».Check", aggregate)
            for folder in ["Proofs/NewTopic", "Proofs/2468.13579v1"]:
                self.assertIn("Kernel package replay passed", run("Replay", folder))


if __name__ == "__main__":
    unittest.main()

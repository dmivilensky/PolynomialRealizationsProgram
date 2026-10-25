"""Protect the owned-module boundary of an explicitly scoped kernel replay.

These fixtures exercise custom Lake source roots and escaped module stems.
No proof replay or certificate preparation runs against the real repository.
"""
from contextlib import redirect_stderr, redirect_stdout
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from Tools.Verification import Check, Replay
from Tools.Verification import PrepareSources
from Tools.Verification.Project import resolve_project


class ReplayScopeTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="replay-scope-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        (self.root / "lakefile.toml").write_text('''name = "replayscopefixture"
srcDir = "src"
[[lean_lib]]
name = "IndependentLibrary"
srcDir = "proofs"
roots = ["Research.NewTopic"]
''')
        self.folder = self.root / "src/proofs/Research/NewTopic"
        self.folder.mkdir(parents=True)
        for name in ("Basic.lean", "Check.lean", "General.lean", "General/Proof.lean",
                     "General/Exact.1.lean", "General/Nested.lean", "General/Nested/Leaf.lean",
                     "GeneralOther/Other.lean", "General/.Hidden/Secret.lean"):
            path = self.folder / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("-- fixture source\n")
        self.folder.with_suffix(".lean").write_text("-- public package root\n")
        (self.folder / "Empty").mkdir()
        (self.folder / "Empty/README.md").write_text("No owned proofs.\n")
        self.project = resolve_project(self.folder)
        self.registrations = {}
        registry = patch.dict(PrepareSources.PREPARATIONS,
                              {self.project.relative: self.registrations})
        registry.start()
        self.addCleanup(registry.stop)

    def test_default_manifest_keeps_complete_owned_package(self):
        manifest = Replay.replay_manifest(self.project)
        self.assertEqual(manifest["root"], ("Research", "NewTopic"))
        self.assertEqual(set(manifest["modules"]), {
            ("Research", "NewTopic"),
            ("Research", "NewTopic", "Basic"),
            ("Research", "NewTopic", "Check"),
            ("Research", "NewTopic", "General"),
            ("Research", "NewTopic", "General", "Proof"),
            ("Research", "NewTopic", "General", "Exact.1"),
            ("Research", "NewTopic", "General", "Nested"),
            ("Research", "NewTopic", "General", "Nested", "Leaf"),
            ("Research", "NewTopic", "GeneralOther", "Other"),
        })
        self.assertEqual(len(manifest["modules"]), 9)
        self.assertEqual(manifest, Replay.replay_manifest(self.project, None))

    def test_scope_changes_kernel_root_and_excludes_textual_prefix_sibling(self):
        manifest = Replay.replay_manifest(self.project, "General")
        self.assertEqual(manifest["root"], ("Research", "NewTopic", "General"))
        self.assertEqual(set(manifest["modules"]), {
            ("Research", "NewTopic", "General"),
            ("Research", "NewTopic", "General", "Proof"),
            ("Research", "NewTopic", "General", "Exact.1"),
            ("Research", "NewTopic", "General", "Nested"),
            ("Research", "NewTopic", "General", "Nested", "Leaf"),
        })
        self.assertEqual(len(manifest["modules"]), 5)
        self.assertEqual(manifest, Replay.replay_manifest(self.project, "General"))

    def test_nested_scope_retains_its_sibling_public_root(self):
        manifest = Replay.replay_manifest(self.project, "General/Nested")
        self.assertEqual(manifest["root"], ("Research", "NewTopic", "General", "Nested"))
        self.assertEqual(set(manifest["modules"]), {
            ("Research", "NewTopic", "General", "Nested"),
            ("Research", "NewTopic", "General", "Nested", "Leaf"),
        })

    def test_union_owns_both_exact_namespaces_and_deduplicates_nested_scope(self):
        manifest = Replay.replay_manifest(self.project, ["General/Nested", "GeneralOther", "General"])
        self.assertEqual(manifest["roots"], [("Research", "NewTopic", "GeneralOther"),
                                            ("Research", "NewTopic", "General")])
        self.assertEqual(len(manifest["modules"]), 6)
        self.assertEqual(len(manifest["modules"]), len(set(manifest["modules"])))
        self.assertIn(("Research", "NewTopic", "GeneralOther", "Other"), manifest["modules"])
        self.assertNotIn(("Research", "NewTopic", "Basic"), manifest["modules"])
        single = Replay.replay_manifest(self.project, ["General", "General/Nested", "General"])
        self.assertEqual(single, Replay.replay_manifest(self.project, "General"))

    def test_union_rejects_any_invalid_member_before_starting_kernel(self):
        with patch.object(Replay.subprocess, "run") as runner:
            for scopes in ([], ["General", "../Outside"], ["General", "Empty"],
                           ["General", "Missing"]):
                with self.subTest(scopes=scopes), self.assertRaises(ValueError):
                    Replay.replay(self.project, scopes)
            runner.assert_not_called()

    def test_invalid_scope_never_starts_kernel_process(self):
        invalid = ("", ".", "..", "../Outside", "General/../General", "Missing",
                   "Empty", "General/Proof.lean", str(self.folder / "General"))
        with patch.object(Replay.subprocess, "run") as runner:
            for scope in invalid:
                with self.subTest(scope=scope), self.assertRaises(ValueError):
                    Replay.replay(self.project, scope)
            runner.assert_not_called()

    def test_scope_symlink_cannot_escape_owned_package(self):
        outside = self.root / "OutsideSources"
        outside.mkdir()
        (outside / "Proof.lean").write_text("-- outside sentinel\n")
        (self.folder / "Escaped").symlink_to(outside, target_is_directory=True)
        with patch.object(Replay.subprocess, "run") as runner:
            with self.assertRaises(ValueError):
                Replay.replay(self.project, "Escaped")
            runner.assert_not_called()
        self.assertEqual((outside / "Proof.lean").read_text(), "-- outside sentinel\n")

    def test_replay_passes_exact_scoped_manifest_to_stock_kernel(self):
        captured = []

        def inspect_manifest(arguments, **kwargs):
            self.assertEqual(arguments[:4], ["lake", "env", "lean", "--run"])
            self.assertEqual(arguments[-2], "--package")
            self.assertEqual(kwargs["cwd"], self.project.workspace)
            self.assertTrue(kwargs["check"])
            captured.append(json.loads(Path(arguments[-1]).read_text()))
            return subprocess.CompletedProcess(arguments, 0)

        with patch.object(Replay.subprocess, "run", side_effect=inspect_manifest) as runner:
            Replay.replay(self.project, "General")
            runner.assert_called_once()
        self.assertEqual(captured[0]["root"], ["Research", "NewTopic", "General"])
        self.assertEqual(len(captured[0]["modules"]), 5)
        self.assertIn(["Research", "NewTopic", "General", "Exact.1"], captured[0]["modules"])
        self.assertNotIn(["Research", "NewTopic", "GeneralOther", "Other"], captured[0]["modules"])

    def test_check_scoped_replay_still_prepares_and_checks_complete_package(self):
        arguments = ["check", str(self.folder), "--replay-scope", "General", "--jobs", "1"]
        with patch("sys.argv", arguments), \
                patch.object(Check, "select_projects", return_value=(self.project,)), \
                patch.object(Check, "prepare") as prepare, \
                patch.object(Check, "check") as check, \
                patch.object(Check, "check_article") as article, \
                patch.object(Check.subprocess, "run", return_value=subprocess.CompletedProcess(
                    [], 0, stdout="cached package\n", stderr="")) as lake, \
                patch.object(Replay, "replay") as replay, redirect_stdout(io.StringIO()):
            Check.main()
        prepare.assert_called_once()
        self.assertEqual(prepare.call_args.args[0], self.project)
        check.assert_called_once_with(self.project)
        article.assert_called_once()
        self.assertEqual(article.call_args.args[0], self.project)
        lake.assert_called_once()
        self.assertEqual(lake.call_args.args[0],
                         ["lake", "--no-build", "build", "+Research.NewTopic.Check"])
        replay.assert_called_once()
        self.assertEqual(replay.call_args.args[0], self.project)
        scope = (replay.call_args.args[1] if len(replay.call_args.args) > 1
                 else replay.call_args.kwargs["scope"])
        self.assertEqual(scope, "General")

    def test_replay_cli_repeated_scopes_selects_one_union(self):
        arguments = ["replay", str(self.folder), "--scope", "General", "--scope", "GeneralOther"]
        with patch("sys.argv", arguments), \
                patch.object(Replay, "select_projects", return_value=(self.project,)), \
                patch.object(Replay, "replay") as replay:
            Replay.main()
        replay.assert_called_once_with(self.project, ["General", "GeneralOther"])

    def test_check_restores_clean_generated_scope_before_module_validation(self):
        group = self.folder / "Certificates/PartII"
        group.mkdir(parents=True)
        (group / "Source.json").write_text("{}")
        self.registrations["Certificates/PartII/Source.json"] = {
            "module": "Tools.Certificates.Example"}
        with self.assertRaises(ValueError):
            Replay.replay_manifest(self.project, "Certificates/PartII")
        captured = []
        def restore(*args, **kwargs):
            (group / "Generated.lean").write_text("-- restored mathematical data\n")
        def inspect(project, scope):
            captured.append(Replay.replay_manifest(project, scope))
        arguments = ["check", str(self.folder), "--replay-scope", "General",
                     "--replay-scope", "Certificates/PartII"]
        with patch("sys.argv", arguments), \
                patch.object(Check, "select_projects", return_value=(self.project,)), \
                patch.object(Check, "prepare", side_effect=restore) as prepare, \
                patch.object(Check, "check"), patch.object(Check, "check_article"), \
                patch.object(Check.subprocess, "run", return_value=subprocess.CompletedProcess(
                    [], 0, stdout="cached package\n", stderr="")), \
                patch.object(Replay, "replay", side_effect=inspect), redirect_stdout(io.StringIO()):
            Check.main()
        prepare.assert_called_once()
        self.assertIn(("Research", "NewTopic", "Certificates", "PartII", "Generated"),
                      captured[0]["modules"])
        self.assertEqual(len(captured[0]["roots"]), 2)

    def test_check_rejects_still_empty_declared_scope_after_preparation(self):
        group = self.folder / "Certificates/PartII"
        group.mkdir(parents=True)
        (group / "Source.json").write_text("{}")
        self.registrations["Certificates/PartII/Source.json"] = {
            "module": "Tools.Certificates.Example"}
        arguments = ["check", str(self.folder), "--replay-scope", "Certificates/PartII"]
        with patch("sys.argv", arguments), \
                patch.object(Check, "select_projects", return_value=(self.project,)), \
                patch.object(Check, "prepare") as prepare, \
                patch.object(Check, "check") as check, \
                patch.object(Check.subprocess, "run") as lake, \
                redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            Check.main()
        prepare.assert_called_once()
        check.assert_not_called()
        lake.assert_not_called()

    def test_clean_registered_source_group_allows_preparation_before_replay(self):
        group = self.folder / "Certificates/PartII"
        group.mkdir(parents=True)
        (group / "Source.json").write_text("{}")
        with patch.dict(PrepareSources.PREPARATIONS, {self.project.relative: {
                "Certificates/PartII/Source.json": {"module": "Tools.Certificates.Example"}}}):
            manifest = Replay.replay_manifest(self.project, "Certificates/PartII", allow_preparation=True)
        self.assertEqual(manifest["modules"], [])
        self.assertEqual(manifest["root"], ("Research", "NewTopic", "Certificates", "PartII"))

    def test_check_repeated_scopes_runs_one_union_after_package_checks(self):
        arguments = ["check", str(self.folder), "--replay-scope", "General",
                     "--replay-scope", "GeneralOther", "--jobs", "1"]
        with patch("sys.argv", arguments), \
                patch.object(Check, "select_projects", return_value=(self.project,)), \
                patch.object(Check, "prepare") as prepare, \
                patch.object(Check, "check") as check, \
                patch.object(Check, "check_article") as article, \
                patch.object(Check.subprocess, "run", return_value=subprocess.CompletedProcess(
                    [], 0, stdout="cached package\n", stderr="")), \
                patch.object(Replay, "replay") as replay, redirect_stdout(io.StringIO()):
            Check.main()
        prepare.assert_called_once()
        check.assert_called_once_with(self.project)
        article.assert_called_once()
        replay.assert_called_once_with(self.project, ["General", "GeneralOther"])

    def test_check_rejects_invalid_requests_before_preparation_or_lake(self):
        requests = ([str(self.folder), "--replay", "--replay-scope", "General"],
                    ["all", "--replay-scope", "General"],
                    ["--replay-scope", "General"],
                    [str(self.folder), "--replay-scope", ""],
                    [str(self.folder), "--replay-scope", "../Outside"],
                    [str(self.folder), "--replay-scope", "Empty"])
        for request in requests:
            with self.subTest(arguments=request), patch("sys.argv", ["check", *request]), \
                    patch.object(Check, "select_projects", return_value=(self.project,)), \
                    patch.object(Check, "prepare") as prepare, \
                    patch.object(Check, "check") as check, \
                    patch.object(Check, "check_article") as article, \
                    patch.object(Check.subprocess, "run") as runner, \
                    redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
                Check.main()
            self.assertNotEqual(error.exception.code, 0)
            prepare.assert_not_called()
            check.assert_not_called()
            article.assert_not_called()
            runner.assert_not_called()

    def test_replay_cli_scope_requires_one_explicit_package(self):
        for request in (["all", "--scope", "General"], ["--scope", "General"]):
            with self.subTest(arguments=request), patch("sys.argv", ["replay", *request]), \
                    patch.object(Replay, "select_projects", return_value=(self.project,)), \
                    patch.object(Replay, "replay") as replay, \
                    redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
                Replay.main()
            self.assertNotEqual(error.exception.code, 0)
            replay.assert_not_called()


if __name__ == "__main__":
    unittest.main()

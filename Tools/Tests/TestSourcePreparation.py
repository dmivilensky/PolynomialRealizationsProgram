"""Check archive acquisition and orchestration without experiments or Lean processes."""
from contextlib import redirect_stdout
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import threading
from types import SimpleNamespace
import unittest
from unittest import mock

from Tools.Verification import Check, PrepareSources

ROOT = Path(__file__).resolve().parents[2]


class SourcePreparationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="archive-routing-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.directory = self.root / "Example"
        certificates = self.directory / "Certificates"
        certificates.mkdir(parents=True)
        self.data = b"pinned upstream mathematical archive"
        self.source = {
            "format": "POLYNOMIAL_REALIZATIONS_CERTIFICATE_SOURCE",
            "repository": "example/upstream", "revision": "main", "revision_kind": "ref",
            "archive_path": "part1/proof/proof.tar.xz", "archive_bytes": len(self.data),
            "archive_sha256": hashlib.sha256(self.data).hexdigest(),
        }
        (certificates / "Source.json").write_text(json.dumps(self.source))
        self.registrations = {
            "Certificates/Source.json": {"module": "Tools.Certificates.LocalPrepare"}}
        registry = mock.patch.dict(PrepareSources.PREPARATIONS, {"Example": self.registrations})
        registry.start()
        self.addCleanup(registry.stop)
        implementation = self.root / "Tools/Certificates/LocalPrepare.py"
        implementation.parent.mkdir(parents=True)
        implementation.write_text('"""Local test hook; never executed."""\n')
        self.project = SimpleNamespace(workspace=self.root, directory=self.directory,
                                       relative="Example", check_module="Example.Check")

    def test_online_check_fetches_missing_bytes_before_local_generation(self):
        with mock.patch("urllib.request.urlopen", return_value=io.BytesIO(self.data)) as download, \
             mock.patch.object(PrepareSources.subprocess, "run",
                               return_value=SimpleNamespace(returncode=0)) as run, \
             redirect_stdout(io.StringIO()):
            PrepareSources.prepare(self.project)
        request = download.call_args.args[0]
        self.assertEqual(request.full_url,
                         "https://raw.githubusercontent.com/example/upstream/main/part1/proof/proof.tar.xz")
        arguments = run.call_args.args[0]
        archive = Path(arguments[arguments.index("--archive") + 1])
        self.assertEqual(archive.read_bytes(), self.data)
        self.assertEqual(arguments[:3], [sys.executable, "-m", "Tools.Certificates.LocalPrepare"])
        self.assertNotIn("preparation", self.source)
        self.assertNotIn("paper", self.source)

    def test_mismatched_download_never_invokes_generator(self):
        with mock.patch("urllib.request.urlopen", return_value=io.BytesIO(b"x" * len(self.data))), \
             mock.patch.object(PrepareSources.subprocess, "run") as run, \
             redirect_stdout(io.StringIO()):
            with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
                PrepareSources.prepare(self.project)
        run.assert_not_called()

    def test_offline_missing_archive_never_downloads_or_generates(self):
        with mock.patch("urllib.request.urlopen") as download, \
             mock.patch.object(PrepareSources.subprocess, "run") as run, \
             redirect_stdout(io.StringIO()):
            with self.assertRaises(FileNotFoundError):
                PrepareSources.prepare(self.project, offline=True)
        download.assert_not_called()
        run.assert_not_called()

    def test_explicit_local_archive_never_downloads(self):
        archive = self.root / "fresh-proof.tar.xz"
        archive.write_bytes(self.data)
        with mock.patch.object(PrepareSources, "fetch") as fetch, \
             mock.patch.object(PrepareSources.subprocess, "run",
                               return_value=SimpleNamespace(returncode=0)) as run, \
             redirect_stdout(io.StringIO()):
            PrepareSources.prepare(self.project, offline=True, archive=archive)
        fetch.assert_not_called()
        arguments = run.call_args.args[0]
        self.assertEqual(arguments[arguments.index("--archive") + 1], str(archive.resolve()))

    def test_invalid_local_archive_stops_before_environment_or_generation(self):
        archive = self.root / "invalid-proof.tar.xz"
        archive.write_bytes(b"x" * len(self.data))
        with mock.patch.object(PrepareSources, "fetch") as fetch, \
             mock.patch.object(PrepareSources, "interpreter") as interpreter, \
             mock.patch.object(PrepareSources.subprocess, "run") as run, \
             redirect_stdout(io.StringIO()):
            with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
                PrepareSources.prepare(self.project, archive=archive)
        fetch.assert_not_called()
        interpreter.assert_not_called()
        run.assert_not_called()


    def test_nested_source_group_downloads_and_prepares_its_own_archive(self):
        group = self.directory / "Certificates/PartII"
        group.mkdir()
        second = {**self.source, "archive_path": "part2/proof/proof.tar.xz"}
        (group / "Source.json").write_text(json.dumps(second))
        self.registrations["Certificates/PartII/Source.json"] = {
            "module": "Tools.Certificates.LocalPrepare"}
        with mock.patch("urllib.request.urlopen", side_effect=lambda *a, **k: io.BytesIO(self.data)) as download, \
             mock.patch.object(PrepareSources.subprocess, "run", return_value=SimpleNamespace(returncode=0)) as run, \
             redirect_stdout(io.StringIO()):
            PrepareSources.prepare(self.project)
        self.assertEqual(download.call_count, 2)
        self.assertTrue(download.call_args_list[1].args[0].full_url.endswith("/part2/proof/proof.tar.xz"))
        archives = [Path(c.args[0][c.args[0].index("--archive")+1]) for c in run.call_args_list]
        self.assertNotEqual(archives[0], archives[1])
        self.assertEqual(archives[1].read_bytes(), self.data)

    def test_bad_nested_archive_is_rejected_before_its_generator(self):
        group = self.directory / "Certificates/PartII"
        group.mkdir()
        (group / "Source.json").write_text(json.dumps({**self.source, "archive_path": "part2/proof/proof.tar.xz"}))
        self.registrations["Certificates/PartII/Source.json"] = {
            "module": "Tools.Certificates.LocalPrepare"}
        with mock.patch("urllib.request.urlopen", side_effect=[io.BytesIO(self.data), io.BytesIO(b"x"*len(self.data))]), \
             mock.patch.object(PrepareSources.subprocess, "run", return_value=SimpleNamespace(returncode=0)) as run, \
             redirect_stdout(io.StringIO()):
            with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
                PrepareSources.prepare(self.project)
        self.assertEqual(run.call_count, 1)


    def test_registered_missing_source_cannot_silently_skip_generation(self):
        (self.directory / "Certificates/Source.json").unlink()
        with self.assertRaisesRegex(ValueError, "Missing registered Source"):
            PrepareSources.prepare(self.project)


    def test_registered_local_archive_is_checked_before_generation(self):
        archive = self.root / "supplier/proof.tar.xz"
        archive.parent.mkdir()
        archive.write_bytes(self.data)
        source = {k: v for k, v in self.source.items()
                  if k not in ("repository", "revision", "revision_kind")}
        source.update(transport="local", archive_path="supplier/proof.tar.xz")
        (self.directory / "Certificates/Source.json").write_text(json.dumps(source))
        with mock.patch("urllib.request.urlopen") as download, \
             mock.patch.object(PrepareSources.subprocess, "run",
                               return_value=SimpleNamespace(returncode=0)) as run, \
             redirect_stdout(io.StringIO()):
            PrepareSources.prepare(self.project, offline=True)
            archive.write_bytes(b"x" * len(self.data))
            with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
                PrepareSources.prepare(self.project, offline=True)
        download.assert_not_called()
        self.assertEqual(run.call_count, 1)

    def test_main_check_prepares_before_coverage_and_build(self):
        events = []
        with mock.patch.object(sys, "argv", ["Check", "Example"]), \
             mock.patch.object(Check, "select_projects", return_value=[self.project]), \
             mock.patch.object(Check, "prepare", side_effect=lambda *a, **k: events.append("prepare")), \
             mock.patch.object(Check, "check", side_effect=lambda *a: events.append("coverage")), \
             mock.patch.object(Check.subprocess, "run", side_effect=lambda *a, **k:
                               (events.append("lake") or
                                SimpleNamespace(returncode=0, stdout="", stderr=""))), \
             redirect_stdout(io.StringIO()):
            Check.main()
        self.assertEqual(events, ["prepare", "coverage", "lake"])

    def test_main_check_accepts_explicit_larger_process_limit(self):
        with mock.patch.object(sys, "argv", ["Check", "Example", "--jobs", "8"]), \
             mock.patch.object(Check, "select_projects", return_value=[self.project]), \
             mock.patch.object(Check, "prepare"), mock.patch.object(Check, "check"), \
             mock.patch.object(Check.subprocess, "run",
                               return_value=SimpleNamespace(returncode=0, stdout="", stderr="")), \
             redirect_stdout(io.StringIO()):
            Check.main()

    def test_independent_slow_proof_does_not_block_a_newly_ready_descendant(self):
        parent_done = threading.Event()
        child_done = threading.Event()
        slow_done = threading.Event()

        def run(arguments, **kwargs):
            if "--no-build" in arguments:
                if slow_done.is_set() and child_done.is_set():
                    return SimpleNamespace(returncode=0, stdout="", stderr="")
                ready = []
                if not slow_done.is_set():
                    ready.append("Example.Slow")
                if not parent_done.is_set():
                    ready.append("Example.Parent")
                elif not child_done.is_set():
                    ready.append("Example.Child")
                output = "\n".join(f"✖ Building {name}" for name in ready)
                return SimpleNamespace(returncode=1, stdout=output, stderr="")
            module = arguments[-1]
            if module == "+Example.Parent":
                parent_done.set()
            elif module == "+Example.Child":
                self.assertTrue(parent_done.is_set())
                self.assertFalse(slow_done.is_set())
                child_done.set()
            elif module == "+Example.Slow":
                if not child_done.wait(timeout=5):
                    return SimpleNamespace(returncode=1)
                slow_done.set()
            else:
                self.fail(f"Unexpected build: {arguments}")
            return SimpleNamespace(returncode=0)

        with mock.patch.object(sys, "argv", ["Check", "Example", "--jobs", "2"]), \
             mock.patch.object(Check, "select_projects", return_value=[self.project]), \
             mock.patch.object(Check, "prepare"), mock.patch.object(Check, "check"), \
             mock.patch.object(Check, "check_article"), \
             mock.patch.object(Check.subprocess, "run", side_effect=run), \
             redirect_stdout(io.StringIO()):
            Check.main()
        self.assertTrue(child_done.is_set())
        self.assertTrue(slow_done.is_set())


class ExperimentRunnerTests(unittest.TestCase):
    def _run(self, outcomes, arguments=()):
        specification = importlib.util.spec_from_file_location(
            "heavy_ball_runner_test", ROOT / "polyak-code/verify_all.py")
        runner = importlib.util.module_from_spec(specification)
        specification.loader.exec_module(runner)
        with tempfile.TemporaryDirectory(prefix="experiment-routing-") as temporary:
            root = Path(temporary)
            with mock.patch.object(runner, "ROOT", root), \
                 mock.patch.object(runner, "OUT", root / "verification"), \
                 mock.patch.object(runner, "PART1", {}), \
                 mock.patch.object(runner, "DIRECT", []), \
                 mock.patch.object(runner.shutil, "copytree"), \
                 mock.patch.object(runner, "run", side_effect=outcomes) as commands, \
                 mock.patch.object(sys, "argv", ["verify_all.py", *arguments]), \
                 redirect_stdout(io.StringIO()):
                code = runner.main()
                sequence = [call.args[0][4] for call in commands.call_args_list]
        return code, sequence

    def test_default_experiment_run_builds_archive_without_extra_flag(self):
        code, sequence = self._run([(True, 0, 0), (True, 0, 0)])
        self.assertEqual((code, sequence), (0, ["regen", "regen"]))

    def test_failed_regeneration_is_reported_as_failure(self):
        code, sequence = self._run([(False, 1, 0)])
        self.assertEqual((code, sequence), (1, ["regen"]))

    def test_part1_only_runs_the_full_automatic_archive_pipeline(self):
        code, sequence = self._run([(True, 0, 0)], ["--part1-only"])
        self.assertEqual((code, sequence), (0, ["regen"]))

    def test_part2_only_packages_data_without_running_part1(self):
        code, sequence = self._run([(True, 0, 0)], ["--part2-only"])
        self.assertEqual((code, sequence), (0, ["regen"]))

    def test_failed_part2_export_does_not_report_overall_success(self):
        code, sequence = self._run([(True, 0, 0), (False, 1, 0)])
        self.assertEqual((code, sequence), (1, ["regen", "regen"]))


if __name__ == "__main__":
    unittest.main()

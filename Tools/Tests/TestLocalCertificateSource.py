"""Check permanent local archive acquisition without producer runs or Lean builds."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

from Tools.Certificates.FetchCertificate import fetch, load_source


class LocalCertificateSourceTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="local-certificate-source-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.cache = self.root / ".lake/certificates/polyak"
        self.raw = b"exact local certificate bytes"
        self.source = {
            "format": "POLYNOMIAL_REALIZATIONS_CERTIFICATE_SOURCE",
            "transport": "local",
            "archive_path": "polyak-code/part1/proof/proof.tar.xz",
            "archive_bytes": len(self.raw),
            "archive_sha256": hashlib.sha256(self.raw).hexdigest(),
        }
        self.archive = self.root / self.source["archive_path"]
        self.archive.parent.mkdir(parents=True)
        self.archive.write_bytes(self.raw)
        self.descriptor = self.root / "Source.json"

    def load(self, source):
        self.descriptor.write_text(json.dumps(source))
        return load_source(self.descriptor)

    def seed_cache(self):
        cached = self.cache / self.source["archive_sha256"] / "proof.tar.xz"
        cached.parent.mkdir(parents=True, exist_ok=True)
        cached.write_bytes(self.raw)

    def test_local_descriptor_does_not_require_remote_locator(self):
        self.assertEqual(self.load(self.source), self.source)
        self.assertNotIn("repository", self.source)
        self.assertNotIn("revision", self.source)

    def test_local_file_is_used_online_and_offline_without_http(self):
        for offline in (False, True):
            with self.subTest(offline=offline), mock.patch("urllib.request.urlopen") as download:
                receipt = fetch(self.load(self.source), self.cache, offline=offline, root=self.root)
            download.assert_not_called()
            self.assertEqual(receipt["archive"], str(self.archive))
            self.assertEqual(receipt["transport"], "local")
            self.assertNotIn("url", receipt)
            self.assertEqual(receipt["status"], "SHA256_MATCHED_NOT_LEAN_VERIFIED")

    def test_missing_local_file_never_falls_back_to_cache_or_http(self):
        self.seed_cache()
        self.archive.unlink()
        for offline in (False, True):
            with self.subTest(offline=offline), mock.patch("urllib.request.urlopen") as download:
                with self.assertRaises(FileNotFoundError):
                    fetch(self.source, self.cache, offline=offline, root=self.root)
            download.assert_not_called()

    def test_existing_receipt_does_not_mask_corruption_or_missing_file(self):
        fetch(self.source, self.cache, root=self.root)
        self.seed_cache()
        self.archive.write_bytes(b"x" * len(self.raw))
        with mock.patch("urllib.request.urlopen") as download:
            with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
                fetch(self.source, self.cache, root=self.root)
            self.archive.unlink()
            with self.assertRaises(FileNotFoundError):
                fetch(self.source, self.cache, root=self.root)
        download.assert_not_called()

    def test_local_file_size_is_pinned(self):
        for raw in (self.raw[:-1], self.raw + b"!"):
            with self.subTest(size=len(raw)), mock.patch("urllib.request.urlopen") as download:
                self.archive.write_bytes(raw)
                with self.assertRaises(ValueError):
                    fetch(self.source, self.cache, root=self.root)
            download.assert_not_called()

    def test_absolute_empty_and_traversing_paths_are_rejected(self):
        for path in ("/tmp/proof.tar.xz", "", "../proof.tar.xz", "a/../proof.tar.xz",
                     "./proof.tar.xz", "a//proof.tar.xz", "a/"):
            with self.subTest(path=path):
                source = {**self.source, "archive_path": path}
                with self.assertRaises(ValueError):
                    self.load(source)
                with mock.patch("urllib.request.urlopen") as download:
                    with self.assertRaises(ValueError):
                        fetch(source, self.cache, root=self.root)
                download.assert_not_called()

    def test_symlink_cannot_escape_workspace(self):
        with tempfile.TemporaryDirectory(prefix="outside-certificate-source-") as temporary:
            external = Path(temporary) / "proof.tar.xz"
            external.write_bytes(self.raw)
            self.archive.unlink()
            self.archive.symlink_to(external)
            with mock.patch("urllib.request.urlopen") as download:
                with self.assertRaisesRegex(ValueError, "escapes the workspace"):
                    fetch(self.source, self.cache, root=self.root)
            download.assert_not_called()

    def test_unknown_transport_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "transport"):
            self.load({**self.source, "transport": "automatic"})

    def test_remote_descriptor_still_requires_repository_and_revision(self):
        remote = {**self.source, "transport": "remote"}
        with self.assertRaisesRegex(ValueError, "repository"):
            self.load(remote)
        remote.update(repository="example/data", revision="main", revision_kind="ref")
        self.assertEqual(self.load(remote), remote)
        del remote["transport"]
        self.assertEqual(self.load(remote), remote)


if __name__ == "__main__":
    unittest.main()

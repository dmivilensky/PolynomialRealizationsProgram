"""Part II data boundaries: malformed transport never becomes proof input."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest import mock

from Tools.Certificates.PolyakPartII import Payload


class PartIIArchiveTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="part2-archive-test-")
        self.addCleanup(temporary.cleanup)
        self.path = Path(temporary.name) / "proof.tar.xz"
        self.raw = {name + ".json": json.dumps({"schema": Payload.SCHEMA, "kind": name,
                                               "data": {}}).encode()
                    for name in Payload.GROUPS}

    def write(self, *, edit_manifest=None, extra=(), duplicate=False, symlink=False):
        manifest = {"format": Payload.FORMAT, "version": 1, "schema": Payload.SCHEMA,
                    "members": {name: {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}
                                for name, raw in self.raw.items()}}
        if edit_manifest:
            edit_manifest(manifest)
        members = [("manifest.json", json.dumps(manifest).encode()), *self.raw.items(), *extra]
        if duplicate:
            members.append(members[-1])
        with tarfile.open(self.path, "w:xz") as stream:
            for name, raw in members:
                member = tarfile.TarInfo(name)
                member.size = len(raw)
                if symlink and name == "rational.json":
                    member.type = tarfile.SYMTYPE
                    member.linkname = "/outside/data.json"
                    member.size = 0
                stream.addfile(member, io.BytesIO(raw))

    def test_complete_versioned_json_data_is_read_without_extraction(self):
        self.write()
        data = Payload.read_archive(self.path)
        self.assertEqual(set(data["groups"]), set(Payload.GROUPS))
        self.assertEqual(set(self.path.parent.iterdir()), {self.path})

    def test_duplicate_member_is_rejected(self):
        self.write(duplicate=True)
        with self.assertRaisesRegex(ValueError, "duplicate"):
            Payload.read_archive(self.path)

    def test_symlink_is_rejected(self):
        self.write(symlink=True)
        with self.assertRaisesRegex(ValueError, "regular"):
            Payload.read_archive(self.path)

    def test_executable_or_external_path_member_is_rejected(self):
        for name in ("run.py", "../outside.json", "/absolute.json"):
            self.write(extra=((name, b"raise RuntimeError('must never execute')"),))
            with self.assertRaises(ValueError):
                Payload.read_archive(self.path)

    def test_wrong_member_digest_is_rejected(self):
        self.write(edit_manifest=lambda m: m["members"]["rational.json"].update(sha256="0"*64))
        with self.assertRaisesRegex(ValueError, "digest"):
            Payload.read_archive(self.path)

    def test_floats_and_nonfinite_values_are_rejected_even_with_matching_hashes(self):
        for value in ("1.25", "NaN", "Infinity"):
            self.raw["rational.json"] = ('{"schema":"'+Payload.SCHEMA+'","kind":"rational",'
                                          '"data":{"value":'+value+'}}').encode()
            self.write()
            with self.assertRaisesRegex(ValueError, "Nonexact"):
                Payload.read_archive(self.path)

    def test_duplicate_json_keys_are_rejected_even_with_matching_hashes(self):
        self.raw["rational.json"] = ('{"schema":"'+Payload.SCHEMA+'","kind":"rational",'
                                      '"data":{},"data":{}}').encode()
        self.write()
        with self.assertRaises(ValueError):
            Payload.read_archive(self.path)

    def test_size_limit_is_enforced_before_reading_payload(self):
        self.write()
        with mock.patch.object(Payload, "MAX_MEMBER_BYTES", 8):
            with self.assertRaisesRegex(ValueError, "bounded"):
                Payload.read_archive(self.path)

    def test_manifest_cannot_add_preparation_or_paper_metadata(self):
        for field in ("preparation", "paper"):
            self.write(edit_manifest=lambda m: m.update({field: "unrelated"}))
            with self.assertRaisesRegex(ValueError, "manifest"):
                Payload.read_archive(self.path)

    def test_noncanonical_or_inexact_rationals_are_rejected(self):
        for value in ([2, 4], [1, 0], [1, -1], [True, 1], [0.5, 1], "1/2"):
            with self.assertRaises(ValueError):
                Payload.rational(value)
        self.assertEqual(Payload.rational([1, 2]).numerator, 1)


if __name__ == "__main__":
    unittest.main()

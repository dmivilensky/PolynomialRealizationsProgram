"""Bounded JSON-only Part II interchange reader; supplier code is never executed."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import tarfile

from ..PrepareCertificate import safe_path, unique_object

FORMAT = "HEAVY_BALL_PARTII_PROOF_DATA"
SCHEMA = "heavy-ball-part2-proof-v1"
GROUPS = ("rational", "exact313", "plateaus", "trigonometry", "system313")
MEMBERS = frozenset({"manifest.json", *(group + ".json" for group in GROUPS)})
MAX_MEMBER_BYTES = 32 << 20
MAX_TOTAL_BYTES = 96 << 20


def _invalid_number(value):
    raise ValueError("Nonexact JSON number in mathematical witnesses: " + value)


def decode(raw):
    return json.loads(raw, object_pairs_hook=unique_object,
                      parse_float=_invalid_number, parse_constant=_invalid_number)


def rational(value):
    """Canonical reduced numerator/positive denominator, never a decimal float."""
    if (not isinstance(value, list) or len(value) != 2 or
            any(type(x) is not int for x in value) or value[1] <= 0):
        raise ValueError("Expected [integer numerator, positive integer denominator]")
    result = Fraction(*value)
    if [result.numerator, result.denominator] != value:
        raise ValueError("Noncanonical rational witness")
    return result


def read_archive(path):
    raw, total = {}, 0
    with tarfile.open(Path(path), "r:xz") as stream:
        for member in stream:
            safe_path(member.name)
            if member.name not in MEMBERS or member.name in raw:
                raise ValueError("Unexpected or duplicate Part II archive member")
            if not member.isfile() or not 0 <= member.size <= MAX_MEMBER_BYTES:
                raise ValueError("Part II archive needs bounded regular JSON members")
            total += member.size
            if total > MAX_TOTAL_BYTES:
                raise ValueError("Part II archive exceeds its uncompressed limit")
            handle = stream.extractfile(member)
            if handle is None:
                raise ValueError("Unreadable archive member")
            value = handle.read(member.size + 1)
            if len(value) != member.size:
                raise ValueError("Inconsistent archive member length")
            raw[member.name] = value
    if set(raw) != MEMBERS:
        raise ValueError("Incomplete Part II mathematical archive")
    manifest = decode(raw["manifest.json"])
    if (not isinstance(manifest, dict) or set(manifest) != {"format", "version", "schema", "members"}
            or manifest["format"] != FORMAT or type(manifest["version"]) is not int
            or manifest["version"] != 1 or manifest["schema"] != SCHEMA
            or not isinstance(manifest["members"], dict)
            or set(manifest["members"]) != MEMBERS - {"manifest.json"}):
        raise ValueError("Unsupported Part II interchange manifest")
    groups = {}
    for group in GROUPS:
        name = group + ".json"
        record = manifest["members"][name]
        if (not isinstance(record, dict) or set(record) != {"bytes", "sha256"}
                or type(record["bytes"]) is not int or record["bytes"] != len(raw[name])
                or record["sha256"] != hashlib.sha256(raw[name]).hexdigest()):
            raise ValueError("Part II member size or digest mismatch: " + name)
        payload = decode(raw[name])
        if (not isinstance(payload, dict) or set(payload) != {"schema", "kind", "data"}
                or payload["schema"] != SCHEMA or payload["kind"] != group
                or not isinstance(payload["data"], dict)):
            raise ValueError("Unsupported Part II mathematical member: " + name)
        groups[group] = payload["data"]
    return {"manifest": manifest, "groups": groups, "raw": raw}

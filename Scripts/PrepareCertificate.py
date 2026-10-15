"""Read the pinned proof archive as exact, provenance-bound reference data.

No bundled Python/C++ source is executed. Successful preparation is not
acceptance of numerical claims; the residual and quadrature verifiers build Lean proofs.
"""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction
import hashlib
import json
from pathlib import PurePosixPath
import re
import tarfile



def digest(data):
    """
    Compute the SHA-256 byte digest used to compare archive members with their provenance
    manifest.
    """
    return hashlib.sha256(data).hexdigest()


def safe_path(name):
    """
    Validate a relative archive member path, rejecting absolute paths and empty, dot or parent
    components before any extraction.
    """
    path = PurePosixPath(name)
    if path.is_absolute() or any(p in ("", ".", "..") for p in name.split("/")):
        raise ValueError(f"Invalid archive member: {name}")
    return path


def unique_object(pairs):
    """
    Decode a JSON object while rejecting duplicate keys. This prevents two consumers from
    interpreting the same provenance field differently.
    """
    out = {}
    for key, value in pairs:
        if key in out:
            raise ValueError(f"Duplicate JSON field: {key}")
        out[key] = value
    return out


def load_json(raw):
    """
    Parse JSON with the duplicate-key guard used for manifests and embedded certificates.
    """
    return json.loads(raw, object_pairs_hook=unique_object)


def exact_number(token):
    """
    Decode supported hexadecimal floats, decimals or rational literals into exact fractions. No
    binary floating-point rounding is introduced. ReferenceInputs separately proves the
    byte-token-value correspondence in Lean.
    """
    if re.fullmatch(r"[+-]?0x[0-9a-fA-F]+(?:\.[0-9a-fA-F]+)?p[+-]?\d+", token):
        sign = -1 if token.startswith("-") else 1
        body = token.lstrip("+-")[2:]
        mantissa, exponent = body.split("p")
        pieces = mantissa.split(".")
        numerator = int("".join(pieces), 16)
        denominator = 16 ** (len(pieces[1]) if len(pieces) == 2 else 0)
        exponent = int(exponent)
        scale = Fraction(2 ** exponent) if exponent >= 0 else Fraction(1, 2 ** -exponent)
        return sign * Fraction(numerator, denominator) * scale
    if not re.fullmatch(r"[+-]?(?:\d+(?:\.\d+)?(?:e[+-]?\d+)?|\d+/[1-9]\d*)", token):
        raise ValueError(f"Unsupported exact numeric token: {token}")
    return Fraction(token)


def numeric_tokens(text):
    """
    Extract the whitespace-delimited numeric tokens from the reference text. ReferenceInputs
    also emits the original bytes and a Lean-checked tokenization.
    """
    return [t for t in text.split() if t[0] in "+-0123456789"]


REFERENCE_MEMBERS = frozenset({
    "embedded/reference/reference.txt",
    "data/reference/support-filter-flow.txt",
})


def prepare_payload(archive, folder):
    """
    Extract only the two members used by the 1.000013 proof.

    The caller pins the entire archive. The original manifest and both member hashes are
    checked on every call, including cached extraction. No bundled program is extracted or
    executed.
    """
    payload = folder / "payload"
    with tarfile.open(archive, "r:xz") as source:
        original = source.extractfile("manifest.json").read()
        manifest = load_json(original)
        if manifest["format"] != "SINEJACOBI_PROOF_3":
            raise ValueError("Unsupported proof archive format")
        flow_name = "data/reference/support-filter-flow.txt"
        if not {flow_name, "claims.json"} <= manifest["members"].keys():
            raise ValueError("Reference data absent from manifest")
        payload.mkdir(parents=True, exist_ok=True)
        cached_manifest = payload / "manifest.json"
        if cached_manifest.exists() and cached_manifest.read_bytes() != original:
            raise ValueError("Cached manifest differs from pinned archive")
        cached_manifest.write_bytes(original)
        claims_raw = source.extractfile("claims.json").read()
        expected = manifest["members"]["claims.json"]
        if len(claims_raw) != expected["bytes"] or digest(claims_raw) != expected["sha256"]:
            raise ValueError("Embedded reference container mismatch")
        claims = load_json(claims_raw)
        if claims["format"] != "SINEJACOBI_CERTIFICATES_2":
            raise ValueError("Unsupported embedded reference container")
        reference = claims["files"]["reference/reference.txt"]
        reference_raw = reference["text"].encode("ascii")
        if digest(reference_raw) != reference["sha256"]:
            raise ValueError("Embedded reference hash mismatch")
        reference_target = payload / "embedded/reference/reference.txt"
        if reference_target.exists() and reference_target.read_bytes() != reference_raw:
            raise ValueError("Cached reference differs from archive")
        reference_target.parent.mkdir(parents=True, exist_ok=True)
        reference_target.write_bytes(reference_raw)
        for name in [flow_name]:
            safe_path(name)
            target = payload / name
            if not target.exists():
                member = source.getmember(name)
                if not member.isfile():
                    raise ValueError("Reference member is not regular")
                raw = source.extractfile(member).read()
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(raw)
            raw = target.read_bytes()
            expected = manifest["members"][name]
            if len(raw) != expected["bytes"] or digest(raw) != expected["sha256"]:
                raise ValueError(f"Reference member mismatch: {name}")
    return payload, manifest

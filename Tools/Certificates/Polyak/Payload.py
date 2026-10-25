"""Read versioned mathematical data; never extract or execute upstream code.

Archive identity is checked by FetchCertificate before this reader is called.
Member hashes bind the JSON records. Neither those hashes nor external check
reports are mathematical premises: emitted Lean proofs check the actual claims.
"""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import tarfile

from ..PrepareCertificate import safe_path, unique_object

FORMAT = "HEAVY_BALL_PART1_PROOF"
SCHEMA = "heavy-ball-part1-proof-v1"
REQUIRED = frozenset({"schema.json", "mathematics.json", "interval-p1.json",
                      "interval-central.json", "checks.json"})
ALLOWED = REQUIRED | {"interval-p2.json"}
MAX_MEMBER_BYTES = 64 << 20
MAX_TOTAL_BYTES = 256 << 20
_payload = None


def _constant(value):
    raise ValueError("nonfinite JSON number: " + value)


def _floating(value):
    raise ValueError("floating number in exact mathematical data: " + value)


def _json(raw, exact=False):
    options = {"object_pairs_hook": unique_object, "parse_constant": _constant}
    if exact:
        options["parse_float"] = _floating
    return json.loads(raw, **options)


def _versioned(raw, name, kind, exact=False):
    """Require the member's own version and kind, independently of the manifest."""
    record = _json(raw[name], exact=exact)
    if (not isinstance(record, dict) or record.get("schema") != SCHEMA or
            record.get("kind") != kind):
        raise ValueError("unsupported proof member schema or kind: " + name)
    return record


def exact_fraction(token):
    """Require canonical reduced rational strings, without decimal conversion."""
    if not isinstance(token, str) or not re.fullmatch(
            r"-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?", token):
        raise ValueError("expected a canonical rational string")
    result = Fraction(token)
    if str(result) != token:
        raise ValueError("noncanonical rational string: " + token)
    return result


def validate_polynomial(record):
    """Check exact coefficients, variable order and distinct monomial tuples."""
    if not isinstance(record, dict) or set(record) != {"variables", "terms"}:
        raise ValueError("invalid polynomial record")
    variables, terms = record["variables"], record["terms"]
    if (not isinstance(variables, list) or len(variables) > 16 or
        any(not isinstance(name, str) or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name)
            for name in variables) or len(set(variables)) != len(variables) or
        not isinstance(terms, list) or len(terms) > 20000):
        raise ValueError("invalid polynomial dimensions")
    previous = None
    for term in terms:
        if not isinstance(term, list) or len(term) != 2:
            raise ValueError("invalid monomial")
        coefficient, powers = term
        if not exact_fraction(coefficient):
            raise ValueError("zero monomial coefficient")
        if (not isinstance(powers, list) or len(powers) != len(variables) or
            any(type(power) is not int or not 0 <= power <= 256 for power in powers)):
            raise ValueError("invalid monomial exponents")
        powers = tuple(powers)
        if previous is not None and powers <= previous:
            raise ValueError("monomials must be distinct and ordered")
        previous = powers


def _interval(record):
    if not isinstance(record, list) or len(record) != 2:
        raise ValueError("invalid exact interval")
    left, right = map(exact_fraction, record)
    if left > right:
        raise ValueError("reversed exact interval")


def _validate(value, depth=0):
    if depth > 256:
        raise ValueError("exact-data nesting limit exceeded")
    if isinstance(value, dict):
        if set(value) == {"variables", "terms"}:
            validate_polynomial(value)
            return
        for key in ("interval", "q_interval"):
            if key in value:
                _interval(value[key])
        intervals = value.get("intervals", {})
        if not isinstance(intervals, dict):
            raise ValueError("invalid exact interval table")
        for interval in intervals.values():
            _interval(interval)
        for child in value.values():
            _validate(child, depth + 1)
    elif isinstance(value, list):
        for child in value:
            _validate(child, depth + 1)
    elif isinstance(value, float):
        raise ValueError("floating number in mathematical data")


def read_archive(archive):
    """Read only the seven contracted JSON names, with bounded regular members."""
    with tarfile.open(archive, "r:xz") as stream:
        members = stream.getmembers()
        names = [member.name for member in members]
        if (len(names) != len(set(names)) or "manifest.json" not in names or
            not REQUIRED <= set(names) or not set(names) <= ALLOWED | {"manifest.json"}):
            raise ValueError("proof archive does not match the JSON-only member contract")
        total = 0
        raw = {}
        for member in members:
            safe_path(member.name)
            if not member.isfile() or not 0 <= member.size <= MAX_MEMBER_BYTES:
                raise ValueError("proof archive member is not a bounded regular file")
            total += member.size
            if total > MAX_TOTAL_BYTES:
                raise ValueError("proof archive exceeds the uncompressed size limit")
            handle = stream.extractfile(member)
            if handle is None:
                raise ValueError("proof archive member is unreadable")
            raw[member.name] = handle.read(member.size + 1)
            if len(raw[member.name]) != member.size:
                raise ValueError("proof archive member has an inconsistent length")
    manifest = _json(raw["manifest.json"])
    if (not isinstance(manifest, dict) or manifest.get("format") != FORMAT or
        type(manifest.get("version")) is not int or manifest["version"] != 1 or
        manifest.get("schema") != SCHEMA or
        not isinstance(manifest.get("members"), dict) or
        set(manifest.get("members", {})) != set(names) - {"manifest.json"}):
        raise ValueError("unsupported proof manifest")
    for name, expected in manifest["members"].items():
        if (not isinstance(expected, dict) or type(expected.get("bytes")) is not int or
            expected["bytes"] != len(raw[name]) or
            expected.get("sha256") != hashlib.sha256(raw[name]).hexdigest()):
            raise ValueError("proof member hash or size mismatch: " + name)
    mathematics = _versioned(raw, "mathematics.json", "mathematical-data", exact=True)
    groups = mathematics.get("groups")
    if (not isinstance(groups, dict) or set(groups) != {"core", "p2", "p5", "startup"} or
            any(not isinstance(value, dict) for value in groups.values())):
        raise ValueError("missing mathematical data groups")
    _validate(mathematics)
    for name in ("interval-p1.json", "interval-central.json", "interval-p2.json"):
        if name in raw:
            proposal = _versioned(raw, name, "parametric-krawczyk-proposals", exact=True)
            if proposal.get("family") != name.removeprefix("interval-").removesuffix(".json"):
                raise ValueError("proof member has an inconsistent family: " + name)
            _validate(proposal)
    # Reports are retained as provenance, never interpreted as accepted inequalities.
    _versioned(raw, "checks.json", "structured-external-check-report")
    schema = _json(raw["schema.json"])
    if not isinstance(schema, dict) or schema.get("$id") != "urn:heavy-ball:part1:proof:v1":
        raise ValueError("unsupported proof interchange schema")
    return {"manifest": manifest, "mathematics": mathematics, "raw": raw}


def configure(archive):
    """Select the already pinned archive for local generators in this process."""
    global _payload
    _payload = read_archive(Path(archive))
    return _payload


def group(name):
    if _payload is None:
        raise RuntimeError("configure the pinned mathematical archive before generating sources")
    return _payload["mathematics"]["groups"][name]


def interval_proposals(family):
    """Read only validated exact slab proposals; coverage flags remain untrusted."""
    if _payload is None:
        raise RuntimeError("configure the mathematical archive first")
    if family not in ("p1", "central", "p2"):
        raise ValueError("unknown continuation family")
    return _versioned(_payload["raw"], f"interval-{family}.json",
                      "parametric-krawczyk-proposals", exact=True)


def polynomial(record):
    """Decode exact polynomial data with a fixed constructor whitelist."""
    import sympy as s
    validate_polynomial(record)
    variables = [s.Symbol(name) for name in record["variables"]]
    return sum((s.Rational(coefficient) * s.prod(variable**power
                for variable, power in zip(variables, powers))
                for coefficient, powers in record["terms"]), s.S.Zero)


def rational(record):
    """Decode a quotient; pointwise nonvanishing remains a Lean obligation."""
    if not isinstance(record, dict) or set(record) != {"numerator", "denominator"}:
        raise ValueError("invalid rational-function record")
    numerator, denominator = record["numerator"], record["denominator"]
    if numerator["variables"] != denominator["variables"]:
        raise ValueError("inconsistent rational-function variable order")
    denominator = polynomial(denominator)
    if denominator == 0:
        raise ValueError("identically zero rational-function denominator")
    return polynomial(numerator) / denominator

"""Exact mathematical data and the versioned Part I interchange contract."""
from importlib import import_module
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import tarfile
import sympy as s

from .certificates.schema import SCHEMA, polynomial, rational, validate
from .verify import (read_json, write_json, source_hashes, versions,
                     requirements_hash, GROUPS)
from .paths import ROOT, MATH, GENERATED, PROOF

FORMAT = "HEAVY_BALL_PART1_PROOF"
REQUIRED_MEMBERS = {"schema.json", "mathematics.json", "interval-p1.json",
                    "interval-central.json", "checks.json"}
OPTIONAL_MEMBERS = {"interval-p2.json"}


def core_export():
    from .algebra.systems import build, G, u, c
    rho, q = s.symbols("rho q")
    core = {"id": "core", "polynomials": {}, "rationals": {}, "intervals": {},
            "checks": [], "normalization": {
                "G": "cosh(t)", "u": "sinh(v)",
                "normalized_lag": "[g(T_n(G)-T_n(c)) +/- 2u(1-c^2)U_(n-1)(c)]/U_(n-1)(G)",
                "p1": {"parameter": "z=1/G", "u": "1-z/2+z^2*A", "atom": "z^2*B"},
                "p2": {"parameter": "G", "unknowns": ["u", "x", "y", "p", "d", "W"],
                       "d": "C*sinh(t)"},
                "central": {"parameter": "h=G-1", "u": "1/2+h*A",
                            "main_atom": "-1/2+h*B", "second_mass": "h*P",
                            "d": "C*sinh(t)=h*D"}}}
    source = {
        "spiral_master": (rho*rho*(rho*rho+1)-2*q*rho*(rho*rho-rho+1)-q*q*(rho*rho+1), [rho, q]),
        "spiral_limit": (rho**4-2*rho**3+2*rho*rho-2*rho-1, [rho]),
        "spiral_switch": (32*G**3-36*G*G+4*G-1, [G]),
        "onewave_switch": (2*G*G-2*G-1, [G]),
        "critical_dual_quotient": (40*c**4-40*c**3-12*c*c+21*c+15, [c]),
    }
    for name, (expression, variables) in source.items():
        core["polynomials"][name] = polynomial(expression, variables)
    for n in range(25):
        core["polynomials"][f"T{n}"] = polynomial(s.chebyshevt(n, c), [c])
        core["polynomials"][f"U{n}"] = polynomial(s.chebyshevu(n, c), [c])
    for family in ("p1", "p2", "central"):
        model = build(family)
        variables = [model.parameter, *model.variables]
        for index, expression in enumerate(model.equations):
            core["polynomials"][f"{family}_F{index}"] = polynomial(expression, variables)
        core["rationals"][f"{family}_dual"] = rational(
            model.dual, sorted(model.dual.free_symbols, key=str))
    return core


def _current_verification(path):
    manifest = read_json(path / "manifest.json")
    profile = manifest.get("profile")
    if (manifest.get("layout") != "heavy-ball-certification-v1" or
        manifest.get("historical") is not False or
        manifest.get("sources_sha256") != source_hashes() or
        manifest.get("requirements_sha256") != requirements_hash()):
        raise ValueError("export requires current source and requirements verification")
    if profile not in ("proof", "complete") or manifest.get("selected_groups") != list(GROUPS):
        raise ValueError("export requires the full proof or complete profile")
    expected = 26 if profile == "proof" else 27
    if (manifest.get("passed") is not True or len(manifest["results"]) != expected or
        not all(record["passed"] for record in manifest["results"]) or
        manifest.get("slabs_per_family") != 4000):
        raise ValueError("export requires a successful 4000-slab cold verification")
    return manifest


def export_bundle(output=None, verification=None):
    """Build mathematical JSON; no program text is part of the interchange format."""
    if not __debug__:
        raise RuntimeError("exact export must not run under python -O")
    output = Path(output or MATH)
    verification = Path(verification or GENERATED / "verification")
    verified = _current_verification(verification)
    profile = verified["profile"]
    groups = {"core": core_export()}
    for name in ("p2", "p5", "startup"):
        groups[name] = import_module(".certificates." + name, __package__).export()
    mathematics = {"schema": SCHEMA, "kind": "mathematical-data", "groups": groups}
    validate(mathematics)
    output.mkdir(parents=True, exist_ok=True)
    write_json(output / "mathematics.json", mathematics)
    files = ["mathematics.json"]
    from .algebra.systems import build
    for family in ("p1", "p2", "central"):
        if family == "p2" and profile == "proof":
            continue
        proposal_path = verification / "continuation" / (family + "_boxes.json.gz")
        if not proposal_path.is_file():
            raise ValueError("missing continuation proposals; perform cold verification first")
        boxes = [box["exact"] for box in read_json(proposal_path)]
        model = build(family)
        dimension = len(model.variables)
        if len(boxes) != 4000:
            raise ValueError("incomplete continuation cover")
        fields = ("parameter", "centre", "radii", "inverse")
        for index, box in enumerate(boxes):
            if Fraction(box["parameter"][0]) >= Fraction(box["parameter"][1]):
                raise ValueError("nonpositive proposal interval width")
            if index and boxes[index-1]["parameter"][1] != box["parameter"][0]:
                raise ValueError("continuation proposals do not form an adjacent exact cover")
            if (len(box["centre"]) != dimension or len(box["radii"]) != dimension or
                any(Fraction(radius) <= 0 for radius in box["radii"])):
                raise ValueError("invalid box dimensions or radii")
            if len(box["inverse"]) != dimension or any(len(row) != dimension for row in box["inverse"]):
                raise ValueError("invalid preconditioner dimensions")
        payload = {"schema": SCHEMA, "kind": "parametric-krawczyk-proposals",
                   "family": family, "parameter": str(model.parameter),
                   "unknown_order": [str(variable) for variable in model.variables],
                   "source_group": "core",
                   "source_equations": [family + "_F" + str(index) for index in range(dimension)],
                   "parameter_domain": [boxes[0]["parameter"][0], boxes[-1]["parameter"][1]],
                   "proposal_precision_bits": 160, "exact_adjacent_cover": True,
                   "replay": "Recompute Krawczyk, derivative and sign bounds from the source systems and exact rational proposals.",
                   "boxes": [{key: box[key] for key in fields} for box in boxes]}
        validate(payload)
        filename = f"interval-{family}.json"
        write_json(output / filename, payload)
        files.append(filename)
    checks = {"schema": SCHEMA, "kind": "structured-external-check-report",
              "historical": False, "results": [
                  read_json(verification / "checks" / (record["suite"] + ".json"))
                  for record in verified["results"]]}
    write_json(output / "checks.json", checks)
    files.append("checks.json")
    schema = (PROOF / "schema.json").read_bytes()
    (output / "schema.json").write_bytes(schema)
    files.append("schema.json")
    manifest = {"format": FORMAT, "version": 1, "schema": SCHEMA,
                "producer": {"repository": "https://github.com/dmivilensky/Heavy-Ball",
                             "source_directory": "part1/certification", "versions": versions(),
                             "sources_sha256": source_hashes(),
                             "requirements_sha256": requirements_hash()},
                "provenance": {"verification_scope": "current-producer",
                               "fresh_verification": True,
                               "source_history": read_json(ROOT / "PROVENANCE.json")},
                "verification": {"profile": profile, "suites": len(verified["results"]),
                                 "slabs": 8000 if profile == "proof" else 12000,
                                 "check_evaluations": verified["check_evaluations"]},
                "members": {name: {"bytes": (output / name).stat().st_size,
                                   "sha256": hashlib.sha256((output / name).read_bytes()).hexdigest()}
                            for name in files}}
    write_json(output / "manifest.json", manifest)
    obsolete = output / "interval-p2.json"
    if obsolete.name not in files and obsolete.exists():
        obsolete.unlink()
    return {"manifest": "manifest.json", "members": len(files),
            "bytes": sum(record["bytes"] for record in manifest["members"].values())}


def read_bundle(path):
    """Read a flat JSON directory or archive without extracting archive paths."""
    path = Path(path)
    if path.is_dir():
        manifest = read_json(path / "manifest.json")
        return manifest, {name: (path / name).read_bytes() for name in _member_names(manifest)}
    with tarfile.open(path, mode="r:xz") as archive:
        members = archive.getmembers()
        names = [member.name for member in members]
        if len(names) != len(set(names)) or any(not member.isfile() for member in members):
            raise ValueError("duplicate or non-file archive member")
        if "manifest.json" not in names:
            raise ValueError("missing proof manifest")
        manifest = json.loads(archive.extractfile("manifest.json").read())
        expected = _member_names(manifest)
        if set(names) != expected | {"manifest.json"}:
            raise ValueError("unexpected archive members")
        return manifest, {name: archive.extractfile(name).read() for name in expected}


def _member_names(manifest):
    if (manifest.get("format") != FORMAT or manifest.get("version") != 1 or
        manifest.get("schema") != SCHEMA):
        raise ValueError("unsupported Part I proof data contract")
    names = set(manifest["members"])
    if names not in (REQUIRED_MEMBERS, REQUIRED_MEMBERS | OPTIONAL_MEMBERS):
        raise ValueError("unexpected or missing mathematical data members")
    return names


def check_bundle(path):
    """Validate interchange format and integrity, independently of producer run flags."""
    manifest, payloads = read_bundle(path)
    for name, record in manifest["members"].items():
        raw = payloads[name]
        if (type(record.get("bytes")) is not int or record["bytes"] < 0 or
            not isinstance(record.get("sha256"), str) or
            len(record["sha256"]) != 64 or
            any(character not in "0123456789abcdef" for character in record["sha256"])):
            raise ValueError("invalid member size or digest: " + name)
        if (len(raw) != record["bytes"] or hashlib.sha256(raw).hexdigest() != record["sha256"]):
            raise ValueError("mathematical data hash mismatch: " + name)
        data = json.loads(raw)
        if name == "schema.json":
            if data.get("$id") != "urn:heavy-ball:part1:proof:v1":
                raise ValueError("unexpected interchange schema")
        else:
            if data.get("schema") != SCHEMA:
                raise ValueError("member schema version mismatch: " + name)
            validate(data)
    mathematical = json.loads(payloads["mathematics.json"])
    if set(mathematical.get("groups", {})) != {"core", "p2", "p5", "startup"}:
        raise ValueError("missing or unexpected mathematical groups")
    return {"passed": True, "meaning": "data format and content integrity",
            "members": len(payloads), "schema": SCHEMA,
            "verification_scope": manifest.get("provenance", {}).get("verification_scope", "unspecified")}

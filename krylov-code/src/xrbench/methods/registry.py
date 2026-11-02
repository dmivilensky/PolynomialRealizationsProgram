"""The single ordered registry for all methods and experimental roles.

Importing this module reads metadata only. Solver and native-library imports are
lazy, so planning and article generation never construct optimization methods.
"""

import importlib
import json

from xrbench.paths import RESOURCES

_entries = json.loads((RESOURCES / "methods.json").read_text())
CATALOG = {entry["method"]: entry for entry in _entries}
if len(CATALOG) != len(_entries):
    raise ValueError("Duplicate method labels in the catalog")
for _label, _entry in CATALOG.items():
    if _entry["kind"] not in {"practical", "exactls", "ablation", "reference"}:
        raise ValueError(f"Invalid execution kind for {_label}")
    if _entry["role"] not in {"practical", "exact", "ablation", "class", "oracle", "reference"}:
        raise ValueError(f"Invalid comparison role for {_label}")
    if not _entry["module"].startswith("xrbench.methods."):
        raise ValueError(f"Invalid solver module for {_label}")
METHODS = {
    label: (entry["module"], entry["params"], entry["kind"], entry["restrictions"])
    for label, entry in CATALOG.items()
}
SOURCES = dict.fromkeys(CATALOG, "resources/methods.json")


def get_solve(label):
    """Return the registered solve(oracle, x0, **params) callable."""
    return importlib.import_module(METHODS[label][0]).solve


def applies(label, problem):
    """Return (allowed, resolved parameters or an explicit restriction reason)."""
    _, params, _, rules = METHODS[label]
    params = dict(params)
    meta = getattr(problem, "meta", {})
    if "max_n" in rules and problem.n > rules["max_n"]:
        return False, f"n > {rules['max_n']}"
    if rules.get("convex_only") and not getattr(problem, "convex", False):
        return False, "nonconvex"
    if rules.get("quadratic_only") and not meta.get("convex_quadratic", False):
        return False, "requires a certified convex quadratic (Dai-Kou 2016)"
    if rules.get("needs_hvp") and not hasattr(problem, "hvp"):
        return False, "no hvp"
    if rules.get("no_stateful") and meta.get("stateful"):
        return False, "stateful problem"
    if rules.get("reject_invalid_L") and meta.get("global_L_valid") is False:
        return False, "no finite global L for fixed-L Nesterov"
    for name in rules.get("meta_params", []):
        if name not in meta:
            return False, f"meta {name} missing"
        params[name] = meta[name]
    return True, params

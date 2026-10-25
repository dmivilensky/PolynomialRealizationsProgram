"""Structured verification outcomes; presentation has no mathematical effect."""
from dataclasses import dataclass, field
import hashlib
import json


class VerificationError(RuntimeError):
    pass


@dataclass
class Collector:
    suite: str
    checks: dict = field(default_factory=dict)
    notes: list = field(default_factory=list)
    artifacts: dict = field(default_factory=dict)

    def check(self, condition, label, *, kind="exact"):
        passed = bool(condition)
        key = str(label)
        record = self.checks.setdefault(key, {"id": key, "kind": kind,
                                              "passed": True, "evaluations": 0})
        record["evaluations"] += 1
        record["passed"] &= passed
        if not passed:
            raise VerificationError(f"{self.suite}: {key}")
        return True

    def note(self, *values, **_presentation):
        """Record a derivation or numerical diagnostic, without accepting a claim."""
        self.notes.append([str(value) for value in values])

    def result(self):
        return {"suite": self.suite, "passed": bool(self.checks) and
                all(c["passed"] for c in self.checks.values()),
                "checks": list(self.checks.values()), "notes": self.notes}


def canonical_bytes(data):
    return (json.dumps(data, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=False, allow_nan=False) + "\n").encode()


def digest(data):
    return hashlib.sha256(canonical_bytes(data)).hexdigest()

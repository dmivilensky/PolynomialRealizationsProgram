"""Turn untrusted rational-angle enclosures into ordinary kernel-checked bounds."""
from pathlib import Path

from .Payload import rational

POINTS = frozenset({(j, 13) for j in range(13)} |
                   {(1, 3), (1, 4), (1, 5), (2, 5),
                    (3, 18), (4, 18), (3, 21), (4, 21), (5, 21)})
OUTPUTS = frozenset({"polyak/Certificates/PartII/Trigonometry/Bounds.lean"})


def leanq(value):
    value = rational(value)
    return f"({value.numerator}/{value.denominator})"


def generate(payload, root):
    if (not isinstance(payload, dict) or set(payload) != {"schema", "points"}
            or payload["schema"] != "heavy-ball-rational-trigonometry-v1"
            or not isinstance(payload["points"], list)):
        raise ValueError("Unsupported rational trigonometry proposals")
    points = {}
    for record in payload["points"]:
        if (not isinstance(record, dict) or set(record) != {"j", "k", "taylor_terms", "sin", "cos"}
                or type(record["j"]) is not int or type(record["k"]) is not int
                or type(record["taylor_terms"]) is not int or not 1 <= record["taylor_terms"] <= 64):
            raise ValueError("Invalid rational-angle proposal")
        point = record["j"], record["k"]
        if point not in POINTS or point in points:
            raise ValueError("Duplicate or unexpected rational-angle point")
        for name in ("sin", "cos"):
            interval = record[name]
            if (not isinstance(interval, list) or len(interval) != 2 or
                    rational(interval[0]) >= rational(interval[1])):
                raise ValueError("Invalid rational-angle interval")
        points[point] = record
    if set(points) != POINTS:
        raise ValueError("Incomplete rational-angle coverage")
    lines = ["import polyak.CertifiedExamples.Trigonometry", "",
             "/-! Generated mathematical proposals; every bound is checked by the ordinary kernel. -/",
             "namespace polyak.Certificates.PartII.Trigonometry", "open CertifiedExamples.Trigonometry", ""]
    for (j, k), record in sorted(points.items()):
        for name in ("sin", "cos"):
            lo, hi = map(leanq, record[name])
            lines += [f"theorem {name}_{k}_{j}_bounds :",
                      f"    (({lo} : ℚ) : ℝ) ≤ Real.{name} (2*Real.pi*{j}/{k}) ∧",
                      f"    Real.{name} (2*Real.pi*{j}/{k}) ≤ (({hi} : ℚ) : ℝ) := by",
                      f"  have h := {name}_bounds (2*{j}/{k}) {record['taylor_terms']} {lo} {hi} (by kernel_decide)",
                      f"  have he : (((2*{j}/{k}) : ℚ) : ℝ)*Real.pi = 2*Real.pi*{j}/{k} := by push_cast; ring",
                      "  rw [he] at h", "  exact h", ""]
    for name in ("cos", "sin"):
        intervals = []
        for j in range(13):
            lo, hi = map(leanq, points[j, 13][name])
            intervals.append(f"⟨{lo},{hi},by norm_num⟩")
        lines += [f"def {name}13Interval : Fin 13 → LeanCert.Core.IntervalRat :=",
                  "  ![" + ",".join(intervals) + "]", "",
                  f"theorem {name}13_mem (j : Fin 13) :",
                  f"    Real.{name} (2*Real.pi*j.val/13) ∈ {name}13Interval j := by",
                  "  fin_cases j"]
        for j in range(13):
            lines.append(f"  · simpa [{name}13Interval,LeanCert.Core.IntervalRat.mem_def] using {name}_13_{j}_bounds")
        lines.append("")
    lines += ["end polyak.Certificates.PartII.Trigonometry", ""]
    path = Path(root) / next(iter(OUTPUTS))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines))
    return sorted(OUTPUTS)

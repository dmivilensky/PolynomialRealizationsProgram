"""Locations internal to the independent Heavy-Ball repository."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PART1 = ROOT.parent
HEAVY_BALL = PART1.parent
GENERATED = ROOT / "generated"
MATH = GENERATED / "math"
PROOF = PART1 / "proof"

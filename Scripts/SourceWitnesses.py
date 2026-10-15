"""Keep article annotations when reproducing literal Lean witness sources."""
from pathlib import Path
import re

PAPER = "2610.05164v2"


def annotated_source(path: Path, source: str) -> str:
    """
    Attach the maintained module overview; compare all executable source bytes.
    """
    existing = path.read_text() if path.exists() else ""
    overview = re.search(r"/-!.*?-/", existing, re.S)
    if overview and PAPER in overview[0]:
        header = overview[0]
    else:
        header = f"""/-!
Article: {PAPER}, Proposition 6 and Section 4.1, factor 1.000013.
Use: exact witnesses for the complete reference trajectory and contact/amplitude integrals,
assembled by `Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
Acceptance is proved by kernel reduction; proposed numerical data are not assumptions.
-/"""
    generated = re.search(r"/-!.*?-/", source, re.S)
    if generated:
        source = source[:generated.start()] + source[generated.end():]
    end = max((m.end() for m in re.finditer(r"^import [^\n]*\n", source, re.M)), default=0)
    return source[:end] + "\n" + header + "\n" + source[end:].lstrip("\n")


def install_source(path: Path, source: str, check: bool = False) -> None:
    """
    Install the annotated generated witness, or compare it byte-for-byte in check mode.
    Maintained module prose is preserved; every executable source byte must still match the
    generator.
    """
    source = annotated_source(path, source)
    if check:
        if path.read_text() != source:
            raise ValueError("Different installed Lean witness source: " + str(path))
    else:
        path.write_text(source)

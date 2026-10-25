"""Local output paths for the Polyak certificate consumer.

The independent mathematics producer has no knowledge of these paths.
"""
from pathlib import Path

from ..FetchCertificate import ROOT


def lean_root(root=None):
    """Choose the local Lean checkout, independently of the input archive."""
    return ROOT if root is None else Path(root).resolve()


def lean_path(root, name):
    """Create the parent of a fixed, repository-relative local output path."""
    relative = Path(name)
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError("Lean output must have a local repository-relative path")
    target = lean_root(root) / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    return target

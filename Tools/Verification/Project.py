"""Discover checkable Lean source directories from Lake without an article registry."""
from dataclasses import dataclass
from pathlib import Path
import re
import tomllib


def lean_code(source):
    """Mask nested comments and strings so source checks inspect executable Lean only."""
    masked = list(source)
    i = 0
    while i < len(source):
        start = i
        if source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source.startswith("/-", i):
            depth = 1
            i += 2
            while depth and i < len(source):
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("Unterminated Lean block comment")
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            i += 1
            continue
        for j in range(start, min(i, len(source))):
            if source[j] != "\n":
                masked[j] = " "
    return "".join(masked)


def name_parts(name):
    """Split a Lean module name while preserving dots inside escaped components."""
    return tuple(part[1:-1] if part.startswith("«") else part
                 for part in re.findall(r"«[^»]+»|[^.]+", name))


def lean_name(parts):
    """Render filesystem components as a Lean name, quoting nonidentifier stems."""
    return ".".join(part if re.fullmatch(r"[^\W\d][\w']*", part) else f"«{part}»"
                    for part in parts)


def workspace_root(path):
    """Find the TOML Lake workspace containing a source directory or file."""
    path = Path(path).resolve()
    if path.is_file():
        path = path.parent
    for parent in (path, *path.parents):
        if (parent / "lakefile.toml").is_file():
            return parent
    raise ValueError(f"No lakefile.toml contains {path}")


def libraries(workspace):
    """Read library source directories and roots from the owning Lake configuration."""
    config = tomllib.loads((workspace / "lakefile.toml").read_text())
    base = workspace / config.get("srcDir", ".")
    result = []
    for library in config.get("lean_lib", []):
        source = (base / library.get("srcDir", ".")).resolve()
        roots = list(library.get("roots", [library["name"]]))
        roots.extend(glob.removesuffix(".+").removesuffix(".*")
                     for glob in library.get("globs", []))
        result.append((source, tuple(dict.fromkeys(name_parts(root) for root in roots))))
    return result


def source_paths(directory):
    """List visible Lean files under a namespace directory and its optional sibling root."""
    paths = {path.resolve() for path in directory.rglob("*.lean")
             if not any(part.startswith(".") for part in path.relative_to(directory).parts)}
    sibling = directory.parent / (directory.name + ".lean")
    if sibling.is_file():
        paths.add(sibling.resolve())
    return tuple(sorted(paths))


def workspace_sources(workspace):
    """Map all configured local library modules to their actual source paths."""
    sources = {}
    for source, roots in libraries(workspace):
        for parts in roots:
            directory = source.joinpath(*parts)
            for path in source_paths(directory):
                module = lean_name(path.relative_to(source).with_suffix("").parts)
                if module in sources and sources[module] != path:
                    raise ValueError(f"Ambiguous source module {module}: {sources[module]} and {path}")
                sources[module] = path
    return sources


@dataclass(frozen=True)
class Project:
    """A directory's Lake module prefix, source root and owned Lean sources."""
    workspace: Path
    directory: Path
    source_root: Path
    parts: tuple[str, ...]

    @property
    def module(self):
        """Return the Lean namespace corresponding to this source directory."""
        return lean_name(self.parts)

    @property
    def check_module(self):
        """Return the conventional complete-check module for this directory."""
        return lean_name((*self.parts, "Check"))

    @property
    def relative(self):
        """Return a stable workspace-relative directory name for logs and diagnostics."""
        return self.directory.relative_to(self.workspace).as_posix()

    @property
    def sources(self):
        """Include namespace sources and the sibling public root when one exists."""
        return source_paths(self.directory)

    def source_module(self, path):
        """Map an owned file through the library's configured source directory."""
        return lean_name(path.relative_to(self.source_root).with_suffix("").parts)


def resolve_project(directory, workspace=None):
    """Resolve any registered source directory with a Check.lean entry, without name cases."""
    path = Path(directory)
    if workspace is not None:
        workspace = Path(workspace).resolve()
        path = path if path.is_absolute() else workspace / path
    path = path.resolve()
    workspace = workspace or workspace_root(path)
    if not path.is_relative_to(workspace) or not (path / "Check.lean").is_file():
        raise ValueError(f"Expected a workspace source directory containing Check.lean: {path}")
    candidates = []
    for source, roots in libraries(workspace):
        if not path.is_relative_to(source):
            continue
        parts = path.relative_to(source).parts
        if parts and any(parts[:len(root)] == root or root[:len(parts)] == parts for root in roots):
            candidates.append(Project(workspace, path, source, parts))
    if not candidates:
        raise ValueError(f"Source directory is not registered as a Lake library: {path}")
    return max(candidates, key=lambda project: len(project.source_root.parts))


def discover_projects(workspace):
    """Discover every registered directory with a complete Check.lean entry point."""
    directories = {path.parent for path in workspace_sources(workspace).values()
                   if path.name == "Check.lean"}
    # A package's complete check owns its internal checker modules as sources.
    # They are not additional packages with independent complete coverage.
    roots = (path for path in directories
             if not any(parent in directories for parent in path.parents))
    return tuple(resolve_project(path, workspace) for path in sorted(roots))


def select_projects(directories=None, workspace=None):
    """Resolve explicit directory arguments or all checkable packages in the current workspace."""
    directories = list(directories or ["all"])
    if workspace is None:
        first = Path(directories[0]) if directories[0] != "all" else Path.cwd()
        workspace = workspace_root(first)
    workspace = Path(workspace).resolve()
    projects = (discover_projects(workspace) if directories == ["all"] else
                tuple(resolve_project(directory, workspace) for directory in directories))
    if not projects:
        raise ValueError(f"No registered directories contain Check.lean in {workspace}")
    return tuple(dict.fromkeys(projects))


def sync_aggregate(projects):
    """Refresh the optional Lake convenience aggregate from the same discovered checks."""
    path = projects[0].workspace / "Tools/Verification/All.lean"
    if not path.is_file():
        return
    source = "".join(f"import {project.check_module}\n" for project in projects)
    # Keep disabled local package imports available when refreshing the public aggregate.
    source += "".join(line + "\n" for line in path.read_text().splitlines()
                      if line.startswith("-- import "))
    source += '''
/-!
Shared complete-check entry point, maintained by `python3 -m Tools.Verification.Check all`.
Use: import every discovered package Check, including its source and axiom audits.
The checked mathematical coverage is documented in each package's own showcase and table.
-/
'''
    if path.read_text() != source:
        path.write_text(source)

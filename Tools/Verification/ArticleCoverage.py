"""Check an explicit article-coverage review, independently of source import coverage.

A reviewed correspondence is not a proof of equivalence of mathematical prose and
Lean types. Lean checks the referenced proofs; this tool detects stale source
reviews, omitted numbered claims and explicitly outstanding obligations. It never
infers full article coverage from a successful build or from a declaration count.
"""
import argparse
import hashlib
from pathlib import Path
import re

from .Project import lean_code, name_parts, select_projects
from .CheckCorrespondence import check_showcase

MAP_SOURCE = re.compile(r"^<!-- article-source: (\S+) sha256=([0-9a-f]{64}) -->$", re.M)
MAP_CLAIM = re.compile(
    r"^(Theorem|Lemma|Proposition|Corollary|Definition) ([A-Z0-9]+\.\d+)"
    r"(?: — (.*?))? \(`([^`]+)`\)$")
MAP_PROSE = re.compile(r"^- `([^`]+)` — (.+)$", re.M)


def ordered_claims(raw):
    """Read the shared section theorem counter used by a flattened article.

    This review format deliberately uses the ordinary amsthm setup of these
    articles: a counter shared by results, definitions and numbered remarks,
    reset at sections, with lettered sections after \\appendix. The pinned
    source includes the preamble; changing the numbering invalidates review.
    """
    text = re.sub(r"(?<!\\)%[^\n]*", "", raw)
    token = re.compile(
        r"\\section(\*?)\{[^}]*\}|\\appendix\b|"
        r"\\begin\{(theorem|lemma|proposition|corollary|definition|remark|assumption|example)\}"
        r"(?:\[([^\]]*)\])?(.*?)\\end\{\2\}", re.S)
    result = []
    section, counter, appendix = 0, 0, False
    for match in token.finditer(text):
        if match[0].startswith(r"\appendix"):
            section, counter, appendix = 0, 0, True
        elif match[0].startswith(r"\section"):
            if not match[1]:
                section += 1
                counter = 0
        else:
            counter += 1
            if match[2] not in ("theorem", "lemma", "proposition", "corollary", "definition"):
                continue
            labels = re.findall(r"\\label\{([^}]+)\}", match[4])
            if not labels:
                raise ValueError("Unlabelled article result requires an explicit coverage identifier")
            prefix = chr(64 + section) if appendix else str(section)
            result.append({"label": labels[0], "kind": match[2], "title": match[3] or "",
                           "number": f"{prefix}.{counter}"})
    if len({item["label"] for item in result}) != len(result):
        raise ValueError("Duplicate article claim")
    return result


def _map_review(project, path):
    """Use the readable correspondence itself as the exhaustive review record.

    No second inventory or per-package JSON file is necessary. Ordered rows
    identify PDF number, TeX label, title and exact declarations. Prose bullets
    retain the additional unnumbered obligations and their audited modules.
    The source digest is a human review seal, not a mathematical axiom.
    """
    raw = path.read_text()
    pins = MAP_SOURCE.findall(raw)
    if not pins:
        return None
    if len(dict(pins)) != len(pins):
        raise ValueError("Duplicate article source pin")
    actual = []
    for name, digest in pins:
        source = _local(project.workspace, name)
        if hashlib.sha256(source.read_bytes()).hexdigest() != digest:
            raise ValueError(f"Stale article coverage review: {name}")
        actual.extend({**claim, "source": name} for claim in ordered_claims(source.read_text()))
    entries = []
    for row in raw.splitlines():
        if not row.startswith("| ") or row.startswith(("| Article |", "| ---")):
            continue
        columns = row.split("|")
        if len(columns) != 5:
            raise ValueError("Article map rows need exactly three columns")
        match = MAP_CLAIM.fullmatch(columns[1].strip())
        if not match:
            raise ValueError(f"Invalid numbered article map row: {columns[1]}")
        entries.append({"label": match[4], "kind": match[1].lower(), "number": match[2],
                        "title": match[3] or "", "links": columns[2], "meaning": columns[3]})
    keys = ("label", "kind", "number", "title")
    if [[item[k] for k in keys] for item in entries] != [
            [item[k] for k in keys] for item in actual]:
        raise ValueError("Article claim inventory differs in labels, order, numbers, kinds or titles")
    # This also enforces exact declaration order and all file links in the showcase.
    check_showcase(project)
    showcase = (project.directory / "Article.lean").read_text()
    block_pattern = re.compile(
        r"/\-!\s*Article: (Theorem|Lemma|Proposition|Corollary|Definition) "
        r"([A-Z0-9]+\.\d+) \[([^\]]+)\]")
    markers = list(block_pattern.finditer(showcase))
    if [m.groups() for m in markers] != [
            (item["kind"].title(), item["number"], item["label"]) for item in actual]:
        raise ValueError("Showcase comments differ from the numbered article order")
    for marker, item in zip(markers, actual):
        caption = showcase[marker.end():].splitlines()[0].split("-/", 1)[0].rstrip()
        expected = ". " + item["title"] + "." if item["title"] else "."
        if caption != expected:
            raise ValueError(f"Showcase title differs from the article: {item['label']}")
    code = lean_code(showcase)
    if re.search(r"^#check\b", code[:markers[0].start()] if markers else code, re.M):
        raise ValueError("Showcase signature outside its numbered article block")
    for i, (marker, item) in enumerate(zip(markers, entries)):
        end = markers[i + 1].start() if i + 1 < len(markers) else len(code)
        checked = [name_parts(n) for n in re.findall(
            r"^#check @?([^\s]+)\s*$", code[marker.start():end], re.M)]
        listed = []
        for name in re.findall(r"\[([^\]]+)\]\([^)]+\.lean\)", item["links"]):
            parts = name_parts(name)
            listed.append(parts if parts[:len(project.parts)] == project.parts
                          else (*project.parts, *parts))
        if checked != listed:
            raise ValueError(f"Showcase signatures differ inside article block: {item['label']}")
    prose = MAP_PROSE.findall(raw)
    counts = re.findall(r"^<!-- article-prose-count: (\d+) -->$", raw, re.M)
    if (len(counts) != 1 or not prose or len(prose) != int(counts[0]) or
            len({label for label, _ in prose}) != len(prose)):
        raise ValueError("Unnumbered mathematics inventory differs")
    owned = set(project.sources)
    for item in entries:
        links = re.findall(r"\[([^\]]+)\]\(([^)]+\.lean)\)", item["links"])
        if not links or not item["meaning"].strip():
            raise ValueError(f"Article row needs signatures and a semantic correspondence: {item['label']}")
        for _, link in links:
            if _local(project.workspace, str((project.directory / link).relative_to(project.workspace))) not in owned:
                raise ValueError(f"Coverage reference outside package audit: {link}")
    for label, description in prose:
        links = re.findall(r"\[[^\]]+\]\(([^)]+\.lean)\)", description)
        if not links:
            raise ValueError(f"Unnumbered obligation has no audited proof references: {label}")
        for link in links:
            if _local(project.workspace, str((project.directory / link).relative_to(project.workspace))) not in owned:
                raise ValueError(f"Coverage reference outside package audit: {link}")
    if re.search(r"<!-- article-unresolved:", raw):
        raise ValueError("Incomplete article coverage: explicitly unresolved correspondence")
    print(f"{project.relative}: article map {len(entries)}/{len(actual)} ordered numbered claims; "
          f"{len(prose)} unnumbered groups; source review current.", flush=True)
    return {"numbered_claims": len(entries), "verified_numbered_claims": len(entries),
            "unnumbered_groups": len(prose)}


def _local(workspace, relative):
    if not isinstance(relative, str) or not relative or Path(relative).is_absolute():
        raise ValueError("Coverage paths must be workspace-relative")
    path = (workspace / relative).resolve()
    if not path.is_relative_to(workspace.resolve()) or not path.is_file():
        raise ValueError(f"Missing or external coverage source: {relative}")
    return path


def check(project, require_complete=False):
    """Validate the reviewed article map when present."""
    table = project.directory / "ArticleMap.md"
    review = _map_review(project, table) if table.is_file() else None
    if review is None and require_complete:
        raise ValueError(f"{project.relative}: no article coverage review")
    return review


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory")
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    try:
        for project in select_projects([args.directory]):
            check(project, require_complete=args.require_complete)
    except (OSError, ValueError, TypeError, KeyError) as error:
        parser.exit(1, f"Article coverage check failed: {error}\n")


if __name__ == "__main__":
    main()

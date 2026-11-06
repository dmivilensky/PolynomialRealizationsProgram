"""Check a reviewed correspondence map against its Lean showcase.

A reviewed correspondence is not a proof of equivalence of mathematical prose and
Lean types. Lean checks the referenced proofs; this tool detects inconsistent
inventories, omitted reviewed claims and explicitly outstanding obligations. It never
infers full article coverage from a successful build or from a declaration count.
The inputs are the review record and Lean sources; manuscripts are not inputs.
"""
import argparse
from pathlib import Path
import re

from .Project import lean_code, name_parts, select_projects
from .CheckCorrespondence import check_showcase

MAP_REVIEW = re.compile(r"^<!-- article-review -->$", re.M)
CLAIM_KINDS = r"Theorem|Lemma|Proposition|Corollary|Definition|Remark|Algorithm"
CLAIM_NUMBER = r"[A-Z0-9]+(?:\.\d+)?"
MAP_CLAIM = re.compile(
    rf"^({CLAIM_KINDS}) ({CLAIM_NUMBER})"
    r"(?: — (.*?))? \(`([^`]+)`\)$")
MAP_TOPIC = re.compile(r"^Topic — (.+?) \(`([^`]+)`\)$")
MAP_PROSE = re.compile(r"^- `([^`]+)` — (.+)$", re.M)


def _map_review(project, path, require_complete=False):
    """Use the readable correspondence itself as the exhaustive review record.

    No second inventory or per-package JSON file is necessary. Ordered rows
    identify reviewed labels, titles and exact declarations. A topic inventory
    deliberately carries no claim about manuscript numbering. Prose bullets
    retain the additional unnumbered obligations and their audited modules.
    """
    raw = path.read_text()
    markers = MAP_REVIEW.findall(raw)
    if not markers:
        return None
    if len(markers) != 1:
        raise ValueError("Duplicate article review marker")
    topic_mode = bool(re.search(r"^<!-- article-topic-count:", raw, re.M))
    inventory = "topic" if topic_mode else "numbered"
    entries = []
    for row in raw.splitlines():
        if not row.startswith("| ") or row.startswith(("| Article |", "| ---")):
            continue
        columns = row.split("|")
        if len(columns) != 5:
            raise ValueError("Article map rows need exactly three columns")
        match = (MAP_TOPIC if topic_mode else MAP_CLAIM).fullmatch(columns[1].strip())
        if not match:
            raise ValueError(f"Invalid {inventory} article map row: {columns[1]}")
        if topic_mode:
            entries.append({"label": match[2], "kind": "topic", "number": "",
                            "title": match[1], "links": columns[2], "meaning": columns[3]})
            continue
        if match[1] != "Algorithm" and "." not in match[2]:
            raise ValueError(f"Invalid mathematical claim number: {match[2]}")
        entries.append({"label": match[4], "kind": match[1].lower(), "number": match[2],
                        "title": match[3] or "", "links": columns[2], "meaning": columns[3]})
    counts = re.findall(rf"^<!-- article-{inventory}-count: (\d+) -->$", raw, re.M)
    if len(counts) != 1 or not entries or len(entries) != int(counts[0]):
        raise ValueError(f"Reviewed {inventory} claim inventory differs")
    if topic_mode and re.search(r"^<!-- article-numbered-count:", raw, re.M):
        raise ValueError("Mixed topic and numbered claim inventories")
    if len({item['label'] for item in entries}) != len(entries):
        raise ValueError("Duplicate reviewed claim label")
    if not topic_mode and len({(item['kind'], item['number']) for item in entries}) != len(entries):
        raise ValueError("Duplicate reviewed claim number")
    # This also enforces exact declaration order and all file links in the showcase.
    check_showcase(project)
    showcase = (project.directory / "Article.lean").read_text()
    block_pattern = (re.compile(r"/\-!\s*Article: (Topic)() \[([^\]]+)\]") if topic_mode
                     else re.compile(rf"/\-!\s*Article: ({CLAIM_KINDS}) "
                                     rf"({CLAIM_NUMBER}) \[([^\]]+)\]"))
    markers = list(block_pattern.finditer(showcase))
    if [m.groups() for m in markers] != [
            (item["kind"].title(), item["number"], item["label"]) for item in entries]:
        raise ValueError(f"Showcase comments differ from the reviewed {inventory} order")
    for marker, item in zip(markers, entries):
        caption = showcase[marker.end():].splitlines()[0].split("-/", 1)[0].rstrip()
        expected = ". " + item["title"] + "." if item["title"] else "."
        if caption != expected:
            raise ValueError(f"Showcase title differs from the reviewed map: {item['label']}")
    code = lean_code(showcase)
    if re.search(r"^#check\b", code[:markers[0].start()] if markers else code, re.M):
        raise ValueError(f"Showcase signature outside its {inventory} article block")
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
    unresolved = re.findall(r"<!-- article-unresolved: (.*?) -->", raw)
    if re.search(r"<!-- article-unresolved:", raw) and not unresolved:
        raise ValueError("Malformed unresolved correspondence marker")
    if unresolved and require_complete:
        raise ValueError("Incomplete article coverage: " + "; ".join(unresolved))
    print(f"{project.relative}: reviewed map {len(entries)} ordered {inventory} claims; "
          f"{len(prose)} unnumbered groups; map and Lean showcase consistent.", flush=True)
    if unresolved:
        print(f"{project.relative}: article coverage INCOMPLETE: " + "; ".join(unresolved), flush=True)
    status = {"complete": not unresolved, "unresolved_obligations": unresolved}
    # A consistent inventory with outstanding mathematical obligations is not a
    # certificate of full coverage. Only --require-complete enforces that claim;
    # ordinary proof builds can still check the existing, narrower theorems.
    if topic_mode:
        return {"topic_claims": len(entries), "verified_topic_claims": 0 if unresolved else len(entries),
                "unnumbered_groups": len(prose), **status}
    return {"numbered_claims": len(entries), "verified_numbered_claims": 0 if unresolved else len(entries),
            "unnumbered_groups": len(prose), **status}


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
    review = _map_review(project, table, require_complete=require_complete) if table.is_file() else None
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

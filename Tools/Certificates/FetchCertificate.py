"""Receive a pinned local or remote archive; this does not verify its mathematics."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tempfile
import urllib.request

ROOT = Path(__file__).resolve().parents[2]
CHUNK = 1 << 20


def load_source(path):
    """
    Read and validate the source descriptor: repository/archive location, format and expected
    cryptographic identity. This is operational provenance, not a mathematical axiom.
    """
    source = json.loads(path.read_text())
    if source.get("format") != "POLYNOMIAL_REALIZATIONS_CERTIFICATE_SOURCE":
        raise ValueError("Unknown source descriptor format")
    transport = source.get("transport", "remote")
    if transport not in ("local", "remote"):
        raise ValueError("Unknown certificate source transport")
    fields = [("archive_sha256", r"[0-9a-f]{64}")]
    if transport == "remote":
        fields.append(("repository", r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+"))
    for key, pattern in fields:
        if not isinstance(source.get(key), str) or not re.fullmatch(pattern, source[key]):
            raise ValueError(f"Invalid source field: {key}")
    if transport == "remote":
        kind = source.get("revision_kind", "commit")
        revision = source["revision"]
        if kind == "commit":
            valid_revision = isinstance(revision, str) and re.fullmatch(r"[0-9a-f]{40}", revision)
        elif kind == "ref":
            # Mutable refs are locators only: size and SHA-256 still pin every accepted byte.
            valid_revision = (isinstance(revision, str) and
                              re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._/-]*", revision) and
                              ".." not in revision and
                              all(part and not part.startswith(".") and
                                  not part.endswith((".", ".lock")) for part in revision.split("/")))
        else:
            raise ValueError("Unknown revision_kind: expected commit or ref")
        if not valid_revision:
            raise ValueError("Invalid source field: revision")
    if not isinstance(source.get("archive_path"), str):
        raise ValueError("Archive path must be a relative repository path")
    member = PurePosixPath(source["archive_path"])
    if member.is_absolute() or any(p in ("", ".", "..") for p in source["archive_path"].split("/")):
        raise ValueError("Archive path must be a relative repository path")
    if type(source["archive_bytes"]) is not int or source["archive_bytes"] <= 0:
        raise ValueError("Archive size must be a positive integer")
    return source


def verify_archive(path, source):
    """
    Check the downloaded archive against the descriptor's size/digest requirements before it
    can supply defining reference data.
    """
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(CHUNK), b""):
            size += len(block)
            if size > source["archive_bytes"]:
                raise ValueError("Archive exceeds pinned size")
            digest.update(block)
    if size != source["archive_bytes"] or digest.hexdigest() != source["archive_sha256"]:
        raise ValueError(f"Archive size/SHA-256 mismatch: {path}")


def fetch(source, cache, offline=False, *, root=ROOT):
    """
    Verify the declared local file on every call, or reuse/download a remote archive.
    A local source never falls back to a cached copy or the network. Offline mode
    permits existing local files and verified remote caches. Receipts record byte
    identity and cannot replace a Lean proof.
    """
    if source.get("transport", "remote") == "local":
        workspace = Path(root).resolve()
        relative = source["archive_path"]
        member = PurePosixPath(relative)
        if member.is_absolute() or any(p in ("", ".", "..") for p in relative.split("/")):
            raise ValueError("Local archive path must be workspace-relative")
        archive = (workspace / relative).resolve()
        if not archive.is_relative_to(workspace):
            raise ValueError("Local archive escapes the workspace")
        verify_archive(archive, source)
        folder = Path(cache) / source["archive_sha256"]
        folder.mkdir(parents=True, exist_ok=True)
        receipt = {
            "status": "SHA256_MATCHED_NOT_LEAN_VERIFIED",
            "transport": "local",
            "source": source,
            "archive": str(archive),
            "scope": "Source identity only; numerical claims require Lean proofs."
        }
        (folder / "source-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        return receipt
    url = ("https://raw.githubusercontent.com/" + source["repository"] + "/" +
           source["revision"] + "/" + source["archive_path"])
    folder = cache / source["archive_sha256"]
    archive = folder / "proof.tar.xz"
    folder.mkdir(parents=True, exist_ok=True)
    if archive.exists():
        verify_archive(archive, source)
    elif offline:
        raise FileNotFoundError(f"Pinned archive is not cached: {archive}")
    else:
        temporary = None
        try:
            request = urllib.request.Request(url, headers={"User-Agent": "PolynomialRealizationsProgram-certificate-fetch"})
            with urllib.request.urlopen(request, timeout=60) as response:
                with tempfile.NamedTemporaryFile(dir=folder, prefix="download-", delete=False) as stream:
                    temporary = Path(stream.name)
                    size = 0
                    while block := response.read(CHUNK):
                        size += len(block)
                        if size > source["archive_bytes"]:
                            raise ValueError("Download exceeds pinned size")
                        stream.write(block)
            verify_archive(temporary, source)
            temporary.replace(archive)
        finally:
            if temporary is not None:
                temporary.unlink(missing_ok=True)
    receipt = {
        "status": "SHA256_MATCHED_NOT_LEAN_VERIFIED",
        "source": source,
        "url": url,
        "archive": str(archive.resolve()),
        "scope": "Source identity only; numerical claims require Lean proofs."
    }
    (folder / "source-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


def main():
    """
    Fetch the source selected on the command line and print its verified operational receipt.
    No bundled upstream program runs.
    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=ROOT / "chebyshev2/Certificates/Source.json")
    parser.add_argument("--cache", type=Path, default=ROOT / ".lake/certificates/chebyshev2")
    parser.add_argument("--offline", action="store_true", help="Check the cached archive without network access")
    args = parser.parse_args()
    try:
        receipt = fetch(load_source(args.source), args.cache, args.offline)
    except (OSError, ValueError, KeyError) as error:
        parser.exit(1, f"Certificate fetch failed: {error}\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()

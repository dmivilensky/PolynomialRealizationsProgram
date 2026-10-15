"""Fetch the paper's exact upstream archive; this does not verify its mathematics."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tempfile
import urllib.request

ROOT = Path(__file__).resolve().parent.parent
CHUNK = 1 << 20


def load_source(path):
    """
    Read and validate the source descriptor: repository/archive location, format and expected
    cryptographic identity. This is operational provenance, not a mathematical axiom.
    """
    source = json.loads(path.read_text())
    if source.get("format") != "POLYNOMIAL_REALIZATIONS_CERTIFICATE_SOURCE":
        raise ValueError("Unknown source descriptor format")
    for key, pattern in (("repository", r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+"),
                         ("revision", r"[0-9a-f]{40}"),
                         ("archive_sha256", r"[0-9a-f]{64}")):
        if not re.fullmatch(pattern, source[key]):
            raise ValueError(f"Invalid source field: {key}")
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


def fetch(source, cache, offline=False):
    """
    Reuse or download the pinned archive and verify its bytes. Offline mode permits only an
    existing verified archive; the receipt records provenance and cannot replace a Lean proof.
    """
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
    parser.add_argument("--source", type=Path, default=ROOT / "2610.05164v2/Certificates/Source.json")
    parser.add_argument("--cache", type=Path, default=ROOT / ".lake/certificates/2610.05164v2")
    parser.add_argument("--offline", action="store_true", help="Check the cached archive without network access")
    args = parser.parse_args()
    try:
        receipt = fetch(load_source(args.source), args.cache, args.offline)
    except (OSError, ValueError, KeyError) as error:
        parser.exit(1, f"Certificate fetch failed: {error}\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Package the committed CollatzEndpointTransport formal artifact."""

from __future__ import annotations

import argparse
import hashlib
import subprocess
import sys
import zipfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PUBLIC_PATHS = (
    ".gitignore",
    "CITATION.cff",
    "LICENSE",
    "README.md",
    "lean",
    "scripts",
)


class PackagingError(RuntimeError):
    """A release-packaging invariant failed."""


def run(args: list[str], *, capture: bool = False) -> str:
    completed = subprocess.run(
        args,
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.STDOUT if capture else None,
    )
    output = completed.stdout or ""
    if completed.returncode != 0:
        if output:
            print(output, file=sys.stderr, end="")
        raise PackagingError(f"command failed: {' '.join(args)}")
    return output.strip()


def digest(path: Path, algorithm: str) -> str:
    value = hashlib.new(algorithm)
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Create the journal-neutral CET software archive."
    )
    parser.add_argument("--version", required=True, help="release version, e.g. 2.0.1")
    parser.add_argument("--ref", default="HEAD", help="committed Git ref to archive")
    parser.add_argument("--output", type=Path, help="output ZIP path")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    version = args.version.removeprefix("v")
    tag_version = run(["git", "show", f"{args.ref}:CITATION.cff"], capture=True)
    if f"version: {version}" not in tag_version:
        raise PackagingError(
            f"CITATION.cff at {args.ref} does not declare version {version}"
        )

    commit = run(["git", "rev-parse", f"{args.ref}^{{commit}}"], capture=True)
    output = args.output or (
        ROOT / "dist" / f"v{version}" / f"CollatzEndpointTransport-{version}.zip"
    )
    output = output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)

    prefix = f"CollatzEndpointTransport-{version}/"
    run(
        [
            "git",
            "archive",
            "--format=zip",
            f"--prefix={prefix}",
            f"--output={output}",
            args.ref,
            "--",
            *PUBLIC_PATHS,
        ]
    )

    forbidden = ("submission/", "working/", ".lake/", "dist/")
    with zipfile.ZipFile(output) as archive:
        names = archive.namelist()
    for marker in forbidden:
        if any(marker in name for name in names):
            raise PackagingError(f"archive contains forbidden path marker: {marker}")

    print(f"commit  {commit}")
    print(f"file    {output}")
    print(f"bytes   {output.stat().st_size}")
    print(f"sha256  {digest(output, 'sha256')}")
    print(f"md5     {digest(output, 'md5')}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

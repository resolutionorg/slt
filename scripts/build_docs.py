#!/usr/bin/env python3
"""Build the API documentation site of the repository resolutionorg/slt.

Usage: scripts/build_docs.py [OUT_DIR]   (from anywhere in the package; default OUT_DIR is docbuild/site)

Builds the `docs` facet of the doc-gen4 fork pinned by `docbuild/` for `SLT`, building it first if
need be: its modules alone, with Mathlib and core references linked out to the hosted
mathlib4_docs, and the bibliography page `references.html` from `references.bib`. Source links
point at the checkout's `origin` remote at the built commit. Prerequisites and publishing:
RELEASING.md.
"""
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

ROOT_LIBS = ["SLT"]
MATHLIB_DOCS = "https://leanprover-community.github.io/mathlib4_docs/"


def run(cmd: list, cwd: str | None = None, env: dict | None = None) -> None:
    subprocess.run([str(c) for c in cmd], cwd=cwd, env=env, check=True)


def git(*args: str) -> str:
    return subprocess.run(["git", *args], capture_output=True, text=True, check=True).stdout.strip()


def fetch(url: str, timeout: int = 120) -> tuple[bytes, dict]:
    with urllib.request.urlopen(url, timeout=timeout) as resp:
        return resp.read(), dict(resp.headers)


def check_bibliography(build: Path) -> None:
    """The facet's prepass reads `references.bib` (docbuild/docs/references.bib is a symlink to it)
    and `fromDb` renders it as `references.html`,
    linking a docstring's bare `[KEY]` to its entry. The prepass's BibTeX parser accepts only keys
    of ASCII letters, digits, `:`, `_` and `-`, and silently drops the rest of the file from the
    first entry with another key, hence the count check.
    """
    entries = re.findall(r"^@\w+\{", Path("references.bib").read_text(encoding="utf-8"), re.M)
    items = json.loads((build / "doc-data" / "references.json").read_text(encoding="utf-8"))
    if len(items) != len(entries):
        sys.exit(f"doc-gen4 read {len(items)} of the {len(entries)} entries of references.bib")


def main(argv: list[str]) -> int:
    os.chdir(Path(__file__).resolve().parent.parent)
    out_dir = Path(argv[0]).resolve() if argv else Path("docbuild/site").resolve()
    sha = git("rev-parse", "HEAD")
    repo_url = git("remote", "get-url", "origin").removesuffix(".git")
    tmp = Path(tempfile.mkdtemp())

    # Mathlib's published address book, which the fork reads as it is.
    bmp, headers = fetch(f"{MATHLIB_DOCS}declarations/declaration-data.bmp")
    decl_data = tmp / "declaration-data.bmp"
    decl_data.write_bytes(bmp)

    # The site: the fork's `docs` facet of the library, from docbuild/, where Lake builds the
    # pinned fork and the library itself (Mathlib from its cache, `lake exe cache get`). It
    # ingests every module of the library in one environment load and emits them with external
    # references redirected to the hosted docs; the configuration is the environment (see RESOLUTION_FORK.md in the fork). Nothing changed since
    # the last build means nothing is rebuilt.
    build = Path("docbuild/.lake/build").resolve()
    run(["lake", "build", *(f"{lib}:docs" for lib in ROOT_LIBS)], cwd="docbuild",
        env={**os.environ,
             "DOCGEN_LOCAL_MODULE_ROOTS": ",".join(ROOT_LIBS),
             "DOCGEN_EXTERNAL_BASE": MATHLIB_DOCS,
             "DOCGEN_EXTERNAL_DECL_DATA": str(decl_data),
             # header-data.bmp can exceed hosts' per-file limits; shipped gzipped instead.
             "DOCGEN_GZIP_HEADER_DATA": "1",
             # The oleans must be in .lake/build, not only in Lake's artifact cache.
             "LAKE_RESTORE_ARTIFACTS": "true"})
    check_bibliography(build)

    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(build / "doc", out_dir)

    # Provenance marker: the commit and tool versions the site was built from.
    lean_label = ""
    try:
        index_html = fetch(f"{MATHLIB_DOCS}index.html")[0].decode(errors="replace")
        if m := re.search(r"This was built using Lean 4(.*?)</p>", index_html, re.S):
            if v := re.search(r"[0-9]\S+", re.sub(r"<[^>]+>", "", m.group(1))):
                lean_label = v.group(0)
    except OSError:
        pass
    manifest = json.loads(Path("docbuild/lake-manifest.json").read_text())
    docgen4_sha = next(p["rev"] for p in manifest["packages"]
                       if p["name"].strip("«»") == "doc-gen4")
    now = datetime.now(timezone.utc).isoformat(timespec="seconds")
    (out_dir / "build.json").write_text(json.dumps({
        "built_at": now,
        "repo_commit": sha,
        "repo_url": repo_url,
        "repo_lean": Path("lean-toolchain").read_text().strip().split(":")[-1],
        "roots": ROOT_LIBS,
        "docgen4_commit": docgen4_sha,
        "decl_data": {"etag": headers.get("ETag", ""),
                      "last_modified": headers.get("Last-Modified", ""),
                      "lean": lean_label, "fetched_at": now},
    }, indent=2) + "\n")
    # GitHub Pages: serve the tree as it is, without a Jekyll pass.
    (out_dir / ".nojekyll").touch()
    shutil.rmtree(tmp, ignore_errors=True)
    pages = sum(1 for _ in out_dir.rglob("*.html"))
    print(f"built {pages} pages @ {sha[:10]} in {out_dir}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

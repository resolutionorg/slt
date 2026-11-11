#!/usr/bin/env python3
"""Assemble the documentation site of the repository: landing page, API documentation, blueprint.

Usage: scripts/build_site.py [--out DIR] [--skip-docs] [--skip-blueprint] [--serve]
       (from anywhere in the package; DIR defaults to _site/)

The site is a static tree: index.html (site/index.html with its placeholders filled: links to the
source, the blueprint and the API documentation), docs/ (scripts/build_docs.py), blueprint/
(`lake exe vbp build`), build.json (provenance) and .nojekyll. `--skip-docs` and
`--skip-blueprint` keep what DIR already holds for that part (the CI builds the two parts in separate
jobs and assembles them here); `--serve` serves DIR afterwards at http://localhost:8000.
The repository's CI publishes the site; RELEASING.md says how.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path

REPO_URL = "https://github.com/resolutionorg/slt"
SOURCE_REF = "main"  # the public repository's branch that links point at
SITE_SRC = Path("site")
BLUEPRINT_DIR = Path("blueprint")


def run(cmd: list, cwd: str | None = None, env: dict | None = None) -> None:
    print("+", " ".join(str(c) for c in cmd), flush=True)
    subprocess.run([str(c) for c in cmd], cwd=cwd, env=env, check=True)


def git(*args: str) -> str:
    return subprocess.run(["git", *args], capture_output=True, text=True, check=True).stdout.strip()


def build_docs(out: Path) -> None:
    """The API documentation, into out/docs (scripts/build_docs.py replaces the directory)."""
    run([sys.executable, "scripts/build_docs.py", out / "docs"])


def build_blueprint(out: Path) -> None:
    """The blueprint, into out/blueprint.

    The "defined in" link of every embedded declaration is computed when the blueprint's modules
    are compiled: VersoBlueprint looks the declaration's module up on Lean's source search path,
    which is the LEAN_SRC_PATH variable, and links to it on GitHub at the checkout's commit. Lake
    gives its compile jobs only LEAN_PATH, so the variable is set here to the package root, where
    the library's sources are; without it the header falls back to the module's path as plain text.
    """
    env = {**os.environ,
           "LEAN_SRC_PATH": os.pathsep.join(
               [str(Path.cwd())] + [p for p in [os.environ.get("LEAN_SRC_PATH", "")] if p])}
    run(["lake", "build"], cwd=BLUEPRINT_DIR, env=env)
    with tempfile.TemporaryDirectory() as tmp:
        run(["lake", "exe", "vbp", "build", "--output", tmp], cwd=BLUEPRINT_DIR, env=env)
        site = Path(tmp) / "html-multi"
        if not (site / "index.html").is_file():
            sys.exit(f"blueprint build produced no {site / 'index.html'}")
        dest = out / "blueprint"
        if dest.exists():
            shutil.rmtree(dest)
        shutil.copytree(site, dest)


def landing_page(out: Path, sha: str, built_at: str) -> None:
    template = (SITE_SRC / "index.html").read_text(encoding="utf-8")
    values = {
        "REPO_URL": REPO_URL,
        "SOURCE_REF": SOURCE_REF,
        "BUILT_AT": built_at,
        "TOOLCHAIN": Path("lean-toolchain").read_text().strip(),
    }
    page = template
    for key, value in values.items():
        page = page.replace("{{" + key + "}}", value)
    if "{{" in page:
        sys.exit("site/index.html has a placeholder this script does not fill: "
                 + page[page.index("{{"):][:40])
    (out / "index.html").write_text(page, encoding="utf-8")
    for extra in SITE_SRC.iterdir():
        if extra.name != "index.html":
            shutil.copy2(extra, out / extra.name)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--out", type=Path, default=Path("_site"))
    parser.add_argument("--skip-docs", action="store_true", help="keep DIR/docs as it is")
    parser.add_argument("--skip-blueprint", action="store_true", help="keep DIR/blueprint as it is")
    parser.add_argument("--serve", action="store_true", help="serve DIR at http://localhost:8000 afterwards")
    args = parser.parse_args(argv)

    os.chdir(Path(__file__).resolve().parent.parent)
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    sha = os.environ.get("GITHUB_SHA") or git("rev-parse", "HEAD")
    built_at = datetime.now(timezone.utc).isoformat(timespec="seconds")

    if not args.skip_docs:
        build_docs(out)
    if not args.skip_blueprint:
        build_blueprint(out)
    for part in ("docs", "blueprint"):
        if not (out / part / "index.html").is_file():
            sys.exit(f"{out / part} has no index.html; build it (drop --skip-{part})")
    landing_page(out, sha, built_at)

    (out / "build.json").write_text(json.dumps({
        "built_at": built_at,
        "repo_url": REPO_URL,
        "source_ref": SOURCE_REF,
        "source_commit": sha,
        "toolchain": Path("lean-toolchain").read_text().strip(),
        "parts": {"docs": "scripts/build_docs.py", "blueprint": "blueprint/"},
    }, indent=2) + "\n")
    (out / ".nojekyll").touch()

    pages = sum(1 for _ in out.rglob("*.html"))
    size = sum(p.stat().st_size for p in out.rglob("*") if p.is_file()) / 2**20
    print(f"site: {pages} pages, {size:.0f} MB, @ {sha[:10]} in {out}")
    if args.serve:
        run([sys.executable, "-m", "http.server", "-d", out, "8000"])
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

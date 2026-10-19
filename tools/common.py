"""Shared helpers for the checkers."""
import hashlib
import pathlib
import re
import subprocess
import os

ROOT = pathlib.Path(__file__).resolve().parent.parent
MARK_BEGIN = "-- FROZEN-STATEMENT-BEGIN\n"
MARK_END = "-- FROZEN-STATEMENT-END"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def frozen_block(path: pathlib.Path) -> str:
    text = path.read_text(encoding="utf-8")
    if text.count(MARK_BEGIN) != 1 or text.count(MARK_END) != 1:
        raise ValueError(f"{path}: expected exactly one frozen block")
    return text.split(MARK_BEGIN, 1)[1].split(MARK_END, 1)[0]


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def mask_comments(text: str) -> str:
    """Blank out comments and string literals, keeping line structure."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j == -1 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth > 0:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(" " * (j + 1 - i))
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def lean_env() -> dict:
    return {**os.environ, "PATH": str(pathlib.Path.home() / ".elan/bin") + ":" + os.environ.get("PATH", "")}


def run_lean_file(source: str, timeout: int = 3600) -> subprocess.CompletedProcess:
    scratch = ROOT / "scratch"
    scratch.mkdir(exist_ok=True)
    path = scratch / "_check.lean"
    path.write_text(source)
    try:
        return subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, capture_output=True,
                              text=True, timeout=timeout, env=lean_env())
    finally:
        path.unlink(missing_ok=True)


def parse_axioms(output: str) -> dict:
    """Map each `#print axioms` declaration to its axiom list."""
    result = {}
    flat = re.sub(r"\s+", " ", output)
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", flat):
        result[m.group(1)] = {a.strip().split(".{")[0] for a in m.group(2).split(",") if a.strip()}
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", flat):
        result[m.group(1)] = set()
    return result

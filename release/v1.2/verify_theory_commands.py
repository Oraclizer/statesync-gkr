#!/usr/bin/env python3
"""Fail closed if a theory source admits, abandons or postulates a result.

The check rejects the Isabelle commands ``sorry``, ``oops``,
``axiomatization`` and ``oracle`` in every tracked ``.thy`` file under
``formal/``. Comments, cartouches and quoted inner-syntax strings are removed
before matching, so the same words may still appear in explanatory text.
"""

from __future__ import annotations

from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[2]
FORBIDDEN = re.compile(r"(?<![A-Za-z0-9_'.])(sorry|oops|axiomatization|oracle)(?![A-Za-z0-9_'])")
OPEN = "\\<open>"
CLOSE = "\\<close>"


def fail(message: str) -> None:
    raise SystemExit(f"theory-commands=FAIL: {message}")


def strip_non_commands(text: str) -> str:
    """Blank comments, cartouches and strings while keeping line breaks."""
    out: list[str] = []
    i = 0
    comment = 0
    cartouche = 0
    in_string = False
    while i < len(text):
        if comment:
            if text.startswith("(*", i):
                comment += 1
                i += 2
            elif text.startswith("*)", i):
                comment -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        if cartouche:
            if text.startswith(OPEN, i):
                cartouche += 1
                i += len(OPEN)
            elif text.startswith(CLOSE, i):
                cartouche -= 1
                i += len(CLOSE)
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        if in_string:
            if text[i] == "\\" and i + 1 < len(text):
                out.append("  ")
                i += 2
            elif text[i] == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        if text.startswith("(*", i):
            comment = 1
            i += 2
        elif text.startswith(OPEN, i):
            cartouche = 1
            i += len(OPEN)
        elif text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    if comment or cartouche or in_string:
        fail("unterminated comment, cartouche or string")
    return "".join(out)


def theory_files() -> list[Path]:
    listed = subprocess.run(
        ["git", "-C", str(ROOT), "ls-files", "-z", "--", "formal/*.thy"],
        check=True,
        capture_output=True,
    ).stdout.decode("utf-8").split("\0")
    return [ROOT / name for name in listed if name]


def main() -> None:
    files = theory_files()
    if not files:
        fail("no tracked theory sources under formal/")
    findings: list[str] = []
    for path in files:
        try:
            body = strip_non_commands(path.read_text(encoding="utf-8"))
        except SystemExit as error:
            raise SystemExit(f"{error} in {path.relative_to(ROOT).as_posix()}") from None
        for number, line in enumerate(body.splitlines(), start=1):
            match = FORBIDDEN.search(line)
            if match:
                findings.append(f"{path.relative_to(ROOT).as_posix()}:{number}: {match.group(1)}")
    if findings:
        fail("; ".join(findings))
    print(f"theory-commands=PASS theories={len(files)}")


if __name__ == "__main__":
    main()

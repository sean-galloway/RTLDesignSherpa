#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Reject attribution trailers in commit messages (GLOBAL_REQUIREMENTS 6.1).

A commit message is the change and nothing else: no Co-authored-by,
Assisted-by, Claude-Session or "Generated with" line, from any model or
harness. Rationale: vault/handbook/authoring/commit-messages.md.

    check_commit_messages.py --file .git/COMMIT_EDITMSG   # commit-msg hook
    check_commit_messages.py --range <base>..<head>       # CI, per push / PR

Exit 0 clean, 1 a trailer was found, 2 the input could not be read.
Only a line that STARTS with a trailer counts; prose that mentions one
(`Co-Authored-By:` in backticks, mid-sentence) is fine. A co-author that is a
GitHub bot (dependabot[bot]) is exempt: that line comes from GitHub's merge,
not from an author.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

RULE = "GLOBAL_REQUIREMENTS.md 6.1 / vault/handbook/authoring/commit-messages.md"

TRAILER = re.compile(
    r"^\s*(co-authored-by|assisted-by|generated-by|claude-session)\s*:",
    re.IGNORECASE,
)
# "Generated with [Claude Code]", often behind an emoji, and the older
# "Documentation and implementation support by Claude." footer. "Generated
# with" must name a link or a model/harness: body prose such as "Generated
# with --docs-only ..." describes a build step and is not attribution.
FOOTER = re.compile(
    r"^[^\w`]*(generated with\s+(\[|(claude|kimi|qwen|nemotron|codex|gemini|"
    r"chatgpt|gpt|copilot|cursor|aider)\b)"
    r"|documentation and implementation support by\b)",
    re.IGNORECASE,
)
BOT = re.compile(r"\[bot\]", re.IGNORECASE)
SCISSORS = re.compile(r"^# -+ >8 -+$")


def offending_lines(message: str) -> list[str]:
    """Return the trailer lines in a commit message, ignoring git comments."""
    found = []
    for line in message.splitlines():
        if SCISSORS.match(line):
            break  # everything below is the verbose diff, never committed
        if line.startswith("#"):
            continue
        if TRAILER.match(line) and not BOT.search(line):
            found.append(line.strip())
        elif FOOTER.match(line):
            found.append(line.strip())
    return found


def check_file(path: Path) -> int:
    try:
        message = path.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        print(f"check_commit_messages: cannot read {path}: {exc}", file=sys.stderr)
        return 2
    bad = offending_lines(message)
    if not bad:
        return 0
    print("[commit-msg] Commit REJECTED: the message carries an attribution trailer.")
    for line in bad:
        print(f"    {line}")
    print(f"  Remove the line(s) and commit again. Rule: {RULE}")
    return 1


def git(*args: str) -> str:
    return subprocess.run(["git", *args], check=True, capture_output=True,
                          text=True).stdout


def check_range(rev_range: str) -> int:
    try:
        shas = git("rev-list", "--no-merges", rev_range).split()
    except subprocess.CalledProcessError as exc:
        print(f"check_commit_messages: bad range {rev_range!r}: {exc.stderr.strip()}",
              file=sys.stderr)
        return 2
    failures = 0
    for sha in reversed(shas):
        bad = offending_lines(git("log", "-1", "--format=%B", sha))
        if bad:
            failures += 1
            subject = git("log", "-1", "--format=%s", sha).strip()
            print(f"{sha[:9]} {subject}")
            for line in bad:
                print(f"    {line}")
    print(f"check_commit_messages: {len(shas)} commit(s) in {rev_range}, "
          f"{failures} with an attribution trailer")
    if failures:
        print(f"Rule: {RULE}")
        return 1
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--file", type=Path, help="commit message file (commit-msg hook)")
    mode.add_argument("--range", dest="rev_range", help="git revision range, e.g. A..B")
    args = parser.parse_args(argv)
    if args.file is not None:
        return check_file(args.file)
    return check_range(args.rev_range)


if __name__ == "__main__":
    sys.exit(main())

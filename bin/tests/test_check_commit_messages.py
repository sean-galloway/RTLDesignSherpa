# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Teeth for bin/check_commit_messages.py.

The no-trailer rule (GLOBAL_REQUIREMENTS 6.1) was unenforced until this
checker existed; between 2026-08-31 and 2026-11-07, 451 of 2,905 commits on
main carried a trailer. These cases pin that the checker FAILS on each trailer
shape it claims to catch, PASSES on prose that merely discusses the rule, and
that --range checks only the commits it is given.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "bin" / "check_commit_messages.py"

CLEAN = "fix(mem-ctrl): pumice CAMs never merge across AXI ids\n\nBody text.\n"


def run(*args: str, cwd: Path | None = None) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, str(CHECKER), *args],
                          capture_output=True, text=True, cwd=cwd)


def check_text(tmp_path: Path, text: str) -> subprocess.CompletedProcess:
    msg = tmp_path / "COMMIT_EDITMSG"
    msg.write_text(text)
    return run("--file", str(msg))


def test_clean_message_passes(tmp_path):
    assert check_text(tmp_path, CLEAN).returncode == 0


@pytest.mark.parametrize("trailer", [
    "Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>",
    "Co-authored-by: Kimi Code <noreply@moonshot.cn>",
    "co-authored-by: someone <a@b.c>",
    "Assisted-by: Claude kimi-k3",
    "Claude-Session: https://claude.ai/code/session_x",
    "Generated-by: Qwen",
    "Generated with [Claude Code](https://claude.com/claude-code)",
    "\U0001F916 Generated with [Claude Code](https://claude.com/claude-code)",
    "Documentation and implementation support by Claude.",
])
def test_each_trailer_shape_fails(tmp_path, trailer):
    res = check_text(tmp_path, CLEAN + "\n" + trailer + "\n")
    assert res.returncode == 1, res.stdout + res.stderr
    assert "6.1" in res.stdout + res.stderr


@pytest.mark.parametrize("prose", [
    "The rule bans a `Co-Authored-By:` line in every message.",
    "No `Assisted-by:` trailer, ever.",
    "  - removed the Co-Authored-By trailer from the template",
    # Real body lines from main that begin "Generated with" but describe a
    # build step; an earlier pattern flagged all three.
    "Generated with generate_has_pdf.sh --rev 0.8 from the reconciled sources;",
    "Generated with --docs-only --no-html --no-markdown, NOT bare --regmap. The",
    "generated with 8 slots, parameterized at instantiation); VENDOR/REVISION",
])
def test_prose_about_the_rule_passes(tmp_path, prose):
    assert check_text(tmp_path, CLEAN + "\n" + prose + "\n").returncode == 0


def test_bot_coauthor_is_exempt(tmp_path):
    text = CLEAN + "\nCo-authored-by: dependabot[bot] <49699333+dependabot[bot]@users.noreply.github.com>\n"
    assert check_text(tmp_path, text).returncode == 0


def test_git_comment_lines_and_scissors_are_ignored(tmp_path):
    text = (CLEAN
            + "# Co-Authored-By: this is a git comment, never committed\n"
            + "# ------------------------ >8 ------------------------\n"
            + "diff --git a/x b/x\n+Co-Authored-By: inside the verbose diff\n")
    assert check_text(tmp_path, text).returncode == 0


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", *args], cwd=repo, check=True,
                          capture_output=True, text=True).stdout.strip()


@pytest.fixture
def repo(tmp_path):
    git(tmp_path, "init", "-q", "-b", "main")
    git(tmp_path, "config", "user.email", "t@example.com")
    git(tmp_path, "config", "user.name", "t")
    git(tmp_path, "config", "commit.gpgsign", "false")
    git(tmp_path, "commit", "-q", "--allow-empty", "-m", "base")
    return tmp_path


def commit(repo: Path, message: str) -> str:
    git(repo, "commit", "-q", "--allow-empty", "--no-verify", "-m", message)
    return git(repo, "rev-parse", "HEAD")


def test_range_fails_and_names_the_commit(repo):
    base = git(repo, "rev-parse", "HEAD")
    commit(repo, "clean one")
    bad = commit(repo, "bad one\n\nCo-Authored-By: Kimi Code <noreply@moonshot.cn>")
    res = run("--range", f"{base}..HEAD", cwd=repo)
    assert res.returncode == 1
    assert bad[:9] in res.stdout


def test_range_only_checks_the_commits_given(repo):
    commit(repo, "old bad\n\nAssisted-by: Kimi k2.5")
    start = git(repo, "rev-parse", "HEAD")
    commit(repo, "new clean")
    assert run("--range", f"{start}..HEAD", cwd=repo).returncode == 0


def test_empty_range_passes_and_says_so(repo):
    head = git(repo, "rev-parse", "HEAD")
    res = run("--range", f"{head}..{head}", cwd=repo)
    assert res.returncode == 0
    assert "0 commit" in res.stdout


def test_bad_range_is_an_error_not_a_pass(repo):
    res = run("--range", "nosuchref..HEAD", cwd=repo)
    assert res.returncode == 2

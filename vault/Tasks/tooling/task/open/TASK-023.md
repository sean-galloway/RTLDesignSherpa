# TASK-023: env_python picks the venv from where you STAND, not from where it LIVES, so it can silently activate another repo's

**Priority:** P2
**Status:** open
**Owner:** TBD
**Filed:** 2026-09-30 (found while mutation-testing the TASK-021 version guard)

`env_python` line 7 resolves its own root by asking git where the *caller* is:

    export REPO_ROOT=$(git rev-parse --show-toplevel)
    ...
    source $REPO_ROOT/venv/bin/activate

A script that locates itself by asking where you are standing will find the wrong
thing the moment you stand somewhere else. There is no check that `$REPO_ROOT` is
this repo, so the venv it activates is whichever one happens to sit at the root of
whatever tree the shell is in.

## Measured, not reasoned about

Sourcing **this repo's** `env_python` from inside the RTLDesignSherpa-DV tree:

| | resolves to |
| --- | --- |
| `CocoTBFramework.__file__` | `RTLDesignSherpa-DV/venv/.../site-packages/CocoTBFramework/__init__.py` |
| `__version__` | **0.6.1** |

versus sourcing **DV's own** `env_python` from the same directory:

| | resolves to |
| --- | --- |
| `CocoTBFramework.__file__` | `RTLDesignSherpa-DV/src/CocoTBFramework/__init__.py` |
| `__version__` | 0.6.8 |

The difference is that DV's `env_python` also sets
`PYTHONPATH="$REPO_ROOT/src:$PYTHONPATH"`, so `src/` shadows site-packages. This
repo's has no such line -- correctly, it has no `src/` -- so from the DV tree it
activates that tree's venv and then imports the **stale built snapshot** in it.

That snapshot is `cocotb-framework` 0.6.7 whose `direct_url.json` points at
`/home/seang/github/RTLDesignSherpa-DV` -- a *different checkout* from
`/mnt/data/github/...` -- and which self-reports `__version__ = "0.6.1"` (the
six-release drift [[TASK-021]] documents). So the wrong-tree import lands on a
package that is wrong about its own identity, which is the worst possible thing to
be measuring against.

## Why it is worth fixing rather than "don't do that"

**This already caused a real misdiagnosis in this repo.** 9 DV test failures were
read as a code defect and investigated as one; the cause was tests resolving
against a built snapshot instead of `src/`, which differed in 8 files. Against
`src/` the same suite was 1504 passed. The mechanism is exactly the one above.

It is silent in the direction that matters. Nothing errors, nothing warns, and the
interpreter that comes up is a real working Python with a real `CocoTBFramework`
in it -- just not the one under test. Every verdict after that point is
unattributable.

## The worktree case, which any fix has to survive

`git rev-parse --show-toplevel` also differs inside a worktree, and this repo has
two, **neither of which has a venv**:

    /mnt/data/github/RTLDesignSherpa                                    venv=yes
    /mnt/data/github/RTLDesignSherpa/.claude/worktrees/pumice-...        venv=NO
    /tmp/pumice_bisect                                                  venv=NO

Sourcing `env_python` in either makes `source $REPO_ROOT/venv/bin/activate` fail
on a missing file. Execution *continues* -- a sourced script does not stop -- so
the session proceeds on the system interpreter with none of the tooling installed.
Louder than the DV case, but the same class: it does not refuse.

So a fix must decide whether a worktree shares the main checkout's venv or
requires its own. **That is the owner's call and the reason this is filed rather
than fixed.** Silently redirecting worktree sessions to the main venv would change
behaviour for two live worktrees, and the shared-tree rule is to confirm before
editing infrastructure every peer sources.

## Proposed fix

1. Derive the root from the script's own location, not the caller's:
   `REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"`. This is the actual
   root cause -- `env_python` is sourced, so `BASH_SOURCE[0]` is `env_python`
   itself.
2. Fail loudly when the venv is absent, rather than continuing on system python:
   print what was expected and `return 1`.
3. Decide the worktree policy explicitly and encode it, with the reason in a
   comment.

## Acceptance

- Sourcing `env_python` from another repo's tree activates THIS repo's venv, or
  refuses -- it must not silently activate the other tree's.
- Sourcing it where no venv exists says so; it does not hand back system python.
- A test that fails on each of those two conditions before the fix. The bar here
  is [[TASK-021]]'s: measure that the guard executes, do not assume it.
- Worktree behaviour stated in a comment with its rationale.

## Hazards

- **Every session and every Makefile sources this file.** A mistake here breaks
  all concurrent work at once, not one area. Two suites were live when this was
  filed, which is why it was not edited on the spot.
- `env_python` is sourced, not executed, so `exit` would kill the caller's shell.
  Use `return`.

## References

- `env_python:7` and `:34` -- the resolution and the unguarded activate
- RTLDesignSherpa-DV `env_python:20,37` -- the `PYTHONPATH=src` line that makes
  that repo's own script safe
- [[TASK-021]] -- the version drift that made the stale snapshot detectable, and
  whose mutation test surfaced this

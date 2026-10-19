# TASK-017: filelist_registry reads the toml and baselines from the worktree while the hook's file set comes from the temporary index -- a peer's staged move fails everyone's commit

**Priority:** P2
**Status:** CLOSED 2026-09-28
**Owner:** TBD (tooling)
**Filed:** 2026-09-28, after it blocked every session twice in one day

## What happens

`bin/filelist_registry.py --blindspots --ratchet` runs in the pre-commit hook.
A pathspec commit (`git commit -- <paths>`) runs that hook against a
TEMPORARY index (`GIT_INDEX_FILE`) = HEAD + the named paths. The checker takes
the tracked `.f` set from that index (`git ls-files *.f`, correct) but reads
`bin/filelists.toml` and the baselines from the WORKTREE (`Path.read_text`).
So while one session has a filelist move staged with the toml edited in its
worktree, every OTHER session's commit sees the `.f` files at their HEAD
locations against a toml that no longer registers those directories:
"unregistered_filelists 0 -> N, REGRESSED", for a commit that touched nothing
of the kind. Pumice's ddr2_char move (2) and rapids' TASK-017 move (6) each
stalled the tree for 20-40 minutes on 2026-09-28; the handbook note
[[a-peers-staged-work-can-fail-your-pre-commit-gate]] records the first.

## Fix

Read every configuration input from the SAME tree as the file set. When
`GIT_INDEX_FILE` is set (hook context), `load_registry()` and the baseline
loaders should take their bytes from `git show :bin/filelists.toml` (the
index being committed), not from disk; standalone runs keep reading disk. The
same rule for `bin/filelist_placement_baseline.json`, `bin/blindspots_baseline.json`
and `bin/filelist_exempt_baseline.json`. `--placement` already classifies by
index; it has the same toml-from-disk hole for `placement_ok`.

## Done when

- [x] with a peer's filelist move staged and toml edited in the worktree, an
      unrelated pathspec commit passes the hook (reproduce with a scratch
      clone: stage a rename, edit the toml unstaged, commit another file)
- [x] the standalone `--blindspots` / `--placement` / `--check` verdicts are
      unchanged

---

## CLOSED 2026-09-28

`bin/filelist_registry.py` gained `_config_text()`: when `GIT_INDEX_FILE` is
set (hook context) the toml and the three baselines are read from the index
being committed via `git show :<path>`, falling back to disk only for a path
the index does not have; standalone runs read disk as before. All four
readers use it (`load_registry`, the exempt ratchet, the blind-spot baseline,
the placement baseline); the writers still write disk.

Reproduced in a scratch clone (a clone, not a branch of the shared tree) the
way the peers had it: an area's only `filelists/` dir renamed and staged, the
toml edited to the new dir but left unstaged, then a temporary index built
from HEAD the way `git commit -- <paths>` does:

| | old script | new script |
|---|---|---|
| under the hook's index | REGRESSED, unregistered_filelists 0 -> 11 | PASS |
| standalone in that worktree | REGRESSED (the move was incomplete -- correct) | REGRESSED (same, correct) |

So the hook now judges a commit against the tree it is committing, and a
peer's half-staged move is that peer's own standalone failure, not everyone
else's. Standalone verdicts on the real tree are unchanged: `--check`,
`--audit`, `--blindspots --ratchet` and `--placement` all PASS. CI runs on a
plain checkout (no `GIT_INDEX_FILE`) and is untouched.

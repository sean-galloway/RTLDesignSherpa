# TASK-007: .rdl edits are gated against their generated artifacts
> **Was `TASK-083` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** CLOSED 2026-09-23  **Priority:** Medium

`bin/check_rdl_regen.py` regenerates each manifest entry into a TEMPORARY
directory and diffs the result against what is committed. Wired into
`bin/hooks/pre-commit` (gated on a staged `.rdl`) and into a new `rdl-regen`
CI job.

Two things the manifest must carry because neither is derivable:

- **The invocation.** An artifact does not record the command that made it --
  stream's two regmaps carry byte-identical banners despite coming from
  different runs. One run emits one regmap, so stream needs two entries. The
  second (`--regmap-output .../rtl/stream_regmap.py`) was determined
  EMPIRICALLY, by reproducing the tracked file byte-for-byte in a scratch dir;
  guessing it would have reported permanent staleness and blocked every commit.
- **Which sources feed it.** `stream_regs.rdl` `include`s `stream_mon_regs.rdl`,
  so editing the include changes the output while the parent is never staged.

Validated in both directions rather than inspected:

| probe | result |
|---|---|
| clean tree | RC=0 |
| artifact dirtied | RC=1, names the stale file + regenerate hint |
| `--staged`, nothing staged | RC=0 (no-op) |
| **include staged, artifact dirty** | **RC=1 — selected via the include** |
| **live commit attempt** | **BLOCKED, nothing landed** |

CI needs its own job: the `filelists` job is deliberately pip-free, and the
generator imports `peakrdl_html` unconditionally even under `--no-html`, so
the step installs the versions pinned in `requirements.txt` -- a different
PeakRDL than the tree was generated with would report everything stale.

**Coverage is 1 of 7 RDL blocks** (stream). The mechanism is general; the
remaining blocks need their invocations determined the same empirical way.
Carried forward as [[TASK-006]].

---

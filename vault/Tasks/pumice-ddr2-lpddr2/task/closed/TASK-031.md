# TASK-031: ddr2_char's clean target must use the marker-aware cleaner

**Status:** CLOSED 2026-09-28  **Priority:** P2 -- this is the last raw
`rm -rf local_sim_build` in any tracked Makefile, and it is the exact mechanism
tooling BUG-005 proved deletes a build directory a peer is simulating in.
Filed from tooling BUG-005 when that global item closed (the cleaner exists and
every other clean target is on it).

## The one-line change

`projects/fpga-systems/NexysA7/mem-ctrl-ip/pumice/ddr2_char_framework/dv/tests/Makefile`,
`clean:` target: replace

    rm -rf local_sim_build logs

with

    rm -rf logs
    python3 $(REPO_ROOT)/bin/clean_sim_builds.py $(CURDIR)

`bin/clean_sim_builds.py` leaves any build directory whose `.sim_busy` marker
names a live pid (dead pid or over-age marker = reclaimable). The Makefile
already requires `REPO_ROOT` (it errors without env_python). Ready-made on
branch `tooling-pumice-halves`, commit `eeec017fb`, dry-run checked with
`make -n clean`.

Acceptance: `grep -rn 'rm -rf.*sim_build' --include=Makefile --include='*.mk'`
over `git ls-files` returns nothing under pumice paths.

---

## Closed 2026-09-28 -- landed from tooling-pumice-halves

`ddr2_char`'s `dv/tests` clean target now calls `bin/clean_sim_builds.py`
instead of a raw `rm -rf local_sim_build` -- the last one in the repo. Landed
with the rest of that branch; char-framework board gate 216 passed, 2 xfailed
against it.

> Branch `tooling-pumice-halves` was DELETED 2026-09-28 at Sean's request (never pushed; the pumice session did the work on main directly, so the branch was redundant). References to it above are historical.

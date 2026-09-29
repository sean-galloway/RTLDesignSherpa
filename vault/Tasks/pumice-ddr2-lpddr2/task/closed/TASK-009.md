# TASK-009: doc + filelist cleanup (push from workstation)
> **Was `PUMICE-CLEANUP (via PUMICE-050)` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.


**Status:** CLOSED 2026-09-26 — tb filelists moved to dv/filelists/; doc placement was already compliant
**Priority:** P2

Apply the RTL-area cleanup pattern to pumice: doc placement ([[doc-placement]])
and filelist consistency ([[filelists]] — the `dv/tb/*_tb_top.f` move into a
`filelists/` dir co-located with the testbench).

**Pushing: Sean pushes pumice from the workstation, NOT from the agent
environment (Sean, 2026-07-24).** Make and commit the pumice changes here if
working, but leave the push to Sean. Do not `git push` pumice work from this
box. (Reason per Sean — workstation is where pumice is pushed from.)

Gated behind the RTL area completing (Tasks/INDEX.md sequencing).


## 2026-09-26 — DONE. It was one `git mv` and five path strings.

Sean asked what was preventing this from closing. Nothing was, and it had been
deferred since 2026-07-24 on a gate that no longer applies.

**Filelist consistency — DONE.** The four `dv/tb/*_tb_top.f` files moved to
`dv/filelists/`, matching `ddr2_char_framework/dv/filelists` in this same area
(so the target pattern already existed here; the task's "gated behind the RTL
area" note was stale). Every line in those files is `$REPO_ROOT`-anchored, so
the move could not break a path. Five test files referenced the old location
and were updated.

  dv/filelists/pumice_core_tb_top.f
  dv/filelists/pumice_rd_return_ring_tb_top.f
  dv/filelists/pumice_top_csr_tb_top.f
  dv/filelists/pumice_top_geared_tb_top.f

**Doc placement — ALREADY COMPLIANT, nothing to do.** Checked against
[[doc-placement]]:

* `README.md` is a pointer (two links out, no duplicated content) — which is
  exactly what rule 2 requires of a project-area README.
* `PRD.md`, `CLAUDE.md`, `AT-A-GLANCE.md` are beside-code agent-facing files in
  a project dir, the home rule 4 and the "four homes" table assign them.
* The four files under `docs/` (`AXI_DRAM_GEARING_SCOPE`, `csr_obs_layout`,
  `design-requirements`, `test_patterns_strobe_race`) are component-specific
  reader-facing specs, not method — so none of them belongs in
  `vault/handbook/`.

**The push restriction is retired.** The task said "Sean pushes pumice from the
workstation, NOT from the agent environment (2026-07-24)". Superseded: Sean
directed pumice pushes from this box throughout 2026-09-25/26 and they landed
on origin/main without incident.

Gate: GATE_RC=0, 0 FAILED, 187 passed at BOTH geometries.

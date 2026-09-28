# TASK-024: greppable structure trackers (CAMs / page policy / refresh / scheduler)

> **Migrated from `PUMICE-015`** on 2026-09-27, when this area's flat
> `closed.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-015` reference resolves. Body below is verbatim from the flat page.
>
> Lane chosen by reading this item's own Status line and opening, not its title:
> a keyword pass over the 35 items misclassified 14 of them.


**Status:** DONE 2026-08-27 — the infrastructure already existed
(`dv/tbclasses/trackers/`, predating the request); this closed the gap
between it and the rearchitected RTL, added the missing structures, and
proved it live. Method note: [[structure-trackers]].

**What was wrong** (nothing had run the trackers since the rearchitecture,
so the rot was invisible):
- `page_predictor_tracker` targeted a DELETED fub (retired with
  HAPPY_HYBRID) — removed.
- `xbank_timers` / `rd_cl_aligner` / `wr_beat_sequencer` targeted RENAMED
  fubs (`pumice_bank_timers`, `pumice_dfi_rd_aligner`,
  `pumice_dfi_wr_serializer`) and read signals that no longer exist —
  retargeted (`btmr` short name; emit-stall + wd handshake taps).
- `scheduler_tracker` targeted the pre-rearchitecture FSM scheduler —
  retargeted to `pumice_cmd_arbiter` and given the Axis-1 POLICY view
  (ORDER/PREF/ROWSEL/COLSEL/PRIO/QOS/WRDRAIN emit-on-change), so a pick
  can be explained and not just observed.
- EVERY tracker hard-coded `mc_clk` while the rearchitected fubs use
  `aclk` — the first one to run killed the test with an AttributeError.
  Fixed centrally: `tracker_clock()` resolves by name, and `guard_run()`
  wraps every run() so a signal miss disables THAT tracker instead of
  failing the sim (instrumentation must never turn a green run red).
- `wire_trackers`'s hierarchy map still pointed at pre-rearchitecture
  instance paths — updated to `u_sched.u_arbiter` / `u_ifc.u_rd_cam` / etc.

**What was added:**
- `page_policy_tracker` (`pgpol`) — the Axis-2 decisions: mode changes,
  per-bank ap-mask edges, timeout-PRE requests, page hit/miss/empty, plus
  the rbl (modes 6/7) and row-pred (mode 5) verdicts read through the
  child instances.
- `cam_tracker` (`camrd` / `camwr`) — entry lifecycle
  INSERT/ISSUE|COMMIT/DRAIN|DONE, CAM-full INS_STALL, and OCC_<n>
  occupancy (the population the write watermarks and most/fewest_pending
  selects key off).
- `refresh_tracker` extended for the v3 work: pull-in CREDIT_<n>, burst
  DRAIN_ON/OFF, REFab-vs-REFpb KIND, and `rotor_advances()` — the exact
  check that catches a desynchronized REFpb rotor mirror.

**Usage:** `PUMICE_TRACKERS=1 pytest <test>` wires them in the core TB;
each writes `<sim_build>/<short>.out`. Off by default.

**Proof (clean run of test_pumice_core_rbl):** all ten trackers wrote live
logs; `pgpol` reproduced the test's arms exactly
(MODE_0 -> MODE_6 -> RBL_LOWLOC(b3) -> MODE_7 -> MODE_0), both CAMs
conserved (45 INSERT = 45 ISSUE/COMMIT = 45 retire), and sched EVT_ACT
(59) matched btmr ROW_ACTIVE_SET (59).

**Remaining (optional, not blocking):** no tracker yet for
`pumice_axi_burst_chopper` / `pumice_wr_splitter` (front-end burst
framing) or the DFI CDC; add them if a front-end bug ever needs the same
cross-structure view.

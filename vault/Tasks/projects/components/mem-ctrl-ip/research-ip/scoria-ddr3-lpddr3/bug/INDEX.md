<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# scoria-ddr3-lpddr3 — bugs

**Next ID: BUG-004** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

Lane created 2026-10-01, when the first composed test found the first
composition defect. Until then every scoria test was a FUB test with mocked
neighbours, and this lane had nothing to carry.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

The count EXCLUDES the reserved `BUG-000` template -- measured against
bin/check_task_ids.py, which rejected a table that counted it.

## Open

(none)

## Closed

- **BUG-003** — `scoria_top` misses the 100 MHz design point by ~2 ns in
  out-of-context place-and-route (WNS -2.022, fmax 83.2 MHz), and it is NOT the
  BUG-001/BUG-002 fixes: pre-fix measures -1.850, so those gates cost 0.172 ns
  on a design already 1.85 ns short. The worst path is the arbiter's pick cone,
  85% route over 31 logic levels, which points at floorplanning. First time
  scoria has been synthesised. **CLOSED 2026-10-10** — owner: 100 MHz was never
  the target, so the premise is invalid and the bug closes under the
  "design point is restated" arm of its own Done-when. Measurements retained as
  the design's first timing characterization; HAS/MAS restatement of the clock
  target lands with TASK-008.

- **BUG-001** — the arbiter issues two ACTs to different banks one cycle apart,
  violating tRRD, and its own final safety gate approves them. Reproduced in
  SIMULATION on 3/3 seeds in ~30 s, measured at the arbiter's own output.
  Same mechanism as pumice BUG-021, which records "not observed in sim".
  **FIXED functionally** the same day (rank-global windows added to
  `w_out_safe`'s ACT arm; checker clean 3/3, arbiter-side tight pairs gone).
  Held open for one gate only: no scoria FPGA build exists to time the change
  on, so the timing claim cannot be made yet.

- **BUG-002** — a command picked in the ZQCS's own fire cycle fires inside the
  tZQCS window, which JESD79-3F 3.10 forbids: the window counter loads on the
  accepted fire, so the pick cone's block is one cycle late and `w_out_safe`
  did not re-validate it. BUG-001's shape on a different window, and found by
  the formal proof written for BUG-001. **FIXED** (one AND term on each of the
  fire gate and `w_ref_safe`; the proof passes at depth 30). Formal-only:
  simulation reproduced it in 0 of 10 alignments. Held open on timing, the same
  gate as BUG-001.

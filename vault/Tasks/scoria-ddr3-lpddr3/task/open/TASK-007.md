# TASK-007: four runtime assertions sit in functional scoria RTL

The repo's standing rule is that RTL carries NO assertions -- they break some
tools, and properties belong in external `formal/` blocks. scoria has 18
`assert` statements across 7 files. Classified, most are fine and **four are
not**:

| Kind | Count | Where | Verdict |
|---|---|---|---|
| `initial assert` parameter guards | 5 | `scoria_axi_burst_chopper` (1), `scoria_top_geared` (1), `scoria_dfi_cmd_path` (3) | KEEP -- elaboration-time geometry checks, not runtime properties, and they catch a bad parameterisation before it simulates |
| dedicated checker module | 9 | `scoria_cmd_history_checker` | KEEP -- the module IS a scoreboard, gated behind `CMD_HISTORY_EN`, and the DV suites arm it deliberately |
| **runtime `always @(posedge)` assertions inside functional RTL** | **4** | `scoria_rd_cmd_cam` (1), `scoria_rd_return_ring` (2), `scoria_dfi_rd_aligner` (1) | **REMOVE** -- this is exactly what the rule prohibits |

**Priority:** P3. Nothing misbehaves; they are inside `ifndef SYNTHESIS` so
they never reach synthesis. The cost is that the rule is not actually true of
this area, and a rule with exceptions nobody has written down is the one the
next session breaks.
**Status:** OPEN. Found 2026-10-01 while opening `formal/scoria` -- which is
also what makes it actionable, because three of the four now have a proof to
move to.

## Three of the four are already proved externally

Inherited from pumice, and `formal/scoria` now holds the same obligations as
real properties over a free environment, which is strictly stronger than an
assertion that only fires on stimulus a test happened to generate:

| inline assertion | now proved by |
|---|---|
| `scoria_rd_return_ring`: `!(dfi_ret_valid_i && !w_iq_rd_valid)` | `a_no_fabrication` |
| `scoria_rd_return_ring`: `!(issue_valid_i && w_empty)` | `a_no_free_empty`, `a_ready_is_notfull` |
| `scoria_rd_cmd_cam`: `!(w_issue_fire && !r_valid[issue_slot_i])` | `a_ticket_integrity`, `a_ins_ready_is_free` |

All three proofs are mutation-verified against scoria's own RTL (a planted
defect makes each FAIL), so moving the obligation out of the RTL loses nothing.

## The fourth has no replacement yet

`scoria_dfi_rd_aligner`: `!(rd_valid_o && !rd_ready_i)` -- the read-return
stream has no backpressure, so a valid with ready low means a dropped word.
There is no `formal/scoria/dfi_rd_aligner` block. Either write one (the
aligner is small, and its credit/window logic already produced one escape in
the mutation runs that needed a masking gate removed to see) or keep this one
assertion and record it as the single documented exception.

## Done when

The three replaced assertions are deleted, and the fourth is either proved in a
new `formal/scoria/dfi_rd_aligner` block or recorded as a stated exception in
the RTL header AND in the handbook note that carries the rule
(`vault/handbook/design/no-assertions-in-rtl.md`), so the next sweep does not
re-open it.

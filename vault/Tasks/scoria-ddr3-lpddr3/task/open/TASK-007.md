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
**Status:** OPEN, BLOCKED ON A DECISION (see the two options below). Found
2026-10-01 while opening `formal/scoria`. The first version of this task
proposed deleting three of the four as already-proved; that was wrong and is
corrected below -- they are input contracts, the proofs ASSUME them, and
deleting them reduces checking.

## CORRECTION: they are INPUT CONTRACTS, and the first version of this task
## had the mapping wrong

The first version of this file claimed three of the four were "already proved
externally" and tabled them against `a_no_fabrication`, `a_no_free_empty`,
`a_ticket_integrity` and `a_ins_ready_is_free`. **That mapping is wrong.**
Checked against the wrappers:

| inline assertion | the property I claimed | what that property actually says |
|---|---|---|
| `rd_cmd_cam`: `!(w_issue_fire && !r_valid[issue_slot_i])` | `a_ins_ready_is_free` | about INSERT readiness, not issue |
| `rd_return_ring`: `!(dfi_ret_valid_i && !w_iq_rd_valid)` | `a_no_fabrication` | drained bursts <= RETURNED bursts, a different quantity |
| `rd_return_ring`: `!(issue_valid_i && w_empty)` | `a_no_free_empty` | FREE on empty, not ISSUE on empty |

Worse for the original plan: the obligations appear in the proofs as
**`assume`**, not `assert`. `formal_scoria_rd_cmd_cam.sv:154` is literally
`assume (!issue_valid_i || sch_valid_o[issue_slot_i])`, and the rd_return_ring
wrapper states the reason in its header:

> THE RTL's OWN TWO ASSERTIONS ARE ENVIRONMENT CONTRACTS, NOT DUT CHECKS.
> Both constrain the block's INPUTS. They were never testing this module; they
> were testing whoever drives it. They appear below as `assume`, which is what
> they always were.

That analysis is correct, and it settles what these four things are: they are
**checks on the block's inputs**, i.e. on whoever drives it, not properties of
the block. A proof cannot "replace" them -- it takes them as given.

## Which means deleting them REDUCES checking

`scoria_rd_cmd_cam`, `scoria_rd_return_ring`, `scoria_wr_data_cam` and
`scoria_dfi_cdc` have **no dedicated DV suites** -- they are covered by
`test_scoria_pumice_logic_parity.py` (logic identical to pumice, which has its
own tests) plus the new proofs. So if these assertions come out of the RTL, the
input contract is checked:

- in formal, only as an `assume` (taken as true, not verified)
- in scoria's own simulation, nowhere directly -- only indirectly, by the macro
  and top tiers corrupting data if a driver broke the contract

Deleting them is therefore not a neutral tidy-up. That is a real reduction, and
it is why this task should NOT be actioned as first written.

## The decision is the owner's, and it is one of two

**(a) Keep them, recorded as a stated exception.** The harm the standing rule
names -- "they break some tools" -- is already mitigated: all four sit inside
`ifndef SYNTHESIS`, so no synthesis or lint flow sees them. The exception class
would be "input-contract checks, guarded from synthesis, whose canonical
statement is the corresponding `assume` in formal/". Cheapest, loses nothing.

**(b) Move the check to the driver.** The contract belongs to whoever issues,
so the honest home is a DV scoreboard on the composition (the macro tier drives
the real scheduler into the real CAMs) or a dedicated unit suite for each of
the four blocks. More work, and it puts the check where the rule wants it.

Not taken unilaterally because (a) amends a standing repo rule, which is
Sean's call, and (b) is a decision about where scoria's DV effort goes next.

What HAS been done meanwhile: each of the four sites now carries a comment
saying it is an input contract rather than a DUT property, and naming the
formal `assume` that states it canonically -- so the next reader does not
re-derive this analysis.

## Done when

Sean picks (a) or (b) above. If (a): the exception class goes in
`vault/handbook/design/no-assertions-in-rtl.md` so the next sweep does not
re-open it, and this closes. If (b): the four checks move to DV and the RTL
blocks lose them.

The `scoria_dfi_rd_aligner` assertion (`!(rd_valid_o && !rd_ready_i)`) is the
one genuine DUT property of the four -- the read-return stream has no
backpressure, so a valid with ready low is a DROPPED WORD, which is about the
aligner and not its driver. It has no proof: there is no
`formal/scoria/dfi_rd_aligner` block. Writing one is worthwhile independent of
this decision.

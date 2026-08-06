<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# common — Open (accepted, not started)

---

## COMMON-010 — Every module MUST have a filelist and a registry entry
**Status:** open 2026-07-23

**The rule** (authority: [[filelists]]): every module in `rtl/common/` has a
filelist in `rtl/common/filelists/`, and the area is registered in
`bin/filelists.toml`. A new module lands with its `.f` **in the same commit** —
not "before the test lands". A module with no filelist has no consumers and is
indistinguishable from dead code the next time someone audits.

**Current state is good but unenforced.** `bin/filelist_registry.py --check`
reports common at 57 modules / 55 covered / 0 uncovered. The 2-module gap is
the `[exempt]` ledger, not a hole:

- `fifo_sync_multi` — multi-instance wrapper; no consumer yet
- `fifo_sync_multi_sigmap` — multi-instance wrapper; no consumer yet

**Work:**
1. Resolve the two exemptions: give each a filelist and a consumer, or drop the
   module. "No consumer yet" is a debt entry, not a permanent state.
2. Wire `--check` into a gate. **Nothing runs it today** — not the pre-commit
   hook, not CI (the only workflow is `track-clones.yml`), not a Makefile
   target. A MUST that nothing enforces is a wish. Shared with AMBA TASK-026;
   do the gate once for both.
3. When reading `--check` output, read all three numbers. It prints `PASS` when
   `declared - covered - exempt` is empty, so "55 covered" alongside "0
   uncovered" on a 57-module area is expected and still worth checking.


## COMMON-019 — ACK-mode arbiter compliance: the model loses a grant
**Status:** open 2026-08-05 — split out of COMMON-016/017. Not asserted on.
**Priority:** P2 — belongs to the DV framework repo (RTLDesignSherpa-DV)
**Upstream:** [RTLDesignSherpa-DV#50](https://github.com/sean-galloway/RTLDesignSherpa-DV/issues/50)
— full write-up and suggested fix also in that repo's
`docs/internal/arbiter-ack-mode-compliance.md`. The fix lands there, not here;
this entry tracks the local consequence (ACK mode logs its verdict instead of
asserting on it).

Two residuals in `ArbiterCompliance`'s ACK path (`WAIT_GNT_ACK=1` only; the
no-ACK path is clean and fully asserted on).

**1. round_robin_violation, ~3 runs in 8** on `arbiter_round_robin[4-1]` at
gate. The `r_last_valid` mirror from COMMON-017 is applied on this path too,
which helped but did not close it. Every surviving violation has the same
shape -- the RTL granted one client *further along* than the model expected:

    expected 0, got 1: requests=0x3, mask=0x0,  last_winner_at_grant=3
    expected 1, got 2: requests=0x7, mask=0xe,  last_winner_at_grant=0

In both the RTL behaves as if its last winner were one grant ahead of the
model's, i.e. the model missed a grant rather than the arbiter misrotating.
Prime suspect is `is_new_grant` in `_check_round_robin_compliance_ack_mode`:
it is derived from `pending_acks`, so a grant to a client that still owes an
ACK is skipped entirely -- no check, no mask update.

**2. unexpected_ack in the single-client saturation phase**, ~115-150 per run,
on `c08_w1` and `c16_w1` at full only. Every one lands in that phase, where one
client is granted repeatedly: more ACK edges are seen than grants are
registered. `_process_ack_mode_grants` reports a `new_grant` on the rising edge
and `grant_continuation` thereafter, and only the former registers a pending
ACK. Warning severity, so nothing fails on it.

**Work:**
1. Make the ACK path register every grant it is handed (or make `is_new_grant`
   read the transaction's own `transaction_type` instead of re-deriving it from
   `pending_acks`), then re-measure over >=8 runs of `[4-1]`.
2. Reconcile grant/ACK counting for held grants so saturation stops producing
   `unexpected_ack`.
3. When both are clean, drop the `WAIT_GNT_ACK == 1` early return in
   `arbiter_round_robin_tb.check_monitor_errors()` so ACK mode asserts like
   no-ACK does.

**Do not** re-add a blanket exclusion to make this quiet: the ACK verdict is
logged at WARNING with full details on every run, which is what made the shape
above visible in the first place.

---

## COMMON-003 — Create integration examples
**Status:** open — not started (migrated from rtl/common/TASKS.md, P2)

Standalone integration examples showing common usage patterns that combine
multiple common modules. Location: `rtl/integ_amba/examples/`.

Proposed:
- Example 1: state machine with timeout (counter + FSM)
- Example 2: multi-master system (arbiter + counters)
- Example 3: CRC-checked packet buffer (CRC + FIFO)
- Example 4: CDC data transfer (sync + handshake + FIFO)
- Example 5: simple PWM generator (counter + comparator)

Deliverables: 5 standalone designs, a test for each, documentation explaining
the design choices, and a README index. Success = all compile cleanly, all
tests pass, docs complete.


## COMMON-006 — Configurable-width adders/multipliers
**Status:** open — deferred pending user feedback, P3

Complex adders/multipliers are generated by Python in `bin/rtl_generators/`.
Parameterized SystemVerilog versions in the library were considered. Current
generation works well and parameterized versions may synthesise less optimally;
this is an educational-value vs practicality trade-off. Kept as open rather
than dropped because the decision was "not now", not "no".

## COMMON-007 — Additional arbiter types
**Status:** open — deferred pending user requests, P3

Token bucket, deficit round-robin, hierarchical arbitration. Current arbiters
cover ~95% of use cases and complex arbiters tend to be application-specific.

## COMMON-008 — Multi-byte CRC support
**Status:** open — deferred pending performance requirements, P3

`dataint_crc.sv` processes one byte per cycle. A 2/4/8/16-byte-per-cycle option
would serve high-throughput consumers, at an area cost.

## COMMON-009 — BCH and Reed-Solomon ECC
**Status:** open — deferred, P3. **Re-check before starting.**

Library ECC is Hamming SECDED only; BCH and Reed-Solomon were deferred as niche
(NAND flash, deep-space comms). A `projects/components/bch/` component once
existed as a docs-only placeholder (PRD/README/TASKS, no RTL and no tests) and
was **deleted 2026-07-23**, so this task is NOT superseded — it is the only
place BCH is tracked.

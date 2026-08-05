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


## COMMON-018 — simple arbiter "violations" are a monitor sampling bug
**Status:** open 2026-08-04 — **ROOT CAUSED. RTL is correct; the fix is in the
DV framework.** Not asserted on locally; logged as unexplained-by-design.
**Priority:** P2 (framework repo)

`arbiter_monitor.py:796` feeds the compliance check the WRONG request vector:

    self.compliance.queue_transaction(
        transaction,
        active_requests=signal_state.prev_req_vector,   # <-- previous cycle
        ...)

while the struct's own comment (line 33) defines `req_vector` as "Request
vector from clients (current at time of grant)". So the checker compares THIS
cycle's grant against LAST cycle's requests.

**Why that is fatal for this DUT and not for its sibling.**
`arbiter_round_robin_simple` drives `grant` combinationally --
`rotate(lowest_set(rotate(request)))` -- so the grant is a SUBSET of the
current request vector by construction. Pair it with the previous vector and
any change in requests between cycles produces a "violation".
`arbiter_round_robin` registers its grant, so `prev_req_vector` is the vector
that produced it and the check mostly lines up -- which is why that TB reports
only the block_arb issue (COMMON-017) and this one reported 144-176.

**The evidence that settles it.** Dumping the model state at each violation:

    t=25885 req=0x8 (only client 3) expected=3 actual=2
    t=25895 req=0x4 (only client 2) expected=2 actual=3
    t=25915 req=0x2 (only client 1) expected=1 actual=2
    t=25945 req=0x1 (only client 0) expected=0 actual=2

In every case the granted client is **not in the recorded request vector at
all**. This RTL cannot grant a non-requesting client -- grant is a subset of
request by construction -- so the pairing is what is wrong, not the arbitration.
Nothing about masking-versus-rotation is involved; that earlier hypothesis was
wrong.

**Fix (DV framework):** pass `signal_state.req_vector` for a combinational-grant
arbiter. Since both kinds share this monitor, the honest fix is to make the
vector choice explicit -- the monitor already knows `ack_mode`, and a
`registered_grant` flag would let it pick -- rather than hardcoding `prev_`.

**Local state:** the simple TB reads the compliance verdict (COMMON-016) and
logs `round_robin_violation` without asserting on it, with a pointer here. Do
not promote it to an assertion until the framework is fixed, and do not widen
the exclusion to other error types.


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


## COMMON-017 — the arbiter compliance model does not model block_arb
**Status:** open 2026-08-01 — **SETTLED: model defect, not an RTL defect.** Suite green.
**Priority:** P2 — belongs to the DV framework repo, not this one

    ArbiterCompliance(RR_Monitor_compliance): Round-robin violation:
    Expected client 17, got 3 @ 25065.0ns

Surfaced the moment `check_monitor_errors()` started asserting on the
compliance verdict (COMMON-016). Reproducible under every seed tried and
**always at the same timestamp**, which is what gave it away: a traffic-
dependent fairness bug does not land on the same nanosecond each run.

**Traced, not guessed.** Probing the arbiter every cycle across 24900-25200 ns
with SEED=1, CLIENTS=32, WAIT_GNT_ACK=0:

    25000-25050  block=1  gv=0  last_grant=0x00000000
    25060        block=0  gv=0
    25070        block=0  gv=1  gid=0   <- first grant after the block
    25080        block=0  gv=1  gid=3   last_grant=0x00000001

The violation is the first grant after `block_arb` releases, and the RTL
restarts the rotation at client 0.

**Why the RTL is right.** `r_last_valid <= grant_valid` every cycle, and
`w_req_post = block_arb ? '0 : request` means no grants while blocked, so
`r_last_valid` falls to 0 during the block. The mask then takes its third
branch:

    assign w_curr_mask_decode = grant_valid   ? w_win_mask_decode[grant_id]  :
                                r_last_valid  ? w_win_mask_decode[r_last_grant_id]
                                              : CLIENTS'(1);

`CLIENTS'(1)` masks everything except client 0, so the first post-block grant
goes to the lowest requester. Self-consistent and deliberate.

**Why the model is wrong.** `RoundRobinMaskState` (DV repo,
`components/shared/arbiter_compliance.py`) clears its mask ONLY in `reset()`.
Nothing clears it when `block_arb` gates the requests, so it retains
`mask_valid=True` and its pre-block `last_winner` and expects the rotation to
continue from there -- hence "expected 17".

**Fix belongs in the DV framework** (read-only from here): `RoundRobinMaskState`
needs to drop `mask_valid` when a blocked interval produces no grants, the same
way the RTL's `r_last_valid` does. Until then
`arbiter_round_robin_tb.check_monitor_errors()` excludes exactly this one error
type, by name, with the reasoning inline. **Every other compliance error still
fails the test** -- do not widen that exclusion.

**Doc gap found on the way (fix in rtl-common):** `arbiter_round_robin.md` says
`block_arb` "blocks all arbitration (forces no grants)" and that requests are
masked to zero. It does not say that a blocked interval RESETS THE ROTATION, so
the next grant after release goes to the lowest requester rather than the
client that was next in line. A reader relying on round-robin fairness across
a blocked period would not expect that.

## COMMON-016 — arbiter ACK mode: 105 unexpected ACKs, and the compliance model was muted
**Status:** open 2026-07-31 — surfaced by test-audit round_1 triage, P2
**Owner:** TBD

Three connected things, found while making `test_walking_requests` capable of
failing.

**1. The compliance model was consumed only to silence it.** The framework
ships `ArbiterCompliance` (`components/shared/arbiter_compliance.py`), which
tracks round-robin mask state and computes `get_expected_winner()` per grant.
`arbiter_round_robin_tb.py` referenced it in exactly one place —

    if hasattr(self.monitor, 'compliance'):
        self.monitor.compliance.ack_timeout_cycles = 8000  # Increased from 1000

— raising its timeout so it would complain less, and never once read
`get_warning_summary()` or `get_comprehensive_analysis()`. Every violation it
found was logged at WARNING and dropped. `check_monitor_errors()` now asserts
on `total_errors`, and the simple TB does not wire compliance in at all (open).

**2. Reading it immediately produced a real number.** With the verdict logged:

| config | errors | warnings |
|---|---|---|
| `WAIT_GNT_ACK=0` | 0 | 0 |
| `WAIT_GNT_ACK=1` | 0 | **105 `unexpected_ack`** |

105 acks arriving with no pending grant, in one gate-level run. Classified as
warnings so the new assertion (errors only) stays green — deliberately, until
someone decides whether the BFM's auto-ack flow or the RTL's ack handling is
wrong. **Do not reclassify these to errors before diagnosing them**; that just
turns the suite red without adding information.

**3. It probably explains the unfailable walking phase.** `manual_request()`
computes `grant_received` and DISCARDS it (logs at debug, returns None), so a
TB cannot learn whether the request it just drove was granted —
`check_manual_request_success()` only samples the grant signal *after*
`manual_request` has deasserted, which is always too late. The available proxy
is the monitor's `arbiter_stats['grants_per_client']`, and that works: in
no-ACK mode it moves exactly +1 per client (simple TB, 5 runs clean, now
asserted per client). In ACK mode it does not move reliably — which is what
105 unpaired acks would do to transaction counting. So the per-client assertion
is scoped to no-ACK mode and ACK mode warns, with the reasoning in the code.

**What would close this:** have `manual_request()` return `grant_received` (a
framework change in the DV repo, not this one), diagnose the unexpected acks,
then assert per client in both modes and drop the scoping.

**Diagnosed 2026-08-04 — it is the MODEL, and the fix is in the framework.**
The 105 (110-166 depending on seed) `unexpected_ack` warnings all land inside
the fairness phase -- the first phase where several clients ack concurrently --
and never in the single-client walking phase. Distinct timestamps, no two at the
same instant, all four clients.

The mechanism is in `process_ack_received`:

    for i in range(self.clients):
        if ack_vector & (1 << i):        # the WHOLE current vector
            matching = [t for t, c in self.pending_acks.items() if c == i]
            if not matching: warn('unexpected_ack')

`ack_detected` fires on any CHANGE of the ack vector
(`ack_vec != prev and ack_vec != 0`), and the handler then iterates every set
bit of the current vector. When client B's ack asserts while client A's is
still held, that edge re-presents A's already-retired bit and A is reported as
an unexpected ack. The BFM is behaving correctly: `_generate_ack` holds each
ack for its `ack_duration` cycles.

**Fix (DV framework repo, read-only from here):** process only newly-asserted
bits -- `new_acks = ack_vector & ~prev_ack_vector` -- rather than the whole
vector. `prev_ack_vector` is already carried in the monitor's signal state.

Local part done: the simple TB now reads the compliance verdict too (it
previously ignored it entirely), which immediately surfaced COMMON-018.



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

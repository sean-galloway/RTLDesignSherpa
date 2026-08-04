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


## COMMON-018 — simple arbiter: ~176 round-robin violations the model cannot explain
**Status:** open 2026-08-04 — surfaced by wiring the compliance verdict into the
simple TB (COMMON-016). NOT asserted on; logged loudly instead.
**Priority:** P2

`arbiter_round_robin_simple` has **no `block_arb` input**, so COMMON-017's
explanation (the model keeping its mask across a blocked interval) cannot
apply. Wiring `check_monitor_errors()` to read the verdict for the first time
reports **144-176 `round_robin_violation` errors per gate run** on a DUT that
simultaneously:

- passes its starvation check (every enabled client granted at least once),
- reports a fairness index above the 0.7 bar,
- passes every functional assertion in the suite.

So the model and the RTL disagree about grant ORDER while the RTL is
demonstrably fair. One of them is wrong about the algorithm and it is not
obvious which.

The candidate: the RTL **rotates** -- `w_shift_amount = last_grant + 1 (mod N)`,
rotating the request window so agent last_grant+1 lands at bit 0 -- while
`RoundRobinMaskState` **masks**, `mask = ~((1 << (winner+1)) - 1)` with an
unmasked fallback. Those two formulations are usually equivalent, which is
exactly why a systematic disagreement needs explaining rather than suppressing.

**Settle it** by dumping, for a handful of violations: the request vector,
`r_last_grant`, the model's `current_mask`/`last_winner`, the expected winner
and the actual grant. One timestamp is probably enough to tell whether the
model or the RTL has the wrong next-agent.

**Do not** promote this to an assertion until it is understood, and do not
widen the exclusion to hide other error types with it -- consuming a checker
only to silence it is what COMMON-016 was about.

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

## COMMON-014 — fifo_control default parameters contradict its own constraint
**Status:** open 2026-07-31 — surfaced by qc round_2 (common part_03), P3 latent

`rtl/common/fifo_control.sv` declares `ADDR_WIDTH = 3` and `DEPTH = 16` as
defaults, while its own header states "DEPTH must equal 2^ADDR_WIDTH (power of
2 depths only)". 2^3 = 8, so the defaults violate the documented contract:

- pointers are 4 bits, addressing 8 slots;
- `(AW+1)'(D)` = `4'(16)` = 0 — the exact truncation the module's comments warn
  about;
- `AFT = DEPTH - ALMOST_WR_MARGIN = 15` is unreachable at max occupancy 8, so
  `wr_almost_full` can never assert.

Latent, not live: both parents override consistently (`fifo_sync` passes
`AW = $clog2(DEPTH)`, and `rtl/cdc/fifo_async` likewise). A standalone
default instantiation silently degrades to depth-8 with dead almost-full logic.

Second, smaller point from the same finding: the header constraint is stricter
than the logic. Via `counter_bin`'s MAX wrap the control equations hold for any
`DEPTH <= 2^ADDR_WIDTH`, which is how `fifo_sync` supports non-power-of-2
depths — so the constraint text overstates the restriction it needs.

Decide: make the defaults self-consistent (e.g. `DEPTH = 8`, or derive
`ADDR_WIDTH = $clog2(DEPTH)`), and relax the header constraint to
`DEPTH <= 2^ADDR_WIDTH`. Owner call — changing a default is visible to any
direct instantiator.

## COMMON-015 — shifter_beat_pack: runtime cfg wider than COUNT_BITS corrupts occupancy
**Status:** open 2026-07-31 — surfaced by qc round_2 (common part_04), P3 misuse corner

`rtl/common/shifter_beat_pack.sv` casts the runtime beat width down to the
occupancy width in two places:

    assign pop_valid = (r_count >= COUNT_BITS'(w_beat_bits)) && (r_count != '0);
    v_count = v_count - COUNT_BITS'(w_beat_bits);

`w_beat_bits` is `BEAT_BITS_W` (CFG_BITS+4) bits; `COUNT_BITS` is
`$clog2(STORAGE_BITS+1)`. At the defaults (STORAGE_BITS=256, COUNT_BITS=9,
CFG_BITS=8) a runtime `cfg_beat_bytes_m1 >= 63` encodes a beat >= 512 bits,
which truncates to **0**: `pop_valid` degenerates to `(r_count != 0)`, the pop
shifts `v_data >> 512` (zeroing the data) and subtracts 0 from the count, so
the packer asserts `pop_valid` forever against corrupted accounting. Values
between `STORAGE_BITS` and `2^COUNT_BITS - 1` (e.g. a 264-bit beat) instead
stall `pop_valid` permanently.

The elaboration guard only checks the STATIC `MAX_BEAT_BITS < STORAGE_BITS`;
nothing checks the runtime value. Misuse-only — the docs do tell callers that
any runtime beat width must fit the storage — but the failure mode is silent
data corruption rather than a clean stall, so a saturating compare or a runtime
assertion is worth the gate.

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

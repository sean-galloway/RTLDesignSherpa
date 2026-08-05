<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# common — Closed (done)

---


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

**CLOSED 2026-08-04.** The occupancy comparison happens in the wider of the
two domains now, so an over-wide runtime cfg_beat_bytes_m1 produces a clean
stall instead of silent data corruption. The subtraction keeps its cast and is
safe by construction: a pop only fires when the wide compare passed, so
w_beat_bits <= r_count <= 2**COUNT_BITS-1 and the cast is exact. Verified:
lint passes, shifter_beat_pack 3/12/165 at gate/func/full.

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

**CLOSED 2026-08-04.** DEPTH now defaults to 8 against ADDR_WIDTH 3, so the
module's shipped defaults satisfy its own rule. The header constraint is
corrected in all three places it appeared: the real rule is
`DEPTH <= 2^ADDR_WIDTH` and DEPTH need not be a power of two, because the
pointer arithmetic wraps via counter_bin's MAX -- which is exactly how
fifo_sync supports non-power-of-2 depths. Verified: lint passes, fifo_buffer
and integ_common green, common gate 75 / func 208.

## COMMON-011 — ISSUE-001: counter.sv tick not gated during reset
**Status:** CLOSED 2026-08-04 — **not an RTL bug. Test sampling artifact.**
The disabled edge-case test is re-enabled and passing; no RTL change was kept.

The claim was that `assign tick = (r_count == MAX)` lets `tick` assert while
the module is held in reset, and the edge-case test in `counter_tb.py` had been
disabled with `if False:` since 2025 waiting on an RTL fix.

**What actually happened.** Enabling the test reproduced "Tick occurred during
reset" -- 4 failures -- which looked like confirmation. It was not. The block
sampled with a bare `await RisingEdge(self.clk)` and read `tick` immediately,
inside the window where the NBA update has not landed, so it read the PRE-EDGE
value and reported a tick that was already gone. The framework's `wait_clocks`
always delays past the edge before returning (Sean: never sample within 200ps
of an edge); the check now uses it and passes.

**Two fixes were tried and both discarded:**

1. `assign tick = RST_ASSERTED(rst_n) ? 1'b0 : (r_count == MAX)` -- rejected
   on sight and rightly: it puts an asynchronous reset into the datapath, so a
   glitch on the reset tree reaches `tick` directly, and it creates a
   reset-to-output combinational path the module does not otherwise have.
2. Registering `tick` inside the `ALWAYS_FF_RST` block, computed one cycle
   early so the timing did not move. Sound RTL, and it fixes nothing:
   - **sync reset** (the counter test's build): nothing can clear `tick`
     before the clock edge, so registered and combinational behave
     identically. Measured -- the registered version failed the same
     pre-edge-sampling check, 4 failures.
   - **async reset** (`+define+USE_ASYNC_RESET`): `r_count` clears
     asynchronously, so the ORIGINAL combinational `tick` clears with it.
     Measured -- FULL passes, 12 tests, with the unmodified RTL.

So the behaviour is correct in both reset modes and the module is unchanged.

**What was actually wrong** was the test, twice over: it sampled in the
forbidden window, and it was then disabled for three years on the strength of
that reading -- so the one check covering this path never ran. It is enabled
now, sampling through `wait_clocks`, and green at gate/func/full.

Lesson worth carrying: a failing test is not proof of an RTL defect until you
know it sampled legally. Both readings here -- the original failure and my
"confirmation" of it -- came from the same illegal sample.


## COMMON-013 — RTL fixes surfaced by Kimi round_2 common review
**Status:** closed 2026-07-23 — three behavioral/robustness RTL fixes + stale
comment corrections, each verified with a clean-rebuild test. P2.

Doc review of `rtl/common/` (round_2 common_part_02/04/05) surfaced RTL defects,
not just doc drift. Triaged and fixed the RTL side:

1. **clock_pulse.sv** — `r_counter` was declared `[WIDTH-1:0]`, but WIDTH is the
   pulse PERIOD, so the counter was as wide as the period. The doc's own 1 Hz
   heartbeat example (WIDTH=100_000_000) would infer ~100 M flip-flops and not
   synthesize. Re-sized to `$clog2(WIDTH)` (guarded for WIDTH<2). Behaviour
   unchanged; `test_clock_pulse` passes on a clean build. Fixing the RTL also
   made the doc's resource table (written for the $clog2 sizing) correct.
2. **clock_gate_ctrl.sv** — the ANSI port list used `[N-1:0]` while `N` is a
   body localparam declared after the port list (forward reference; strict-LRM
   tools reject it). Changed to `[IDLE_CNTR_WIDTH-1:0]` (identical width).
   `test_clock_gate_ctrl` passes on a clean build.
3. **pwm.sv** — `w_all_repeats_done` compared `r_repeat_value` against
   `local_repeat` while that register increments in the same period-boundary
   cycle, so `repeat_count = N` emitted N+1 periods (and repeat=1 "single pulse"
   gave two). This disagreed with the docs AND pwm's own header waveform.
   Compare against `local_repeat - 1`; the existing `local_repeat==0` (infinite)
   branch guards the subtraction. `test_pwm` 9/9 on a clean build. NOTE: the
   existing test waits for `done` but does not count exact periods, so it did
   not catch this — a period-count assertion would be a good follow-up.

Also corrected stale/incorrect RTL header comments (comment-only, all still
lint clean): `sort.sv` said "ascending (smallest at LSB)" but the compare-swap
sorts DESCENDING with the largest at the LSB; `sync_pulse.sv` advertised a
phantom "toggle synchronized back to source for ready" feedback path that has no
port or logic, and gave two inconsistent min-spacing figures; `fifo_sync.sv` /
`fifo_async.sv` advertised sim-only overflow/underflow detection the bodies
never contained.

## COMMON-001 — Improve test coverage to 95%
**Status:** closed — 100% module coverage, exceeded the 95% target. P2.

Every module in `rtl/common/` has a test. Baseline coverage was ~90% with gaps
in clock utilities, synchronizers and miscellaneous modules.

## COMMON-002 — Waveform save files for all modules
**Status:** closed. P3.

GTKWave save files so a failing test opens with the relevant signals already
grouped rather than requiring them to be found by hand.

## COMMON-004 — Documentation consistency review
**Status:** closed — Phase 3 complete (all Priority 1 and 2 modules). P2.

Module documentation reconciled against the RTL: headers, parameter tables with
ranges, port lists, notes.

## COMMON-005 — Parameterization audit
**Status:** closed — audit complete. P3.

Modules scored on parameterization quality; Priority-1 modules (score < 60)
identified and addressed. See [[sizing-invariants]] for the practice this fed.

## COMMON-012 — arbiter_round_robin_simple starved agents (Kimi round_2)
**Status:** closed 2026-07-23 — RTL fixed, doc corrected, regression test now catches it

The module rotated its priority pointer the wrong direction. Rotating the
request vector LEFT by `last+1` maps rotated bit j to agent `(j - s) mod N`, so
the scan started at agent `(N - last - 1)` instead of `last + 1`. That is a
REFLECTION of the pointer, not a rotation — and a reflection composed with
itself is the identity, so the pointer oscillated between two positions. With
N=4 and all four agents requesting it granted 0,3,0,3,... forever; two of four
agents were NEVER served. Fix: rotate right first, then left back.

Measured on the real RTL under Verilator, before/after: 10/0/0/10 -> 5/5/5/5.

Three things this exposed, all now fixed:

1. **The doc table was computed for the wrong direction** and was internally
   inconsistent (its own `Selected` column could not produce its `Grant` column
   for two of five rows). Recomputed from the fixed logic.
2. **The fairness threshold was meaningless.** `min_fairness_threshold = 0.3`
   on a 4-client arbiter: Jain's index for k of n served equally is k/n, so 0.3
   passes with TWO clients completely starved (index 0.5). The test reported
   "fairness: 0.500" and PASSED against a starving arbiter. Raised to 0.7 and
   backed by a direct per-client zero-grant assertion.
3. **No stimulus ever saturated.** None of ArbiterMaster's profiles assert all
   clients continuously — even `fast` leaves a 1-3 cycle gap — so the arbiter
   was never forced to walk its rotation and the request pattern, not the
   arbiter, decided who was served. Added a `test_saturated_fairness` phase
   using the BFM's `force_client_request()` manual-control path.

Mutation-checked: the new assertion FAILS on the pre-fix RTL
("STARVATION under saturation: client(s) [0, 3] received ZERO grants") and
passes after. Full arbiter suite 23/23.

Blast radius: none in-repo. `arbiter_round_robin_simple` has no instantiators —
the sibling arbiters only name it in comments and use
`arbiter_priority_encoder` internally. It is a library module someone could
have picked up, which is exactly how it survived unnoticed.

Practice recorded in [[randomization]].

---

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

**CLOSED 2026-08-05 — fixed in the DV framework.**

`registered_grant` is now a monitor constructor argument. It selects which
request vector the compliance check is paired with: the previous cycle's for a
DUT that registers its grant (`arbiter_round_robin`, the default), the current
cycle's for one that drives grant combinationally. `arbiter_round_robin_simple`
passes `registered_grant=False`.

The local "UNEXPLAINED (COMMON-018)" logging is gone and the simple TB now
asserts on the compliance verdict with no exclusions: 144-176 violations per
run became 0. gate/func/full all green.

---

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

**CLOSED 2026-08-05 — fixed in the DV framework.**

The model now mirrors `r_last_valid`. Two consecutive grant-less cycles drop
the priority mask back to reset, so the first grant after a `block_arb`
interval is expected to restart at the lowest requester instead of continuing
the rotation.

Two things had to be right, and the first attempt got both wrong:

1. **Where.** The reset must happen in the compliance *replay*
   (`run_compliance_analysis`), not in the monitor's sampling loop. Grants are
   queued and the round-robin state is advanced during replay, so resetting the
   mask live mutates state the replay re-derives and changes nothing. The first
   fix did exactly that and the violation survived it.
2. **How idle is measured.** The replay sees only grants, so the gap has to be
   counted by the sampling loop (which sees every cycle) and handed over as
   `idle_before`. Inferring it from transaction timestamps instead produced
   40-60 false violations per run.

The threshold was measured against the RTL rather than argued: park the mask on
client 1, hold requests low for N cycles, then request {0,3}. One grant-less
cycle grants 3 (rotation holds), two or more grant 0 (mask reset).

Mutation-checked: disabling the mirror restores the violation. The
`round_robin_violation` exclusion is gone from the TB and 5/5 runs are clean —
`arbiter_round_robin` func went from ~45s with reruns to 15s with none.

---

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

**CLOSED 2026-08-05 — partially fixed; ACK-mode residual split out to
COMMON-019.**

Two real defects fixed in the DV framework:

1. **ACK level vs edge.** `ack_detected` fires on any change of the vector and
   the handler iterated every set bit it was given, so a held ACK was
   re-presented every time another client's ACK moved. Now only newly-asserted
   bits count: `ack_vector & ~prev_ack_vector`.
2. **ACKs were processed live against a table built during replay.**
   `pending_acks` is only written while replaying the queue, so an ACK handled
   at sample time looked at a table that did not yet contain its own grant, and
   every such ACK was reported as `unexpected_ack`. ACKs are now queued
   (`queue_ack`) and replayed in one timestamp-ordered stream with the grants.
   That took the ACK-mode configs with warnings from 6 of 6 to 2 of 6.

The compliance verdict is read and asserted on in both arbiter TBs with no
exclusions (no-ACK mode). What remains is tracked as COMMON-019.


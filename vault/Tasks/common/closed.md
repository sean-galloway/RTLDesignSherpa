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

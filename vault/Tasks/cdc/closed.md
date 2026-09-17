<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# cdc — Closed (done)

_None._

---

## CDC-FORMAL-STALE — the 4-phase handshake formal proof ran against a pre-rename DUT copy
**Status:** CLOSED 2026-09-16 — all three work items done. The proof now reads
the shipped RTL and covers both parameters it could not previously see, and
doing so immediately found a real defect ([[CDC-002]]).

**Item 1 (refresh the forked copy) was overtaken and done better.** The fork
`cdc_handshake_formal.sv` is gone rather than refreshed: the 2026-09-11 sweep
deleted every hand-copied DUT in the repo and moved the tasks onto sv2v, so
`formal/cdc/cdc_4_phase_handshake/` flattens and proves
`rtl/cdc/cdc_4_phase_handshake.sv` itself. The old `formal/cdc/cdc_handshake/`
directory no longer exists. (A copy survives in the stale
`pumice-ataglance-modes` worktree; that checkout is ~677 commits behind and
corrects itself when it takes main.)

**Items 2 and 3 (properties for the two parameters, and re-run).** sv2v keeps
`TIMEOUT_CYCLES` and `FAST_PATH` as real parameters in the flat file, so each
configuration is driven by `chparam` from its own sby task -- the same shape
`wb4_slave`/`wb4_master`/`wb4_retry` already use. Six tasks now:

| task | config | result |
|---|---|---|
| prove / cover | defaults | PASS |
| prove_timeout / cover_timeout | `TIMEOUT_CYCLES=4` | PASS |
| cover_fast | `FAST_PATH=1` | PASS |
| prove_fast | `FAST_PATH=1` | **FAIL — CDC-002, left red on purpose** |

New properties: `ap_no_lost_transfer` (checked in every configuration -- the
source may only accept a new transfer once the destination has actually taken
the previous one), `ap_timeout_quiet_when_idle`, `ap_timeout_fires` (a
transfer stalled past the programmed count MUST raise `src_timeout`, so the
counter cannot silently do nothing), plus covers `cp_timeout` and
`cp_fastpath_taken`. The covers matter: `cover_fast` reaching
`cp_fastpath_taken` proves the fast branch is genuinely exercised, so the
`prove_fast` failure is not vacuous.

**The timeout path is sound.** It was the other "most likely to carry a bug"
candidate and it holds: the count is cleared in `S_IDLE`, never fires before
anything is sent, and always fires once a transfer stalls past the threshold.

---

## CDC-001: scrub the tests for completeness (cdc)
**Status:** CLOSED 2026-09-16 — testqc round_2 ran end to end over `val/cdc`,
15 tests in 5 units, 42.1 min, 5 ok / 0 failed. **14 findings: 12 confirmed
against the code, 2 refuted. Seven fixed here, two filed as [[CDC-003]] /
[[CDC-004]], three were documentation defects fixed in place.**

**Every finding was verified against the source before being acted on**, and
that mattered — two did not survive:

- *"The wavedrom wrappers never deliver TEST_LEVEL, so only the gate branch is
  reachable"* (raised twice, parts 02 and 03). **Refuted.**
  `cocotb_test/simulator.py` lines 204-205 copy the parent `os.environ` into
  the sim env, *after* seeding it from `extra_env` — so the parent env wins and
  `TEST_LEVEL=full pytest …` reaches the full branch today. No fix needed.
- *"A docstring advertises clock ratios no grid runs"* — partially refuted:
  ratios ARE swept (the wrapper parametrizes the periods and passes them via
  `extra_env`), but the grid tops out at 2.0x while the docstring claimed 2.5x.
  Fixed as a documentation defect.

**Fixed:**
- `cdc_2_phase_handshake.py`: a detected CDC ordering violation incremented
  `cdc_violations`/`timing_errors` but never `total_errors`, which IS the pass
  gate — so the violation logged an error and the test passed. The 4-phase
  sibling already carried the one-line fix with a comment; it was never
  back-ported. Now identical. **Honest scope:** the reviewer claimed the same
  stimulus fails the 4-phase suite. It does not — 4-phase passes 53/53 at
  REG_LEVEL=FULL and the branch never fired in 134 configurations. This closes
  a LATENT hole, it does not fix an observed escape.
- `cdc_open_loop.py`: `run_walking_pattern` and `run_back_to_back` compared
  only `len(received)` — a pulse delivered with wrong data passed. The TB
  already had `verify_no_loss()`; the phases simply never called it. Added
  `verify_slice_no_loss()` (per-phase slice, because the whole-queue form would
  false-fail after any phase that legitimately drops pulses at the stretch
  cliff) and wired both phases to it. The check is visibly armed -- `✓ walking:
  32/32 arrived, data verified` -- and **mutation-checked**: inverting the RTL's
  `dst_data <= r_src_data` to `~(r_src_data)` makes it fail with
  `DATA MISMATCH at #0: sent=0xA5A5 recv=0x5A5A`, while the count check alone
  would still have passed (the same number of pulses arrive). RTL restored
  byte-identical afterwards.

  *The first mutation attempt proved nothing and looked like success:* XORing
  with `1'b1` broke elaboration, so 28 tests "failed" in 1.85 s with zero
  `DATA MISMATCH` lines -- a compile abort, not a detection. Mutate
  width-safely (`~x`) and check the run actually elaborated.
- `test_fifo_buffer_async.py`: three of four checking phases returned a verdict
  the test discarded (`comprehensive_randomizer_sweep`, `back_to_back_test`,
  `stress_test_with_random_patterns`). `simple_incremental_loops` does assert
  internally, but runs FIRST, so it cannot see the later phases. All three now
  asserted.
- `test_johnson2bin.py`: resolved the filelist's include dirs and then passed
  `includes=[]`, discarding them. Now `includes=includes`.
- Two TBs (`johnson2bin_tb`, `counter_johnson_wavedrom_tb`) lacked the
  contract's `setup_clocks_and_reset` — they had invented `setup_clock()` /
  `reset_dut()` names. `TBBase` supplies the other two methods but not this
  one (97 TB files define it). Added, delegating to the existing pair.
- The two counter wavedrom wrappers parametrized on `wave_cfg`, which only
  named the `sim_build` directory — so `REG_LEVEL=FULL` ran three IDENTICAL
  generations. Grid collapsed. (Checked the other six `_wavedrom_grid` users:
  they bind real widths/depths/clock periods, so this was cdc-local.)
- Documentation: johnson2bin's pair list was wrong in the docstring AND in
  three of four inline comments (the code's widths are the correct ones);
  gaxi_buffer_async advertised `basic|medium|full` against
  `valid_levels = ['gate','func','full']`.

**Validation:** 30 passed (open_loop + both wavedrom), 34 passed (johnson2bin +
fifo_buffer_async), 53 passed at REG_LEVEL=FULL on each handshake suite — each
after `make clean-all`.

**Not done, filed instead:** [[CDC-003]] (fifo_async wavedrom hand-drives
`dut.read` against a live auto-started BFM) and [[CDC-004]] (a 349-line TB
class inside its own test file). Both touch the same class, both change
committed wavedrom JSON, and both are refactors rather than scrub fixes.

---

## CDC-004: a TB class lived inside test_fifo_async_wavedrom.py
**Status:** CLOSED 2026-09-16 — pure move, proven.

`FifoAsyncWaveDromTB` now lives at `bin/TBClasses/cdc/fifo_async_wavedrom_tb.py`,
beside the siblings it should always have sat with
(`counter_johnson_wavedrom_tb`, `counter_bingray_wavedrom_tb`). The test file
drops from 526 to 286 lines; imports split 6 to the TB, 15 staying with the
wrapper; the single consumer was rewired to import it.

**Correction to this task as filed:** the class is **237 lines (66-302)**, not
349. The original figure came from a boundary scan that overshot; the 241-line
diff reconciles with 237 plus the import-block tidy.

**How "changed nothing" was proven, because the obvious gate does not work.**
Byte-identical wavedrom JSON is NOT available: `get_wavejson_dir` documents
that "Wavedrom output is NOT deterministic -- two consecutive runs of the same
test produce different waveform lengths", and it writes to a GITIGNORED
`WAVES/staged/<module>/`, never to the committed diagrams. Measured directly:
two identical pre-move runs differed in bytes on all three files, with wave
lengths 55 vs 66 and 55 vs 61 — while the file set and all 12 signal names per
file stayed stable.

So the gate became: (1) the moved class body diffs **byte-identical** against
the extracted original — it does, the diff is empty; (2) `TEST_LEVEL=full`
passes 3/3; (3) staged output matches the pre-move baseline on file set and
signal names. All three hold.

Note `TEST_LEVEL` gates how many scenarios emit — `gate` emits two of three —
so this was baselined and validated at `full`, or a third of the output would
never have been exercised.

---

## CDC-002: cdc_4_phase_handshake FAST_PATH acknowledged a transfer the receiver never took
**Status:** CLOSED 2026-09-16 — fixed by option 2, and the parameter deleted.

`D_IDLE` sampled `dst_ready` and then set `dst_valid` AND `r_ack_dst` together on
the following cycle. A receiver that dropped ready in between was acked for a
beat it never took: `dst_valid && dst_ready` never held, `D_WAIT_REQ_CLR` drove
valid low, and the beat was silently lost.

The destination now always transitions to `D_WAIT_READY`, which acks only on an
OBSERVED handshake. That made `FAST_PATH` save nothing, so it was removed rather
than left as a knob that did nothing.

**Blast radius was wider than this task first recorded** — it said "two
instantiations in cdc_counter_domain.sv". In fact the consumers were in two
different areas: `cdc_counter_domain.sv` (FPGA demo build, passed `1'b1`) and
`retro_legacy_blocks/rtl/rtc/rtc_core.sv` (passed `1'b0`). Both had the
connection dropped.

**Evidence:** the flat rebuilt from the fixed RTL contains no `FAST_PATH`, and
the four remaining proofs pass — `prove`, `cover`, `prove_timeout`,
`cover_timeout`. `prove_fast`/`cover_fast` are gone with the parameter, along
with their Makefile targets and sby tasks. `ap_no_lost_transfer` — the property
that caught this — remains and still passes; its counterexample against the
unfixed design (`D_WAIT_REQ_CLR` with `r_ack_dst=1` and zero destination
completions) is the mutation evidence.

**Directed test added 2026-09-16, closing the debt above.**
`val/cdc/test_cdc_4_phase_handshake.py` now carries a `TIMEOUT_CONFIG` entry
(`TIMEOUT_CYCLES=512`, 10 ns / 20 ns) alongside the clock-period sweep, which
had set no RTL parameters at all -- so every other config elaborates
`g_no_timeout`, where `src_timeout` is tied to `1'b0`. A second cocotb test,
`cdc_4_phase_timeout_test`, stalls the destination and watches the source in
BOTH builds: when the counter is compiled in it must assert within bounds and
clear once the stall lifts; under the same stimulus with the counter compiled
out it must stay low. A parameter's OFF state needs its own test, and this is
it. Measured: asserted at exactly 512 clk_src cycles.

**Mutation evidence:** forcing `src_timeout <= 1'b0` inside `g_timeout` turns
the new test red -- "src_timeout never asserted within 1224 clk_src cycles" --
with the `TIMEOUT_CYCLES=512` build confirmed from the log as the one that ran.
The RTL was restored byte-identical, 0 markers left.

The stall uses `GAXISlave.ready_policy = 'stall'`, not a large `ready_delay`:
once phase 2 has latched a randomized delay it cannot be shortened, which would
put the recovery half of the test out of reach. The slave's own docstring makes
the same point -- randomized `ready_delay` "cannot do that: it is not
controllable."

---

## CDC-003: fifo_async wavedrom scenarios hand-drove dut.read against a live BFM
**Status:** CLOSED 2026-09-16 — reads now go through the BFM, and the captured
diagrams are strictly better than the ones they replace.

**The contention was real:** `FifoBufferTB` constructs a `FIFOSlave` whose
`BusMonitor` base auto-starts `_monitor_recv`, and it drives `read_sig` through
`_set_rd_ready` at five sites. The scenarios poked `dut.read` by hand anyway.

**What the evidence actually showed, against this task as filed.** The filed
fix said "drive reads through the BFM". Measuring the baseline first showed the
BFM was *already* driving everything visible: 7 of the 8 read edges in the
pre-change diagrams occur DURING the fill — slave drainage on its own randomizer
schedule — while the hand-driven loops fell almost entirely outside the capture.
So the diagrams had been recording the contention since they were promoted
2026-07-25.

**Three BFM attempts failed before the real obstacle was found**, and it was not
the randomizer: switched profiles, a park sized to the fill, and a looping
`read_delay` sequence all produced ZERO in-window reads. The cause was the
capture slice in `constraint_solver.py`:

    start = seq_start - context_before
    end   = seq_end + context_after + post_match_cycles + 1

with `context_cycles_*` left at `None`, both resolve to `max(3, window_size//4)`.
At `max_window_size=200` that is ~50 trailing samples, which closes the capture
while the fill is still finishing — and BFM reads can only follow the fill.
Raising `max_window_size` alone changes nothing; the trailing context is the knob.

**The fix:** `read_delay` is an exact looping sequence `[fill_hold, spacing]`
(FlexRandomizer loops a list: `value = sequence[0]; sequence.rotate(-1)`), so the
first consult holds the reader off while the FIFO fills and every consult after
is the scenario's drain spacing. The constraint gained
`context_cycles_before=5`, `context_cycles_after=150`, `max_window_size=300`.
The clock grid is now uniformly 10/12 ns (the `(32,8,10,20)` pair went).

**Result, measured against the pre-change baseline:**

| diagram | wave len | read edges | after last write |
|---|---|---|---|
| gray_code_sync | 50 -> 98 | 2 -> 4 | 0 -> 3 |
| power_of_2_depth | 50 -> 141 | 3 -> 6 | 0 -> 4 |
| write_fill_read_empty | 50 -> 127 | 2 -> 4 | 1 -> 4 |

`wr_full` TRANSITIONS in write_fill_read_empty for the first time in any
version, including the committed artifacts: scenario 1 writes `TEST_DEPTH - 1`
in its loop PLUS one more after it, so with the reader parked the FIFO genuinely
fills. (An earlier note in this task claiming it could never fill was wrong.)

**Staged only.** `get_wavejson_dir` writes to the gitignored
`WAVES/staged/<module>/`; promoting to the tracked diagrams is a deliberate
`WAVEJSON_DIR=docs/markdown/assets/WAVES` run, not done here — the committed
`.png` files beside the JSON would need regenerating with them.

# TASK-001: scrub the tests for completeness (cdc)

> Migrated 2026-09-27 from `vault/Tasks/cdc/closed.md` as **CDC-001** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
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
  cliff) and wired both phases to it. The check is visibly armed -- `walking:
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

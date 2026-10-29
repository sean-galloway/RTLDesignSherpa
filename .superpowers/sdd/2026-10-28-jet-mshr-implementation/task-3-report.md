# Task 3 Report: `jet_wb_buffer` decoupled writeback buffer

## Scope
Implement the J5 dirty-victim FIFO (`jet_wb_buffer`) for `projects/components/cache-ip/jet-mesi-l1`, plus its harness, cocotb testbench/testplan, filelist, and integration into `jet_all.f`.

## Original implementation (commit feacb32b0)

### What was built
- `rtl/fub/jet_wb_buffer.sv` — VICTIM_DEPTH-deep circular FIFO of dirty victims.
  - Beat-serial capture (`cap_i`/`cap_line_i`/`cap_beat_i`/`cap_beat_data_i`).
  - Streaming beat drain (`drain_req_o`/`drain_line_o`/`drain_beat_data_o`/`drain_accept_i`/`drain_done_i`).
  - Snoop snarf (`sn_line_i` → `sn_hit_o`/`sn_data_o`/`sn_bresp_cycle_o`) with `sn_eff_i` recording.
  - `wb_occupancy_o` popcount.
- `rtl/filelists/jet_wb_buffer.f` and append to `rtl/filelists/jet_all.f`.
- `dv/tb/jet_wb_buffer_th.sv` — parameter-forwarding harness.
- `dv/tbclasses/jet_wb_buffer_tb.py` — golden-model scored TB.
- `dv/tests/test_jet_wb_buffer.py` — pytest runner (default geometry cell only).
- `dv/testplans/jet_wb_buffer_testplan.yaml`.

### TDD evidence
1. **RED**: stub RTL returned all zeros; `SEED=1 REG_LEVEL=GATE pytest .../test_jet_wb_buffer.py` failed as expected.
2. **GREEN** after fixes:
   - Replaced lowest-free-slot allocation with tail-pointer circular FIFO.
   - Aligned TB golden model `head`/`tail` pointers with physical slots so `cap_slot_o` scored correctly.
   - Capped random-phase beat accepts to `FILL_BEATS - beats_sent` and skipped data checks once an entry was beat-complete to avoid counter-wrap mismatches.

```bash
$ cd projects/components/cache-ip/jet-mesi-l1/dv/tests
$ SEED=1 REG_LEVEL=GATE python3 -m pytest test_jet_wb_buffer.py -v
# 1 passed, 1 warning
$ SEED=1 REG_LEVEL=FUNC python3 -m pytest test_jet_wb_buffer.py -v
# 2 passed, 2 warnings
```

### Verification before commit
- `filelist_registry.py --check --audit --blindspots --placement --testplans --ratchet` + `check_broken_links.py --ratchet` all PASS.
- Commit: `feacb32b0 feat(jet): jet_wb_buffer + unit TB (J5)`.

---

## Fix round (review findings)

### Finding 1 — drain side must be l1_victim-shaped
The brief's per-beat drain streaming conflicted with the global plan that `l1_drain` consumes the buffer unchanged. Ruling: l1_victim shape wins.

**Changes:**
- Removed `drain_req_o`, `drain_line_o`, `drain_beat_data_o`, `drain_accept_i`.
- Added `drain_valid_o`, `drain_addr_o[ADDR_WIDTH-1:0]` (line + zero offset), `drain_data_o[LINE_WIDTH-1:0]`.
- Kept `drain_done_i` as the BRESP retire pulse.
- Updated module header comment to state the l1_victim compatibility truthfully.
- Updated harness and TB golden model to drive/check the new head outputs.
- Rewrote directed drain scenarios to BRESP-retire the head; `oldest_first_order` now delays BRESP for A and verifies the head stays A until retirement.

### Finding 2 — partial-capture slot leak
The original RTL closed the open slot when `cap_i` deasserted mid-gather, leaving an allocated-but-never-valid entry.

**Changes:**
- Removed the `r_open && !cap_i` close logic. The slot now stays open across `cap_i` pauses and closes only on the last beat.
- Added a `translate_off` bounded-pause assertion so a stuck partial capture fails loudly in simulation.
- Added directed `capture_pause_resume` scenario: pause after 2 beats, resume, complete, drain.

### Minor fixes
- `sn_eff_i` write gated on `sn_eff_i != JET_PEND_NONE` so a non-matching or no-effect snarf cycle cannot clobber a pending effect.
- `_scen_snarf_invalidated_still_drains` now checks DUT `wb_occupancy_o` via `_check_occupancy` instead of scoring the model against itself.
- Testplan coverage line numbers and scenario descriptions updated for the new RTL.

### TDD evidence for fix round
1. **Compile RED** after first assertion draft: Verilator rejected `##[1:$]` range delay.
2. **GREEN** after replacing it with a bounded simulation-only pause counter:

```bash
$ cd projects/components/cache-ip/jet-mesi-l1/dv/tests
$ SEED=1 REG_LEVEL=GATE python3 -m pytest test_jet_wb_buffer.py -v
# test_jet_wb_buffer[2-64-64-gate] PASSED — 183 checks, 0 mismatches
$ SEED=1 REG_LEVEL=FUNC python3 -m pytest test_jet_wb_buffer.py -v
# test_jet_wb_buffer[2-64-64-gate] PASSED
# test_jet_wb_buffer[2-64-64-func] PASSED — 956 checks, 0 mismatches
```

### Verification before this commit
- `filelist_registry.py --check --audit --blindspots --placement --testplans --ratchet` + `check_broken_links.py --ratchet` all PASS.

## Files changed in this fix round
- `projects/components/cache-ip/jet-mesi-l1/rtl/fub/jet_wb_buffer.sv`
- `projects/components/cache-ip/jet-mesi-l1/dv/tb/jet_wb_buffer_th.sv`
- `projects/components/cache-ip/jet-mesi-l1/dv/tbclasses/jet_wb_buffer_tb.py`
- `projects/components/cache-ip/jet-mesi-l1/dv/testplans/jet_wb_buffer_testplan.yaml`
- `.superpowers/sdd/2026-10-28-jet-mshr-implementation/task-3-report.md`

## Self-review
- `l1_victim` shape is now explicit and matches `victim_valid`/`victim_addr`/`victim_data`/`victim_clear` semantics.
- Capture pause/resume is covered by both RTL behavior and a directed scenario; the simulation assertion documents the "never aborts" contract.
- `sn_eff_i` hazard is closed.
- No MAS docs were touched, per controller ruling.
- Remaining gap: the J7 VICTIM_DEPTH {1,2,4} sweep is still out of scope; only the default depth=2 cell is verified.

---

## Follow-up fix: vacuous partial-capture assertion

### Problem
The `translate_off` bounded-pause assertion used a 10-bit counter (`$clog2(1023 + 1) = 10`) to count up to `MAX_PAUSE_CYC = 1023`. Because the counter wrapped from 1023 back to 0, the expression `r_pause_cnt <= 1023` was always true and the assertion could never fire.

### Fix
Widened the counter to 11 bits by computing `PAUSE_CNT_W = $clog2(MAX_PAUSE_CYC + 2)`. The counter can now represent the value `MAX_PAUSE_CYC + 1 = 1024`, so after 1024 paused cycles the assertion `r_pause_cnt <= 1023` evaluates false and the `$error` fires.

### Files changed
- `projects/components/cache-ip/jet-mesi-l1/rtl/fub/jet_wb_buffer.sv`
- `projects/components/cache-ip/jet-mesi-l1/dv/testplans/jet_wb_buffer_testplan.yaml` (assertion line number)

### Verification
```bash
$ cd projects/components/cache-ip/jet-mesi-l1/dv/tests
$ SEED=1 REG_LEVEL=GATE python3 -m pytest test_jet_wb_buffer.py -v
# test_jet_wb_buffer[2-64-64-gate] PASSED — 183 checks, 0 mismatches
$ SEED=1 REG_LEVEL=FUNC python3 -m pytest test_jet_wb_buffer.py -v
# test_jet_wb_buffer[2-64-64-gate] PASSED
# test_jet_wb_buffer[2-64-64-func] PASSED — 956 checks, 0 mismatches
```

### Why the assertion is now firable
With `PAUSE_CNT_W = 11`, `r_pause_cnt` ranges 0..2047. The assertion checks `r_pause_cnt <= 1023`. During a real pause the counter increments every cycle while `r_open && !cap_i`; after 1023 paused cycles `r_pause_cnt == 1023` (pass), and on the 1024th paused cycle it becomes `1024` (fail), so the `$error` can be reached. The existing directed `capture_pause_resume` scenario exercises legal short pauses; an artificially long pause would trigger the assertion.

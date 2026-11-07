# TASK-001: CDC demo build plan -- delivered as one top with five runtime CDC modes

> Migrated 2026-11-07 from `projects/fpga-systems/NexysA7/misc-ip/cdc_counter_display/docs/CDC_DEMO_TODO.md` section 5 ("Demo Build Plan") and section 6 ("Open Questions"). The file's background sections (3, 4) became `docs/CDC_FAILURE_MODES.md`; its primitive-selection sections (1, 2) were dropped in favour of the rtl-cdc book. Its own 2026-07-22 note ("not built as written") was stale: the demo was built, differently.

**Priority:** P2
**Status:** CLOSED 2026-09-08 -- `build-demo` (`cdc_demo_top`) board-validated on Nexys A7 210292BFA3EE: smoke, press 50x exact, cfg-load, cdc-mode round-trip, watch-fail sweep 5.96 Hz - 50 MHz, all four MMCM clocks measured (`stable/MANIFEST.md`). Timing met, WNS +3.223 ns.
**Owner:** sean galloway

## Plan vs what was built

The plan asked for five sibling top-levels plus two "lucky case" variants. The
build is one top, four counters, each with a runtime `CDC_MODE` CSR
(`build-demo/rtl/cdc_counter_domain.sv`); every mode is instantiated and a
sys_clk mux selects one. That answers open questions 1 and 2 (one
parameterized top; the broken variants differ by a mode, not a directory).

| Plan item | Delivered as |
|---|---|
| `demo_5_broken_no_cdc` | mode 0 NO-CDC (the reset value) |
| -- (not in the plan) | mode 1 STRETCH, `cdc_open_loop` tuned to a ~20-25 MHz cliff: the "tuned to work" anti-pattern |
| `demo_4_async_fifo` | mode 2 SYNC_FIFO, `fifo_async` depth 16 |
| `demo_2_2phase` | mode 3 TWO_PHASE, `cdc_2_phase_handshake` |
| `demo_3_4phase` | mode 4 FOUR_PHASE, `cdc_4_phase_handshake` |
| `demo_5c_broken_but_slow` | the slow end of the `watch-fail` sweep (mode 0 reads clean at Hz-kHz) |
| lab write-up, "sweep until impossible values" | `make host-cdc_demo ARGS="watch-fail --counter 2"`, `docs/HARNESS.md`, six episode scripts in `docs/transcripts/`, the `cdc_demo_guide` and `cdc_fpga_system` books |
| per-variant XDC with `set_max_delay -datapath_only` | one `build-demo/fpga/constraints/cdc_demo.xdc` |
| per-variant cocotb test | one shared UART-harness test, `build-demo/dv/tests/test_cdc_demo_uart.py` -- see TASK-002 for what it does not cover |

The v3 clocking (MMCM, co-prime divisors 11/29/67/128, glitchless
`BUFGMUX_CTRL` tree) also removes the plan's 4b trap (integer, phase-related
clocks) by construction.

## Not built, filed separately

- TASK-002 -- sim does not carry a value through modes 1-4
- TASK-003 -- the cross-mode comparison table (`docs/COMPARISON.md` in the plan)
- TASK-004 -- `demo_1_synchronizer`, the single-bit `cdc_synchronizer` case
- TASK-005 -- a metastability injector so RTL sim can show mode 0 failing (open question 3; also the plan's `demo_5b` static case)

Out of scope, as the plan said: formal on the primitives (they have their own
proofs under `formal/cdc/`), new primitives, other boards. Open question 4
(Vivado for area) is folded into TASK-003.

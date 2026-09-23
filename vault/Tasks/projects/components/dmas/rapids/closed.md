<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# RAPIDS tasks — closed

Completed tasks, newest first. Convention: [Tasks](../../../../INDEX.md).

## TASK-081: the board kick sequencer never writes KICK_ENABLE, and no sim can catch it

**Priority:** High — the rapids board characterization campaign cannot launch a
channel. **Status:** CLOSED 2026-09-22 -- all four items done, board-confirmed.

`rapids_beats_top` replaced write-to-kick with staged `CHx_DESC_ADDR_{LOW,HIGH}`
plus a rising-edge-detected `KICK_ENABLE` (SRC 0x0040 / SNK 0x1040). The on-chip
kick sequencer in `rapids_char_top.sv` still implements the OLD protocol: it
walks `KST_SCAN -> KST_LOW -> KST_HIGH` emitting APB writes at
`base + ch*8` and `+0x4` only, and its own comment states the stale assumption
outright -- `KST_HIGH: // HIGH write triggers the kick` (line 823). There is no
write to `KICK_ENABLE` anywhere in the kick path (0 matches).

So `_stage_kicks()` + `go()` -- the path the campaign actually uses in
`run_characterization.py` -- stages descriptor addresses and never pulls the
trigger. Same root cause as the sink self-check failure fixed in the cocotb TB,
but in a second, independent implementation.

**Why no test catches it.** The sim toplevel is `rapids_char_harness`; the
bitstream top is `rapids_char_top`. `flists/rapids_char_harness.f` references
`rapids_char_top.sv` **zero** times, so the sequencer sits ABOVE the simulated
DUT and `verify-sim` is structurally incapable of exercising the board's launch
mechanism. The gate can be fully green while the board never kicks.

> **SUPERSEDED 2026-09-23 by TASK-084.** That paragraph was true when written and
> is no longer. The whole host path (UART -> AXIL -> region decode -> harness CSRs
> -> kick sequencer -> apb4_master) was moved INTO `rapids_char_harness`, which is
> the sim toplevel, so `verify-sim` now exercises the board's launch mechanism
> directly. The structural gap this task documented is closed by construction
> rather than by the bolt-on test.

**Do:**
- [x] Add the `KICK_ENABLE` write to the sequencer. Done 2026-09-22: new
      `KST_KICK` state after the scan completes, issuing ONE write to
      `w_kick_base + 0x040` carrying the whole staged mask, so every channel
      launches on the same cycle. `KST_SCAN` routes to it only when the mask is
      non-zero, so `GO` with mask=0 stays a no-op. The enum widened `[1:0]` ->
      `[2:0]` to hold the fifth state.
- [x] Delete the dead `kick_channel()` in `run_characterization.py`. Done
      2026-09-22 (no callers repo-wide; the `kick_channels` hits are STREAM's
      unrelated plural helper).
- [x] Close the coverage gap. Done 2026-09-22:
      `dv/test_rapids_char_top_kick.py`, toplevel `rapids_char_top`, driving the
      board top over a simulated UART (`UART_BAUD = FPGA_CLK_HZ / CLKS_PER_BIT`
      passed as a generic so the RTL divisor cannot drift from the TB) through
      the REAL host transport -- `RapidsCharIO` over `UARTAxiBridge(channel=)`.
      Host code and RTL run together, because the defect lived exactly in that
      seam: the host staged and the RTL never pulled the trigger. Asserts
      KICK_ENABLE is written exactly once, carries the staged mask, and is the
      FINAL write after all staging; a second case proves `GO` with mask=0
      pulses nothing.
      ALSO: `make sim` ran only the pinned harness file, so a new test in `dv/`
      would never have executed. It now runs the whole `dv/` directory
      (`DV_TESTS`), so anything dropped there runs by default. `verify-sim`
      stays pinned to the sink self-check -- it is a fast pre-bitstream gate.
- [x] Re-run a board campaign and confirm non-zero beats before trusting any
      previously recorded rapids board numbers. Done 2026-09-22 on the Genesys 2
      (xc7k325tffg900-2, NUM_CHANNELS=8). Rebuilt from the fixed RTL -- the
      bitstream on disk predated the fix by nine days and structurally could not
      kick -- then programmed and characterized:

      - `make bitstream BOARD=genesys2`: RC=0, `verify-sim` passed on the way in
        (no `BITSTREAM_SKIP_VERIFY`), WNS 1.213 ns / TNS 0.000 / 0 failing
        endpoints of 201168, WHS 0.048 / THS 0.000. 27.08% LUTs, 10.26% regs,
        9.89% BRAM.
      - Smoke (2 ch x 4 beats): SINK and SOURCE both PASS, golden-validated.
        `AXI4-wr prod=8`.
      - Campaign (8 ch x 8 beats): **OVERALL PASS**. All 8 sink channels and all
        8 source channels CRC-match golden. `SINK AXI4-wr prod=64` (= 8x8) at
        91.4% util / 5.85 GB/s; `SOURCE AXI4-rd prod=64` at 80.0% / 5.12 GB/s;
        AXIS-out 4096 B in 32 packets. ch0-ch3 goldens 0x89346A28 / 0x1BD7E214 /
        0x942B69BD / 0x06C8E181 are the SAME four the sim produces, so board and
        sim now agree rather than merely both being green.

      Non-zero beats confirmed on hardware. One anomaly fell out and is filed as
      TASK-082: the sink-ingress AXIS meter reads zero on the board while the
      write side counts every beat. It is observability, not datapath -- the CRCs
      match -- but a zero left unexplained in a recorded board number is exactly
      what this task was about, so it is tracked rather than tolerated.

**Validated as far as it can be without hardware.** `verilator --lint-only` on
`flists/rapids_char_top.f`: RC=0, 268 diagnostics, IDENTICAL to the pre-patch
baseline, and zero of them cite `rapids_char_top.sv`. All 268 are pre-existing
MULTIDRIVEN warnings out of the PeakRDL-generated `rapids_regs.sv`.

**Now proven in simulation, and the test is non-vacuous.** Against the FIXED
sequencer: 2 passed. Against the PRE-FIX sequencer (swapped back in, KST_KICK
count 0) the same test FAILS with `KICK_ENABLE (0x1040) was never written --
the sequencer staged the descriptor addresses and never launched`. A test that
passed on both would have proven nothing, which is the trap that let this ship.

Still NOT proven on hardware: the remaining item below. Sim exercises the
sequencer's APB writes, not the board's UART front end at real baud, the
bitstream, or the DUT's response.

**Evidence:** `rapids_char_top.sv:777-860` (sequencer FSM and `w_kick_paddr`),
`run_characterization.py:189,203,288-298` (dead `kick_channel`, `_stage_kicks`,
`go`), `flists/rapids_char_harness.f` (no `rapids_char_top.sv`). The cocotb-side
twin of this defect and its measurements are in
`projects/components/dmas/rapids/known_issues/active/char_harness_sink_selfcheck_no_beats.md`.

## TASK-084: one RTL harness -- move the host path down so verify-sim can reach it

**Priority:** High -- TASK-081 was a defect the gate could not see. Fixing the
defect without fixing the blindness leaves the next one equally invisible.
**Status:** CLOSED 2026-09-23 -- full re-validation, sim and board.

RAPIDS had THREE levels where STREAM has two, and the host path was stranded at
the wrong one:

```
  before                                  after (the STREAM shape)
  rapids_char_genesys2_top  (MMCM/pins)   rapids_char_genesys2_top  (MMCM/pins)
  rapids_char_top   1129 lines            rapids_char_top    262 lines
      UART->AXIL master                       pins + reset sync + LED/7-seg
      region decode, harness CSRs         rapids_char_harness  (SIM TOPLEVEL)
      apb4_master, both AXIL FSMs             UART->AXIL, CSRs, kick sequencer
      the KICK SEQUENCER                      apb4_master, + the DUT
  rapids_char_harness  (SIM TOPLEVEL)
      just wiring + the DUT
```

`stream_harness` takes `i_uart_rx`/`o_uart_tx` directly and owns `harness_csr`;
`stream_genesys2_top` is pins + MMCM + `u_harness`. RAPIDS now matches. 717 lines
relocated by line range -- working, board-validated RTL was never retyped -- and
the old instantiation port map re-expressed as declarations plus alias assigns
for exactly the 35 connections whose actual differed from the formal.

**Harness: 104 ports -> 7** (`aclk`, `aresetn`, `i_uart_rx`, `o_uart_tx`,
`o_led_status`, `o_result_valid`, `o_pass`). The 55 `cfg_*`/`obs_*`/`gen_*`/
`s_apb_*` ports collapsed inward, which is why the port count fell so far: they
were the CSR interface, and the CSRs are inside now.

**The TB went 738 -> 225 lines** because it reuses `RapidsCharCampaign` -- the
BOARD's own host program -- over `UartSimHarness` + `RapidsCharIO` inside
`cocotb.external`. Sim and board now run the same code rather than two
implementations that must be kept in agreement. They had already drifted apart
once: that drift was TASK-081.

**Validation (all of it, because a refactor of a board-validated design earns
none of the benefit of the doubt):**

| gate | result |
| --- | --- |
| lint, both flists | 0 real errors, 268 warnings -- identical in kind to baseline, 0 citing either rewritten file |
| `rapids_char_top` port list | byte-identical (9 ports, 13 params) -- XDC and the Genesys 2 wrapper untouched |
| harness sim | 2 passed (sink + source), 630.75s |
| kick sim | 2 passed (kick_enable + empty_mask), 596.49s |
| `verify-sim` gate | passed on the new TB, proven non-vacuous (link probe + 4 golden CRCs + `wr prod=32`) |
| bitstream | RC=0, WNS 1.041 / TNS 0.000 / 0 failing of 201142, WHS 0.058 |
| board campaign | **OVERALL PASS**, 8ch x 8 beats |

Behaviour is provably unchanged: all 16 board CRCs are byte-identical to the
pre-refactor campaign (`0x89346A28 / 0x1BD7E214 / 0x942B69BD / 0x06C8E181 /
0xB554DBD2 / 0x27B753EE / 0xA84BD847 / 0x3AA8507B`), `AXI4-wr prod=64` at 91.4%
and `AXI4-rd prod=64` at 80.0% both match exactly. Utilisation went DOWN
slightly (55197 -> 55158 LUTs, 41808 -> 41799 regs, BRAM unchanged) -- expected
once a module boundary dissolves and logic merges. WNS 1.213 -> 1.041 ns: tighter
but positive, and a thin positive WNS is this flow's design point.

**Two things fell out of it:**

- `test_rapids_char_top_kick.py` observes `apb_cmd_*`, which is internal to
  `u_harness` now. Repointed to `dut.u_harness.*` AND given `--public-flat-rw`:
  Verilator inlines plain internal wires, and an inlined signal is not `false` at
  runtime, it is ABSENT -- the recorder would have silently seen nothing and the
  test would have failed claiming the sequencer emitted no writes.
- TASK-082 now REPRODUCES IN SIM. See that task.

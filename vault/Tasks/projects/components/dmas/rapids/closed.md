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

## TASK-083: re-measure the beat-count knee on rapids (July data is stale)

**Priority:** Medium. **Status:** open 2026-09-22.

`reports/perf/json/genesys_8ch_2026-07-15.json` (8 channels, recorded
2026-07-15T21:35:42) shows a clean knee:

```
  beats 1, 4, 16  -> PASS in both backpressure modes
  beats 64        -> PASS bpoff, FAIL bpon
  beats 256+      -> FAIL in both        (sink_pass and source_pass fail together)
```

**This has NOT been re-measured.** The 2026-09-22 campaign ran beats=8 only --
deliberately below the knee, so that a failure would be attributable to the kick
rather than confounded by this limit. So the knee is a July-era observation, and
whether it survives the staged-address/KICK_ENABLE refactor and the TASK-081 fix
is simply unknown. It is recorded here because it is real measured data that is
currently documented nowhere, not because it is known to be current.

Note the July numbers are NOT tainted by the TASK-081 kick defect: that defect
was introduced by `4ef2dcef0` (2026-09-13 11:34) and fixed by `8fa5af471`
(2026-09-22 15:02), so only board results recorded inside that window are
suspect. July predates it by two months.

**Do:**
- [ ] `make suite BOARD=genesys2 PORT=/dev/ttyUSB0` with
      `--suite-channels 8 --suite-beats 1,4,16,64,256` and compare against the
      July table. (Both `--suite` AND plain `characterize`/`--smoke` write a
      timestamped JSON in the suite schema now -- fixed 2026-09-23, 77dc4de0e --
      so a run no longer evaporates into scrollback the way the 2026-09-22
      numbers did. Note `flows-rapids-beats/reports/` is gitignored: those files
      are durable on disk, NOT in the repo. The tracked, curated records live in
      `rapids_characterization/reports/perf/json/`.)

**RESULT 2026-09-23: the knee is gone. 28/28 configs pass.**

Two board sweeps on the post-TASK-084 bitstream, 8 channels, both backpressure
modes, both seeds:

```
  beats   1   4  16  64  256 | 1024 4096      July 2026-07-15
  now     P   P   P   P   P  |   P    P       P P P (64 bpon F) (256+ F)
```

Every point July failed now passes: 64/bpon (both seeds), and 256, 1024, 4096
(all four combinations each). Sink and source both golden-validated at every
size, up to 32768 beats total at 4096/channel.

What changed in between is substantial -- the staged-address + `KICK_ENABLE`
refactor, the TASK-081 board-kick fix, and TASK-084 -- so this records that the
limit is ABSENT under today's design. It does not attribute the fix to any one
of them; nobody bisected it and this task does not pretend otherwise.

Records: `reports/rapids_char_suite_20260923_032532.json` (1..256) and
`rapids_char_suite_20260923_032753.json` (1024/4096). Both are gitignored --
durable on disk, not in the repo.

## TASK-082: the sink-ingress AXIS meter reads zero on hardware

**Priority:** Medium -- it does not corrupt data, but it puts a 0.0% utilisation
and "0 B, 0 pkts" into recorded board numbers for an interface that demonstrably
carried traffic. **Status:** CLOSED 2026-09-23 -- fixed and validated in sim AND on the board.

Measured on the Genesys 2, 2026-09-22, on the freshly fixed bitstream:

```
 8ch x 8 beats:  SINK AXIS-in: util=0.0%  (prod=0  bp=0 starv=70 idle=0)  0 B, 0 pkts
                 SINK AXI4-wr: util=91.4% (prod=64 bp=0 starv=6  idle=0)  5.85 GB/s
 2ch x 4 beats:  SINK AXIS-in: prod=0 starv=14        SINK AXI4-wr: prod=8
 sim (OLD tb):   sin meter: prod=32 bp=0 starv=12 idle=100 util=72.7%
 sim (NEW tb):   sin meter: prod=0  bp=0 starv=38            util=0.0%   <-- reproduces
 board 2026-09-23 (post-TASK-084, 8ch x 8): AXIS-in prod=0 starv=70, AXI4-wr prod=64
```

**IT REPRODUCES IN SIMULATION NOW (2026-09-23).** That is the useful part of
this update. Before TASK-084 the cocotb TB hand-sequenced the launch: it kicked
the channels, explicitly waited for `snk_system_idle` to deassert, and only THEN
started the AXIS generator -- with a long comment explaining that this was what
kept the sin window open. The board never does that; it stages everything and
fires one atomic GO. So the old TB was driving the DUT in a way the hardware
never does, and that masked the defect. The TB now reuses the board's own
campaign, drives the same GO path, and reads the same prod=0.

This moves TASK-082 from a board-only mystery (needs the Genesys 2, an ILA, and
a reprogram per experiment) to a waveform-debuggable one (`WAVES=1` on the
harness sim). Worth doing before theorising further.

All sink CRCs match golden in every one of those runs, so the data flowed. The
sink IS AXIS-fed (`axis4_master_pattern_gen` drives `s_axis_*`), so this is not a
different stimulus path -- the meter is blind, not the wire idle.

**MECHANISM PROVEN 2026-09-23 (board suite, 28 configs).** My earlier guess in
this task -- "the clear at window-open wipes the count" -- was WRONG, and so were
two follow-ups (a meter misclassification, then a bad tap). The counters settle
it without a waveform:

```
 beats/ch  total   sin prod  missed   sin starv  wr starv  dStarv   window total
        1      8          0       8          21        13       8   sin==wr  (21)
       16    128          0     128         134         6     128   sin==wr (134)
       64    512        322     190         204        14     190   sin==wr (526)
      256   2048       1858     190         196         6     190   sin==wr (2054)
     1024   8192       8002     190         196         6     190   sin==wr (8198)
     4096  32768      32578     190         196         6     190   sin==wr (32774)
```

Three facts fall out, and together they are conclusive:

1. **`missed == min(190, total)`** -- a FIXED quantity, not a proportional loss.
   Below 190 total beats the whole transfer is missed, which is why small runs
   read exactly 0 and looked like a dead meter.
2. **Beats lost from `prod` reappear in `starv`, exactly** (dProd == dStarv on
   every row). Nothing is uncounted; the meter is awake and watching an idle
   wire.
3. **`sin` and `wr` report the SAME window total** on every row, so they share
   one `obs_meter_clear`/`obs_meter_freeze` and the window itself is fine.

So the beats are not lost inside the window -- they land in a DEAD ZONE between
the meter being armed and the window actually opening, and inside the window the
ingress sits starved for precisely that many cycles while the write side drains
what was buffered.

**Confirmed at cycle level 2026-09-23** (`WAVES=1` sink run, timescale 1ps,
aclk=10,000ps, 4ch x 8 beats = 32):

```
  clear #2        875,840,000   GO: arms the meter AND pulses cfg_gen_start
  32 handshakes   875,860,000 .. 876,170,000   (31 clocks, back to back)
  clear #3        876,940,000
  obs_win_active  876,950,000 .. 877,330,000   (38 clocks)  <-- the counted window
  obs_wr_prod     reaches 32 INSIDE that window
  obs_sin_prod    never leaves 0
```

The window that produces the reported numbers opens **78 clocks after the last
ingress beat**. `obs_win_active` is gated on `obs_dut_busy` (`~snk_system_idle`),
which cannot assert until the DUT has already accepted traffic -- so ingress is
structurally guaranteed to start before the window it is supposed to be measured
in. Note there are TWO windows in the run (an earlier 1196-clock one from a prior
phase); an analysis that latches onto the first will read "no handshakes before
the window" and look like a refutation. It is not -- it is the wrong window.

*Correction:* an earlier draft of this task guessed the 190 was absorbed by
`SRAM_DEPTH=256`. The waveform does not support that. The bound is the dead-zone
DURATION (~111 clocks in this sim config), not a buffer depth; 190 is simply how
many beats fit in that gap in the 8-channel board configuration.

This is the same front-loading the OLD cocotb TB worked around by hand: it kicked,
waited for `snk_system_idle` to deassert, and only then started the generator,
with a comment explaining that this was what kept the sin window open. The board
never does that -- it stages and fires one atomic GO -- so the workaround hid a
real measurement defect for as long as sim and board ran different code.

**Not a datapath fault.** Every one of those 28 configs PASSED with golden CRCs.
The data always moved; only the ingress meter under-reports.

**FIXED 2026-09-23.** `s_axis` now has its own
measurement window (`obs_sin_win_active`) that opens at `obs_arm` -- the same
cycle `CSR_GO` pulses `cfg_gen_start`, so it is counting before the generator can
emit a beat -- and closes WITH the shared window, so `sin` and `wr` still describe
the same span end. The other three meters (`rd`, `wr`, `sout`) keep the shared
window untouched.

```
  sink, 4ch x 8 beats (32)      before          after
    sin   prod=0   starv=38   util=0.0%   ->  prod=32  starv=117  util=21.5%
    wr    prod=32  starv=6    util=84.2%  ->  prod=32  starv=6    util=84.2%   (identical)
  source
    rd    prod=32  starv=16   util=66.7%  ->  unchanged
    sout  prod=32  starv=16   util=66.7%  ->  unchanged
```

The arithmetic closes the loop: sin's new window is 32+117 = 149 cycles, the
shared window is 32+6 = 38, and 149-38 = **111** -- exactly the dead zone measured
off the waveform. Three independent routes (counter arithmetic across 6 transfer
sizes, the waveform, and the fix's effect) now agree.

**Caveat, deliberately accepted.** `sin` utilisation is now LOWER (21.5%, not the
84.2% `wr` shows) because the dead zone lands inside its window as starvation.
That is honest -- the ingress really is idle then -- but it means sink-ingress
numbers are NOT comparable with any run recorded before this change. `util =
prod/(prod+bp+starv)`, so the dead zone dilutes it; the beat COUNT is now correct,
which is what the meter was there to report.

Option rejected: opening the SHARED window at `obs_arm` would have fixed `sin`
in one line but moved `wr`/`rd`/`sout` too, invalidating every board number
recorded earlier in this session. The surgical split keeps them byte-identical.

**Do:**
- [x] Anchor the sink-ingress measurement to the stimulus rather than to
      `obs_dut_busy`. Done: dedicated window opened at `obs_arm`.
- [ ] Re-run `--suite --suite-beats 1,4,16,64,256` afterwards and assert
      `sin prod == wr prod` at every size. The bug is silent at small sizes
      today precisely because 0 looks like "no traffic" rather than "190 early".

**BOARD-CONFIRMED 2026-09-23.** Two sweeps on the fixed bitstream, 8 channels,
both backpressure modes, both seeds -- the same axes as the pre-fix baseline:

```
   beats  expect   sin BEFORE  short  |  sin AFTER  short
       1       8            0      8  |         8      0
       4      32       absent      -  |        32      0
      16     128            0    128  |       128      0
      64     512          322    190  |       512      0
     256    2048         1858    190  |      2048      0
    1024    8192         8002    190  |      8192      0
    4096   32768        32578    190  |     32768      0
```

Every shortfall is zero. The `beats=4` row had been dropped from the JSON
entirely (`engaged <= 0` left nothing to report); it now reads
`prod=32 starv=197 engaged=229 util=14.0%`.

**No collateral, checked rather than asserted:** all 21 `wr`/`rd`/`sout`
comparisons (7 sizes x 3 interfaces) are identical before and after in BOTH
`prod` and `starv`. That was the whole argument for splitting `sin` off instead
of moving the shared window, and it held.

Peak measured on the fixed build: **12.75 GB/s full-duplex of 12.8 GB/s** at
4096 beats (sink 6.36 + source 6.39).

**Cost, recorded because it is a trend and not a one-off:** post-route
WNS 1.041 -> **0.684 ns**, WHS **0.013 ns**, 0 failing endpoints of 201144;
+24 LUTs, +3 registers. Still positive and a thin positive WNS is this flow's
design point -- but that is two consecutive changes eating setup slack
(1.213 -> 1.041 -> 0.684), worth watching before the next one.

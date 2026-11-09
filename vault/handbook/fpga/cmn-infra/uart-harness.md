---
title: UART harness
summary: One host program against sim and silicon; transports differ, bytes do not.
---

# UART harness: sim + FPGA, one host program

The characterization pattern (ddr2_char, cdc_counter_display, stream_char,
rapids_char): the host program speaks a UART byte protocol to harness CSRs.
- SIM transport: `make_uart_channel(dut, clock, clks_per_bit)` from
  `bin/TBClasses/harness/cocotb_axil_bridge.py`, handed to
  `UARTAxiBridge(channel=...)`. A cocotb.function bridge, NOT a polling pump.
  The TB wraps the HARNESS with an injectable driver - not the clocking top -
  so co-prime/awkward clocks stay testable.
- FPGA transport: `UARTAxiBridge(port=...)`, the real serial port. Same bytes,
  same host code; `channel=` versus `port=` is the entire difference.
- Both halves already exist and are shared - see [[host-stack]] for the layer
  map. Write neither.
- All register access by name via the PeakRDL regmap
  ([[registers-by-name]] in dv/) - this is what guarantees sim and board
  cannot disagree about the address map.
- Sim equivalence is the point: run the SAME host program in sim first; it
  has caught real host bugs (clear_stats, data-mode CRC) before silicon.
- Sim config replicates the FPGA config EXACTLY (channels, presets,
  monitor sizing); shrink only transfer lengths for runtime.
Board-side mechanics: [[boards]].

## The anti-pattern: a private bridge in the testbench

**Never define a bridge class inside a testbench.** If sim reaches the DUT by
any path other than `UARTAxiBridge(channel=...)`, the equivalence property is
gone and nothing reports it - the sim still passes, it just stops being
evidence about the board.

What it cost (STREAM Genesys 2, found 2026-08-25). The cosim declared FOUR
byte-identical `_Bridge` classes inline in
`Genesys2/stream/dv/tbclasses/stream_harness_tb.py`, each wrapping
`cocotb.function(tb.uart_write/uart_read)`. Grepping that whole `dv/` tree for
`UARTAxiBridge`, `byte_channel`, `cocotb_axil_bridge`, `make_uart_channel` or
`TracingChannel` returned ZERO hits, while the file's own docstring claimed
"there is one transport class and no copy to drift". Two consequences:

- Those shims hook in at the REGISTER level, above the ASCII protocol, so the
  UART byte framing the board's host actually talks through was never
  exercised in simulation at all. A defect in that layer is structurally
  invisible: sim green, board dead, descriptors verifying fine in memory
  because they arrived by a different route than the board uses.
- With no `ByteChannel` there is no wire, so `TracingChannel` cannot record
  one, so the board-vs-sim byte diff - the entire reason the abstraction
  exists - was unavailable exactly when a board was moving zero beats.

The campaign layer had drifted the same way: eight board host programs import
`CharacterizationRunner` from the flow's shared `bin/characterization.py`; no
sim code imported it. The cosim reimplemented the campaigns inline, carrying
comments like "Match the FPGA characterization's first config exactly" - a
hand-maintained lookalike of the runner the board runs.

Same failure shape as [[one-source-config]] one layer up: a second
implementation beside a shared one, with nothing comparing them. The rule is
the same - inject the transport, run the ONE program.

## Instrumentation goes INSIDE the board's program, not around it

The board's program for a DMA campaign is `CharacterizationRunner.run_config`:
reset_stream, load_descriptors, configure_stream, setup_timer, kick, poll,
CRC. Its first step is `CTRL.SOFT_RESET`, and that reset reaches every
instrument: the in-core monitor CSRs, both observers and both tallies sit in
the `unit_aresetn` domain (pinned by `cocotb_test_soft_reset_scope`, written
after a board probe that wrote a register's own reset value "proved" config
survived). So there are exactly two places per-run instrumentation can go:

- `runner.mon_config = MonitorProgram(...)` (`bin/stream_monitors.py`) -- the
  in-core cone set, applied INSIDE `configure_stream()` after the reset,
  where the runner would otherwise program its own legacy defaults.
- `runner.run_config(cfg, pre_kick=fn)` -- everything else: monbus routing,
  address ranges, timeouts, the tally CAM, observer arming. Runs after
  configure_stream and before the kick.

What it cost (STREAM Genesys 2, 2026-09-08). Five mon-build host programs
each hand-rolled reset/configure/kick and carried their own monitor
programming; they disagreed on the packet mask (one allowed every type, which
admits the ~1.1M-packet perf stream, floods the group and wedged the UART),
on the ENABLE bit layout (hardcoded from a stale comment), and on the routing
(records sent to the capture memory while the tally was swept). Each
disagreement read as a monitor defect and the board was "broken" for a day.
The obs campaign, which called `run_config`, worked -- but its observer and
CAM writes went BEFORE the call, where the reset undid them; it was binning
on reset-default cones. One program, one hook, proven in the cosim first:
`test_stream_mon_compress` runs `bin/mon_compress.measure_compression` over
the sim channel, the same function `host_mon_compress.py` runs on the board.

### A board probe and a proxy drive the BOARD's beat width (granite TASK-003 item 6, 2026-10-29)

A read/write program carries an AXI beat size. The 64-bit builds made
`AXI_SIZE_8` the habit, and on the 128-bit host of the DFI 1:4 build every
8-byte beat is a legal NARROW transfer: the controller turns each one into
its own BL8 read of the same 16-byte line, two reads per line, and the
proxy's DFI probe counted "two valids per read" for an afternoon before the
host was suspected. The same habit in the board probe made the transaction
stride overlap (the "3-of-8 floor") the day before. Rule: the beat size and
the stride come from the build's `axi_data_width` (`build_info()` on the
board, `TEST_AXI_DATA_WIDTH` in the proxy), never from a constant; a narrow
beat is a test of its own (`TEST_AXI_SIZE`, granite TASK-007), not the
default stimulus.

### An ILA capture must not reprogram a levelled board

`capture_ila.tcl` programmed the ILA bitstream before arming, which resets
the FPGA: the read-path cell the host had just found (IDELAY tap, bitslip,
rddata_delay, DFI phase) was gone and the capture showed an unlevelled
read. `CAP_NO_PROGRAM=1` attaches and arms only; program once with `make
program BITSTREAM=.../ddr2_char_ila.bit`, level and set up over UART, then
capture. The granite 1:4 capture (`board75_dfi4ila/cap_rd.py`) is the
pattern: scan the cell, write under a "wr" trigger, read under a "rd"
trigger, decode both CSVs and diff the DFI words written against the DFI
words read, on both sides of the harness's `dfi_rddata_delay` -- that is
how the one wrong beat per read run became "the first device word of the
run, wrong on the PHY's own output" in one pass.

### The read-path pair follows the clock plan; the host derives it from the bitstream (granite ISSUE-002, 2026-11-09)

The a7ddrphy presents a read's data a fixed number of nanoseconds after the
command (CL, flight time, ISERDES capture) and asserts `rddata_valid` a fixed
number of sys cycles after `rddata_en`. Which sys cycle the data lands in
therefore depends on the sys period, and the harness's `rddata_delay` has to
move with it: `t_rddata_en + 1` at 50 / 66.67 / 75 MHz, `t_rddata_en + 0` at
100 MHz (DDR2-400). Both values were measured by joint board sweeps
(bring-up 2026-07-21, pumice ISSUE-012 / ISSUE-015; granite TASK-003
2026-10-29). Bitslip and IDELAY tap cannot recover a whole-cycle
misplacement, so with the wrong pair the leveling sweep probes all 8 x 32
cells and finds no eye, every read mismatches, and the log says "analog read
path not recoverable" -- which reads as a hardware fault.

For six weeks the 100 MHz pair lived in three environment variables
(`TEST_T_PHY_WRLAT=1 TEST_T_RDDATA_EN=1 TEST_RDDATA_DELAY=1`, plus
`PUMICE_MC_CLK_HZ=100000000` for the JEDEC derivation) that every 100 MHz run
had to export, recorded in one task log. On 2026-11-09 a session that did not
know ran every 100 MHz bitstream it had without them, saw five placements
fail identically while 75 MHz and LiteDRAM passed, and filed the design
(granite ISSUE-002) with a day's matrix behind it. The "source-identical
rebuild of the 2026-11-02 design" in that matrix was not one either: the
worktree build sourced the MAIN tree's `env_python`, so `REPO_ROOT` and every
`$REPO_ROOT` in the filelists pointed at HEAD -- 566 of 749 sources came from
the wrong tree. Source the worktree's own `env_python` and count the paths
in the build log before calling a worktree build an A/B.

Rules, all in the host now:

- **The pair is derived from the bitstream.** `DDR2CharDriver.clk_mhz()`
  reads `BUILD_CLK_HZ` (the harness's own `FPGA_CLK_HZ`, the constant its
  UART divisor is built from); `ddr2_char.read_path_offset(clk_mhz)` is the
  measured table; `SimpleTest`, `A7Leveling` and `pumice_char.
  ControllerConfig` default `rddata_delay` to `t_rddata_en + offset`, and
  `ControllerConfig.mc_clk_hz` to the same register. The `TEST_*` and
  `PUMICE_MC_CLK_HZ` variables still pin a value; they are overrides for an
  experiment, never the way a board point is configured.
- **Leveling verifies the pair and searches when it is wrong.**
  `A7Leveling.run` sweeps at the derived `rddata_delay` first and, finding no
  eye, at the other offsets (0, 1, 2 above `t_rddata_en`); an eye found off
  the table is reported in the result and on the console with the clock, so
  the table gets extended instead of the environment. The level cache carries
  the pair the eye belongs to.
- **The JEDEC timings are programmed after every soft reset, from the same
  clock.** `soft_reset` reverts the controller CSRs to the RTL resets, which
  are not a board configuration (tREFI 1950 cycles is 19.5 us at 100 MHz,
  2.5x JEDEC's 7.8 us; tRTW 6 is under the read window). The smoke init and
  the leveling sweep used to run on them; `jedec_for_read_path` derives the
  set once and `SimpleTest.init`, `reinit_datapath` and `A7Leveling._reinit`
  write it each time.
- **`[init]` logs what it ran with**: the pair, its offset, whether leveling
  moved it, and the timings. A failing run then records its configuration,
  and "no eye" with `offset 1 at 100.00 MHz` in the line above it is a host
  bug, not a board one.

The general form: a value the host needs that is a property of the BITSTREAM
(its clock, its DFI rate, its beat width) is read from the bitstream's own
registers, never carried in the environment of the shell that happens to run
it. The beat-width rule two sections up is the same rule.

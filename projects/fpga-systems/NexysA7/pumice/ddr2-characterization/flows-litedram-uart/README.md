# flows-litedram-uart — LiteDRAM DDR2 comparison flavor

The pumice `build-perf` characterization harness with **LiteDRAM's DDR2
controller** behind the AXI port instead of pumice. Same UART bridge, same
generated address bridge, same `harness_csr`, same `char_engine_block`
(chargen_regs + generator array + perf meters + latency histograms), same
host program and CSV. Only the controller differs, so a number from here and a
number from `build-perf` are directly comparable.

## Layout

```
litedram_hp.yml            LiteDRAM core config: MT47H64M16 x16, A7DDRPHY,
                           75 MHz sys / 1:2 / DDR2-300 (== pumice PUMICE_SYS_75),
                           cmd_buffer_depth 16, one 64b/id8 AXI user port
regen.sh                   regenerate the core; --bios bakes the self-init BIOS in
gen/board/gateware/      litedram_core.v (+ vendored VexRiscv.v) -- Vivado only
rtl/char_engine_harness.sv build-perf's ddr2_char_harness minus pumice:
                             uart_axil_bridge -> bridge_ddr2_char_axil ->
                             {harness_csr, debug_sram, dfi_mon_ram, chargen_apb ->
                              char_engine_block -> m_axi}, timer, LEDs
rtl/litedram_char_top.sv   pins: litedram_core (own PLL/PHY/init) + the harness
                           on user_clk, m_axi -> user_port_axi_0
rtl/filelists/
  litedram_char_harness.f  lint closure (verilator): everything but the core
  litedram_char_board.f    board build: harness.f + top + litedram_core.v
constraints/litedram_char.xdc   Nexys A7 pins (the regenerated core xdc has none)
tcl/build_all.tcl          non-project Vivado flow over litedram_char_board.f
host/host_litedram_char.py the pumice host (build-perf/host) with the pumice
                           CSR surface turned into no-ops; same suites, same CSV
Makefile                   variables only; flow logic is make/fpga_flow.mk
```

## Address map and identity

Identical to `build-perf` because it is the same `bridge_ddr2_char_axil`:
`ddr2_apb` (pumice CSR, **terminated** here: PREADY=1, reads 0),
`harness_csr`, `debug_sram`, `dfi_mon_ram`, `obs_apb` (terminated),
`chargen_apb` -> `char_engine_block`. `harness_csr.BUILD_ID` reads `"LDR2"`
(0x4C445232) instead of `"DDR2"` so a host can tell which controller it is
talking to; the `BUILD_*` geometry words report DFI rate 2, BL4, 13 row bits,
32b DRAM beat, x16 device.

## Build / program / run

```
make regen                     # ./regen.sh --bios (LiteX venv + riscv-gcc)
make lint                      # verilator --lint-only char_engine_harness
make bitstream                 # Vivado; bitstream/litedram_char.bit + reports/
make program                   # JTAG via the board registry (fpga_board.py)
make host-litedram_char ARGS="--status"
make host-litedram_char ARGS="--char-profile matrix --char-scale 1000 \
                              --csv ../char_results/litedram_<date>.csv"
```

`--char-profile` takes a `pumice_char` run profile and uses its scenario
half only; the pumice config presets mean nothing to LiteDRAM, so every
record is tagged `litedram`. The host waits on `STATUS.init_done`
(`litedram_core.init_done`, asserted by the BIOS after calibration) before
launching generators, as it waits on pumice's init.

## What LiteDRAM does not have

- No controller CSRs: paging / scheduling / refresh sweeps are pumice-only.
  LiteDRAM runs whatever `litedram_hp.yml` generated (ROW_BANK_COL, open page
  with lookahead auto-precharge, per-bank machines with round-robin).
- No host leveling: the BIOS calibrates the a7ddrphy itself.
- `CTRL.soft_reset` re-arms the generators only; the user port has no reset
  input into the core.

## Results

**Post-fix re-run (2026-10-03), the current A/B:** both images rebuilt from one
commit on the post-sdpram-fix tree (`amba 71d48b6f7`; pumice `build-perf` WNS
+0.132 ns, this flow WNS +0.321 ns, both timing-clean).
`char_results/litedram_2026-10-03_matrix.csv` (14/14 integrity) against pumice
`build-perf/reports/char_postfix_2026-10-03.csv` (84/84 integrity), full
analysis in
`projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2/docs/char_results/FINDINGS_litedram_ab_2026-10-03.md`:
pumice `open_page` now **matches LiteDRAM on every page-friendly pattern**
(writes 569-570 both, reads 561-579 both, ld/pum 1.00-1.01x — the "reads 2x"
gap below was the pre-ring-fix state). LiteDRAM still leads same-bank row
thrash 1.6-2.5x; pumice still leads bank-interleaved BL4 (0.78x). The LiteDRAM
side is unchanged from the 2026-09-10 baseline within rebuild noise — 13 of
14 rows within 25 read-cycles, worst row 0.22%: the sdpram fix does not touch
this datapath.

**Original run (2026-09-10, timing-clean build, WNS +0.195 ns, 35% LUTs):**
`docs/char_results/litedram_2026-09-10_matrix.csv` and
`FINDINGS_litedram_ab_2026-09-10.md` (under the pumice component docs).
Streaming reads 564-579 MB/s and writes 554-569 MB/s at BL4 / 75 MHz / 1:2,
14/14 integrity. Against pumice `open_page` on the same harness: writes equal,
reads 2x (pumice 291.7), read latency 24.7 vs 49.2 cycles. Concurrent
both-directions points date from this run; both sides re-measured post-fix
2026-10-04 (`char_results/litedram_concurrent_2026-10-04.csv`,
`litedram_multigen_2026-10-04.csv` — 285.8 MB/s total 1+1 normalized to 75 MHz,
reproducing 09-10's 285.6; pumice's side `build-perf/reports/concurrent_postfix_2026-10-04.csv`,
571.1 MB/s total, the 2.00x stands; full table in the addendum to
FINDINGS_litedram_ab_2026-10-03.md).

## History

- 2026-09-10 (later): first measured A/B. Build needed the core's CRG
  reset-strobe false path (the standalone core xdc only covers its
  ars_ff/mr_ff synchronisers) and the harness reset-sync patterns needed a
  leading wildcard; both in `constraints/litedram_char.xdc`.
- 2026-09-10: harness rewired onto the shared `char_engine_block` (extracted
  from `ddr2_char_macro` so both flows instantiate one spine); Makefile moved
  onto `make/fpga_flow.mk`; `FPGA_CLK_HZ` corrected 100 -> 75 MHz (the UART
  divisor had been wrong for the 75 MHz regen). Earlier that day: core
  regenerated with a BIOS at 75 MHz / 1:2, five flow bugs fixed
  (`HARNESS_PLAN.md`). LiteDRAM's own BIST at this point (2026-09-06):
  WR 504/475 MiB/s, RD 184/270 MiB/s (bl8/bl16).

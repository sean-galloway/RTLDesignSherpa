# DDR2/LPDDR2 Memory Controller — Nexys A7 Characterization

**Status:** Built and measured. The harness, the board bring-up and the
workload characterization are all done; this directory holds the LiteDRAM
comparison flow and the measured results.

**System documentation:** [`../docs/pumice_fpga_system/`](../docs/pumice_fpga_system/)
— the chaptered book for this system: the board, every block around the
controller and why it is shaped that way, the five targets built from one
harness source, and the measurement flow.

---

## What is where

| Path | What |
|---|---|
| [`../build-perf/`](../build-perf/) | the measurement build: harness top, Vivado flow, host programs, results |
| [`../ddr2_char_framework/`](../ddr2_char_framework/) | the harness RTL, shared by every target, plus the cocotb/verilator twin |
| [`flows-litedram-uart/`](flows-litedram-uart/) | the A/B reference: LiteDRAM's DDR2 controller behind the same harness |
| [`char_results/`](char_results/) | measured CSVs, soak logs and dated findings pages |
| [`docs/ddr2_char_guide/`](docs/ddr2_char_guide/) | the older operator guide (v0.90) |

The controller under test lives at
[`projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2/`](../../../../components/mem-ctrl-ip/pumice-ddr2-lpddr2/),
with its own HAS and MAS in that component's `docs/`.

---

## Validation methodology

DFI v2.1 is the boundary between the controller and the DRAM PHY. The PHY itself
— IOB serdes, bitslip, IDELAY tap calibration — is FPGA-specific and out of
scope for the controller family, so this project reuses LiteDRAM's `a7ddrphy`
verbatim and drives its DFI master port from pumice.

That is the same boundary the DV repo's DFI BFM drives in simulation, which is
the point: code that passes in cocotb against the BFM should pass on hardware
against the PHY, modulo PHY-side training. The training is a host job — there is
no hardware leveling FSM — and it is covered in the system book.

Multi-rank (`NUM_RANKS` in {1, 2, 4}) is not exercised here: the onboard DDR2 is
single-rank by construction. Multi-rank validation needs a board with a DIMM
socket.

No CPU runs on the FPGA. The 100T cannot fit the controller, the perf logic and
a soft CPU with any timing margin, so the host runs off-board over the UART.
An earlier plan had VexRiscv and Linux on LiteX; it was dropped on that budget.
LiteDRAM's own flow still vendors a `VexRiscv.v`, because its self-init BIOS
needs one — that is LiteDRAM's CPU, not ours.

---

## Results

Measured numbers live in [`char_results/`](char_results/) and
[`../build-perf/results/`](../build-perf/results/) — dated findings pages beside
the CSVs and soak logs they came from. Synthesis and timing reports for the
measurement build are under
[`../build-perf/fpga/reports/`](../build-perf/fpga/reports/); read those rather
than any estimate, which is why the pre-RTL resource-budget table that used to
sit here is gone.

**Note on reading old findings:** the read path was rebuilt after several of
these pages were written (`rd_intake` admit gate plus a deeper return ring), and
the board design point moved to 75 MHz. A findings page states its own date and
configuration; check both before comparing it against a current run.

---

## Decision Log

- **2026-06-15** — Original DDR2 bring-up plan recorded under
  `projects/NexysA7/pumice-memory-controller/`. Validation methodology (DFI
  controller + LiteDRAM `a7ddrphy`), CPU choice (VexRiscv Linux on LiteX), and
  three-sub-phase hardware bring-up agreed. At that date the controller was
  pre-RTL (HAS v0.2, MAS v0.1).
- **2026-06-25** — Directory renamed `pumice-memory-controller/` →
  `ddr2-characterization/`. Harness architecture recorded: reuse
  `dma_address_gen`, the stream CRC block, `harness_csr` and the LED/7-seg
  drivers; author two new master-side blocks, `axi4_master_wr_injector` and
  `axi4_master_rd_crc_check`, by adapting stream's slave-side equivalents.
- **2026-09-10** — The DUT-agnostic half of `ddr2_char_macro` (chargen regs,
  generator arrays, perf taps) extracted into
  `ddr2_char_framework/rtl/char_engine_block.sv`; the macro now wraps it around
  pumice, and `flows-litedram-uart/rtl/char_engine_harness.sv` is `build-perf`'s
  harness minus the controller on the same block and the same bridge address
  map, so the LiteDRAM A/B measures through identical RTL (pumice TASK-027).
- **2026-09-29** — This README reduced to a pointer. It had carried
  "**Status:** Skeleton — directories scaffolded, harness RTL not yet written"
  since June, along with a phase table calling hardware bring-up "Future" and
  characterization "Skeleton (directory + plan only)", a "what we need to build"
  harness section and a "TBD" host. All of it was false by the whole of
  `build-perf`. The live content moved to the system book; the log stays here.

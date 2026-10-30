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
[`projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/`](../../../../components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/),
with its own HAS and MAS in that component's `docs/`.

---

## Pattern legend (what each name means)

The names in every `char_results/*.csv` and in `pumice_char.py`'s profiles,
in plain words. The aggregation (half-burst) families are the `half_*` rows.

**Families** are what one injector walks. The DRAM is x16, a burst is BL8 =
16 bytes, a page (row) is 2 KB, eight banks.

| name | what the injector does | what it measures |
|---|---|---|
| `incremental` | linear march, one burst after the next, across columns, then banks, then rows | the best-case stream |
| `row_major` | the same march wrapped inside ONE page | every burst a page hit: pure column throughput |
| `col_major` | stride = one row, same bank | every burst a page miss: PRE + ACT each time, the tRC / tRP floor |
| `col_major_interleaved` | stride = one bank | every burst a new bank, activates pipeline: bank parallelism |
| `random` | an LFSR walk inside a region (two rows x all banks per thread) | mixed hits and misses, no order |
| `row_thrash` | one bank, two rows, a burst to each in turn | the row-buffer conflict a scheduling window can reorder |
| `mixed` | bank-paired threads one row apart, reads and writes at once | read/write turnaround under row conflicts |
| `half_pair` | **aggregation**: every DRAM burst issued as TWO half-width host transactions, low half then high half, back to back: l0 h0 l1 h1 ... | whether the controller merges a pair into one burst (a combiner does; without one each half costs a full burst) |
| `half_oct` | the same halves, but all eight low halves then the eight high halves: l0..l7 h0..h7 | the merge window has to hold eight transactions |
| `half_pair_sweep`, `half_oct_sweep` | as above, with the idle gap after each transaction looping 0,1,..7 clocks inside the run | the merge window against arrival spacing, averaged |

**Scenario suffixes**: `_bl4` / `_bl8` / `_bl16` = host transaction length in
beats (AxLEN+1), i.e. DRAM bursts per transaction; `_multiid` = AXI IDs from
an LFSR (out-of-order allowed) instead of a counter; `_gap` = 8 idle clocks
between transactions; `_thrN` = N injectors at once, each in its own
region (the board builds have four, so 5..8 run as four and say so);
`_gapN` = a FIXED N idle clocks between transactions (the `half_gap`
profile: 512 pairs per cell).

**Presets** (the controller's config for a run): `open_page` = row-major
address map (column, bank, row from the low bits up), pages left open;
`close_page` = the same map, every access auto-closes its page;
`bank_interleave` = bank bits below the column, so consecutive bursts hop
banks (close-page policy); `defaults` = the controller's reset state.
LiteDRAM has one config (row/bank/col, open page with auto-precharge).

**Profiles** (which cells a run covers): `every` = the four stream families
x bl 4/8/16 + the multiid and gap variants x three presets; `windows` =
mixed, row_thrash and random on four injectors at bl8 under open and close
page; `half_threads`
= pair and oct at 1..8 threads; `half_burst` = pair, oct and their sweeps
on one thread; `half_burst8` = the same on eight; `half_gap` = the pair walk
at fixed gaps 0..7; `concurrent` = one writer and one reader at once per
family; `multigen` = one writer and two readers.

**Numbers**: write / read MB/s = bytes moved over the pass's cycles at the
harness clock; peak is 600 MB/s at 75 MHz (DDR2-300 x16) and 800 at 100
(DDR2-400). "merges 512/1024 (ratio 0.5)" means every pair merged.

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

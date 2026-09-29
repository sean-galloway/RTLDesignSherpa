<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Resource Estimates

Unlike the theoretical throughput and latency numbers above, the resource figures
here are **measured** from the actual place-and-route of the characterization
build (`rapids_char_harness` wrapping `rapids_beats_top`) on the Nexys A7-100T.

## FPGA Resource Summary

Measured, post-implementation (Vivado 2025.1, `xc7a100t-csg324-1`, 100 MHz,
characterization build: `NUM_CHANNELS = 4`, `DATA_WIDTH = 512`,
`ADDR_WIDTH = 64`, `APB_ADDR_WIDTH = 13`):

| Resource | Used | Available | Utilization |
|----------|------|-----------|-------------|
| Slice LUTs | 37,555 | 63,400 | 59.24% |
| -- LUT as Logic | 30,205 | 63,400 | 47.64% |
| -- LUT as Memory | 7,350 | 19,000 | 38.68% |
| Slice Registers (FF) | 28,683 | 126,800 | 22.62% |
| Block RAM Tile | 22 | 135 | 16.30% |
| -- RAMB36 | 20 | 135 | -- |
| -- RAMB18 | 4 | 270 | -- |
| DSP48E1 | 0 | 240 | 0% |

**Timing:** all user-specified timing constraints met at 100 MHz (positive slack)
-- the harness plus DUT close cleanly on the -1 speed grade part.

The characterization build uses 4 channels (sink + source) to fit the harness
(BRAM SRAM buffers, golden-CRC checkers, UART bridge) comfortably on the 100T.
The design parameter default is `NUM_CHANNELS = 8`; an 8-channel build roughly
scales the per-channel SRAM/scheduler logic and would target a larger part.

---

## Resource Breakdown by Block

Approximate distribution of the DUT logic (excludes the char harness's UART/CRC
scaffolding). Both a sink and a source instance are present; they do not share
logic.

### APB Configuration Slave + Register Block

- LUTs: ~1.5K
- FFs: ~2K
- Function: APB decode, PeakRDL `rapids_regs` block (config + monitor regfile
  @ 0x1000), `rapids_config_block` hwif fan-out.

### Scheduler Group (per direction)

- LUTs: ~3-4K per direction
- FFs: ~3K per direction
- Function: `scheduler_beats` (three-opcode: DATA / CTRL_READ / CTRL_WRITE),
  `descriptor_engine_beats` (256-bit fetch/parse + prefetch), channel arbitration.

### Control Engines (per direction)

- LUTs: ~0.5K per direction
- FFs: ~0.5K per direction
- Function: `ctrlrd_engine` (poll-until-match, retry budget) and `ctrlwr_engine`
  (single-beat doorbell write). Small -- one AXI read/write state machine each.

### AXI Read / Write Engines

- LUTs: ~2-3K each
- FFs: ~2-3K each
- Function: 512-bit streaming AXI masters (source read, sink write) with
  beat-level completion.

### SRAM Buffers (sink + source)

- BRAM: dominant BRAM consumer (20x RAMB36 + 4x RAMB18)
- Function: per-channel sink and source data buffers decoupling network and
  memory ends. BRAM scales with `SRAM_DEPTH` x `NUM_CHANNELS` x 2 directions.

### MonBus / AXI Monitors (USE_AXI_MONITORS)

- LUTs: ~1-2K
- FFs: ~1-2K
- Function: rd/wr AXI monitors feeding the MonBus AXI-Lite group (error-drain +
  capture master), monitor perf windows @ 0x1000.

---

## SRAM Sizing

BRAM is the primary scaling resource. Each direction has its own per-channel
buffer, so total BRAM ~= `2 x NUM_CHANNELS x ceil(SRAM_DEPTH x DATA_WIDTH / BRAM_bits)`.
For the 4-channel char build this lands at 22 BRAM tiles (16.30% of the 100T).
Deeper buffers improve small-transfer efficiency (Section 6.1) at the cost of
BRAM; wider `NUM_CHANNELS` multiplies both scheduler logic and BRAM.

---

## Scaling Notes

| Change | LUT/FF impact | BRAM impact |
|--------|---------------|-------------|
| `NUM_CHANNELS` 4 -> 8 | ~+scheduler/arbiter per channel | ~2x buffer tiles |
| `SRAM_DEPTH` deeper | minimal | +tiles per direction |
| `USE_AXI_MONITORS` off | -1-2K LUT/FF | none |
| `DATA_WIDTH` 512 -> 256 | ~half datapath LUT/FF | ~half buffer width |

DSP usage is zero -- RAPIDS Beats is pure control + datapath movement, no
arithmetic multiply/accumulate.

---

**Last Updated:** 2026-07-13

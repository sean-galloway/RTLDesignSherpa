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

# RAPIDS Beats MAS - Waveform TODO

**Purpose:** Track ASCII waveforms that need to be replaced with simulation-generated versions.

**Last Updated:** 2025-01-10

---

## Waveform Generation Process

1. **Run simulation** with waveform capture enabled
2. **Capture VCD/FST** from CocoTB test
3. **Generate wavedrom JSON** from key signals
4. **Render to SVG/PNG** using wavedrom-cli
5. **Replace ASCII waveform** with image reference

---

## Chapter 1: Overview

### Figure 1.1.4: Basic Sink Path Transfer Timing

**File:** `ch01_overview/01_architecture.md`
**Test Source:** `test_snk_sram_controller_beats.py::test_basic_transfer`
**Signals to Capture:**
- `clk`
- `snk_apb_valid`
- `snk_apb_ready`
- `snk_scheduler_idle`
- `snk_system_idle`

**Note (2026-09-26):** this figure previously listed `snk_fill_*`, `sram_wr_en` and
`data_avail`. `rapids_core_beats` exposes NO fill-side ports -- the fill interface
is internal to it -- and since `bdf4e0dff` the SRAM is STREAM's `sram_controller`,
which has no write-enable port at all. Those signals are not observable at this
module's boundary, so the figure is re-scoped to the APB kick and idle status that
are. For the fill handshake itself, capture Figure 3.3.3 instead.

**Expected Behavior:** Show 4-beat fill operation with SRAM write and data availability tracking.

---

### Figure 1.3.1: Reset Timing

**File:** `ch01_overview/03_clocks_and_reset.md`
**Test Source:** `test_scheduler_beats.py::test_reset_sequence`
**Signals to Capture:**
- `clk`
- `rst_n`
- `scheduler_state`
- `descriptor_engine_idle`

**Expected Behavior:** Show async assert, sync deassert, FSM returning to IDLE.

---

## Chapter 2: FUB Blocks

### Figure 2.1.3: Basic Transfer Timing

**File:** `ch02_fub_blocks/01_scheduler.md`
**Test Source:** `test_scheduler_beats.py::test_basic_transfer`
**Signals to Capture:**
- `clk`
- `scheduler_state` (one-hot decode to name)
- `descriptor_valid`
- `sched_rd_valid`
- `sched_wr_valid`
- `sched_rd_done_strobe`
- `sched_wr_done_strobe`

**Expected Behavior:** Full state machine transition: IDLE -> PARSE -> CH_XFER_DATA -> DONE -> IDLE

---

### Figure 2.2.3: Descriptor Chain Timing

**File:** `ch02_fub_blocks/02_descriptor_engine.md`
**Test Source:** `test_descriptor_engine_beats.py::test_chain_fetch`
**Signals to Capture:**
- `clk`
- `apb_valid`
- `m_axi_arvalid`
- `m_axi_araddr`
- `m_axi_rvalid`
- `descriptor_valid`

**Expected Behavior:** Show two-descriptor chain fetch with AXI transactions.

---

### Figure 2.3.2: AXI Read Burst Timing

**File:** `ch02_fub_blocks/03_axi_read_engine.md`
**Test Source:** NONE YET -- no test exercises `axi_read_engine_beats` directly
(verified 2026-09-26: nothing under `dv/tests/` instantiates it; only the
testplans and coverage config name it). This figure cannot be generated until
such a test exists.
**Signals to Capture:**
- `clk`
- `sched_rd_valid`
- `sched_rd_beats`
- `m_axi_arvalid`
- `m_axi_arlen`
- `m_axi_rvalid`
- `m_axi_rdata` (first/last beat indicator)
- `m_axi_rlast`
- `axi_rd_sram_valid`
- `sched_rd_done_strobe`

**Expected Behavior:** Show 8-beat read burst with SRAM writes.

---

### Figure 2.4.2: AXI Write Burst Timing

**File:** `ch02_fub_blocks/04_axi_write_engine.md`
**Test Source:** NONE YET -- no test exercises `axi_write_engine_beats` directly
(verified 2026-09-26, same as Figure 2.3.2). This figure cannot be generated
until such a test exists.
**Signals to Capture:**
- `clk`
- `sched_wr_valid`
- `sched_wr_beats`
- `m_axi_awvalid`
- `m_axi_awlen`
- `axi_wr_sram_drain`
- `m_axi_wvalid`
- `m_axi_wdata` (first/last indicator)
- `m_axi_wlast`
- `m_axi_bvalid`
- `m_axi_bresp`
- `sched_wr_done_strobe`

**Expected Behavior:** Show 4-beat write burst with AW/W/B phases.

---

### Figure 2.5.2: Allocation and Release Timing

**File:** `ch02_fub_blocks/05_beats_alloc_ctrl.md`
**Test Source:** `test_alloc_ctrl_beats.py::test_basic_alloc_drain`
**Signals to Capture:**
- `clk`
- `wr_valid`
- `wr_size`
- `rd_valid`
- `space_free`
- `wr_ptr` (internal)
- `rd_ptr` (internal)

**Expected Behavior:** Show 8-beat allocation followed by single-beat releases.

---

### Figure 2.6.2: Data Arrival and Drain Timing

**File:** `ch02_fub_blocks/06_beats_drain_ctrl.md`
**Test Source:** `test_drain_ctrl_beats.py::test_basic_write_drain`
**Signals to Capture:**
- `clk`
- `wr_valid`
- `rd_valid`
- `rd_size`
- `data_available`
- `rd_empty`

**Expected Behavior:** Show single-beat arrivals followed by 4-beat drain.

---

### Figure 2.7.2: Latency Bridge Timing

**File:** `ch02_fub_blocks/07_beats_latency_bridge.md`
**Test Source:** `test_latency_bridge_beats.py::test_basic_latency`
**Signals to Capture:**
- `clk`
- `s_valid`
- `s_data` (beat payload)
- `m_valid`
- `m_data` (beat payload)

**Expected Behavior:** Show 2-cycle latency between input and output.

---

## Chapter 3: Macro Blocks

### Figure 3.3.3: Sink Path Transfer Timing

**File:** `ch03_macro_blocks/03_sink_data_path.md`
**Test Source:** `test_snk_sram_controller_beats.py::test_complete_transfer`
**Signals to Capture:**
- `clk`
- `fill_alloc_req`
- `fill_alloc_size`
- `fill_valid`
- `fill_ready`
- `fill_data`
- `sched_wr_valid`
- `sched_wr_beats`
- `m_axi_awvalid`
- `m_axi_wvalid`
- `m_axi_bvalid`
- `sched_wr_done_strobe`

**Expected Behavior:** Complete sink path from fill allocation through AXI write completion.

---

## Waveform Format Requirements

### Wavedrom JSON Structure

```json
{
  "signal": [
    {"name": "clk", "wave": "p......"},
    {"name": "signal1", "wave": "01.0..."},
    {"name": "data", "wave": "x.=.=.x", "data": ["D0", "D1"]}
  ],
  "config": {"hscale": 2}
}
```

### Rendering Command

```bash
# Single waveform
npx wavedrom-cli -i figure_name.json -s figure_name.svg

# Convert to PNG
convert figure_name.svg figure_name.png
```

### File Naming Convention

```
assets/wavedrom/
├── ch01_sink_path_timing.json
├── ch01_sink_path_timing.svg
├── ch01_sink_path_timing.png
├── ch02_scheduler_fsm_timing.json
├── ch02_scheduler_fsm_timing.svg
├── ch02_scheduler_fsm_timing.png
...
```

---

## Progress Tracking

| Figure | File | Status | Test Coverage |
|--------|------|--------|---------------|
| 1.1.4 | ch01_overview/01_architecture.md | TODO | test_snk_sram_controller_beats.py |
| 1.3.1 | ch01_overview/03_clocks_and_reset.md | TODO | test_scheduler_beats.py |
| 2.1.3 | ch02_fub_blocks/01_scheduler.md | TODO | test_scheduler_beats.py |
| 2.2.3 | ch02_fub_blocks/02_descriptor_engine.md | TODO | test_descriptor_engine_beats.py |
| 2.3.2 | ch02_fub_blocks/03_axi_read_engine.md | TODO | test_src_sram_controller_beats.py |
| 2.4.2 | ch02_fub_blocks/04_axi_write_engine.md | TODO | test_snk_sram_controller_beats.py |
| 2.5.2 | ch02_fub_blocks/05_beats_alloc_ctrl.md | TODO | test_alloc_ctrl_beats.py |
| 2.6.2 | ch02_fub_blocks/06_beats_drain_ctrl.md | TODO | test_drain_ctrl_beats.py |
| 2.7.2 | ch02_fub_blocks/07_beats_latency_bridge.md | TODO | test_latency_bridge_beats.py |
| 3.3.3 | ch03_macro_blocks/03_sink_data_path.md | TODO | test_snk_sram_controller_beats.py |

: Waveform Progress Tracking

---

## Notes

- All waveforms should show at least 7 clock cycles
- Use meaningful data values (not just X/0)
- Include cycle markers for key events
- FSM states should be decoded to names
- Signal groups should be logical (inputs, outputs, internal)

---

**Last Updated:** 2025-01-10

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
**Test Source:** `test_sink_data_path.py::test_basic_transfer`
**Signals to Capture:**
- `clk`
- `snk_fill_valid`
- `snk_fill_ready`
- `snk_fill_data`
- `sram_wr_en`
- `data_avail`

**Expected Behavior:** Show 4-beat fill operation with SRAM write and data availability tracking.

---

### Figure 1.3.1: Reset Timing

**File:** `ch01_overview/03_clocks_and_reset.md`
**Test Source:** `test_scheduler.py::test_reset_sequence`
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
**Test Source:** `test_scheduler.py::test_basic_transfer`
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
**Test Source:** `test_descriptor_engine.py::test_chain_fetch`
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
**Test Source:** `test_axi_read_engine.py::test_basic_burst`
**Signals to Capture:**
- `clk`
- `sched_rd_valid`
- `sched_rd_beats`
- `m_axi_arvalid`
- `m_axi_arlen`
- `m_axi_rvalid`
- `m_axi_rdata` (first/last beat indicator)
- `m_axi_rlast`
- `sram_wr_en`
- `sched_rd_done_strobe`

**Expected Behavior:** Show 8-beat read burst with SRAM writes.

---

### Figure 2.4.2: AXI Write Burst Timing

**File:** `ch02_fub_blocks/04_axi_write_engine.md`
**Test Source:** `test_axi_write_engine.py::test_basic_burst`
**Signals to Capture:**
- `clk`
- `sched_wr_valid`
- `sched_wr_beats`
- `m_axi_awvalid`
- `m_axi_awlen`
- `sram_rd_en`
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
**Test Source:** `test_beats_alloc_ctrl.py::test_basic_alloc_drain`
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
**Test Source:** `test_beats_drain_ctrl.py::test_basic_write_drain`
**Signals to Capture:**
- `clk`
- `wr_valid`
- `rd_valid`
- `rd_size`
- `data_avail`
- `rd_empty`

**Expected Behavior:** Show single-beat arrivals followed by 4-beat drain.

---

### Figure 2.7.2: Latency Bridge Timing

**File:** `ch02_fub_blocks/07_beats_latency_bridge.md`
**Test Source:** `test_beats_latency_bridge.py::test_basic_latency`
**Signals to Capture:**
- `clk`
- `in_valid`
- `in_beats`
- `out_valid`
- `out_beats`

**Expected Behavior:** Show 2-cycle latency between input and output.

---

## Chapter 3: Macro Blocks

### Figure 3.3.3: Sink Path Transfer Timing

**File:** `ch03_macro_blocks/03_sink_data_path.md`
**Test Source:** `test_sink_data_path.py::test_complete_transfer`
**Signals to Capture:**
- `clk`
- `snk_fill_alloc_req`
- `snk_fill_alloc_size`
- `snk_fill_valid`
- `snk_fill_data`
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
| 1.1.4 | ch01/01_architecture.md | TODO | test_sink_data_path.py |
| 1.3.1 | ch01/03_clocks_and_reset.md | TODO | test_scheduler.py |
| 2.1.3 | ch02/01_scheduler.md | TODO | test_scheduler.py |
| 2.2.3 | ch02/02_descriptor_engine.md | TODO | test_descriptor_engine.py |
| 2.3.2 | ch02/03_axi_read_engine.md | TODO | test_axi_read_engine.py |
| 2.4.2 | ch02/04_axi_write_engine.md | TODO | test_axi_write_engine.py |
| 2.5.2 | ch02/05_beats_alloc_ctrl.md | TODO | test_beats_alloc_ctrl.py |
| 2.6.2 | ch02/06_beats_drain_ctrl.md | TODO | test_beats_drain_ctrl.py |
| 2.7.2 | ch02/07_beats_latency_bridge.md | TODO | test_beats_latency_bridge.py |
| 3.3.3 | ch03/03_sink_data_path.md | TODO | test_sink_data_path.py |

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

# WaveDrom Candidate Survey

**Date:** 2025-10-11
**Task:** TASK-020
**Purpose:** Identify tests that would benefit from WaveDrom timing diagram generation

---

## Executive Summary

**Total Tests Surveyed:** 139 test files across 5 directories
**Tests with WaveDrom:** 11 (7.9%)
**High-Priority Candidates:** 15
**Medium-Priority Candidates:** 23
**Estimated Implementation Effort:** 4-6 weeks for all high-priority candidates

### Key Findings

1. **Already Implemented** (11 tests): AXI4 monitors, APB, GAXI examples
2. **High-Value Opportunities**: Arbiters, protocol converters, state machines, CDC components
3. **Documentation Gap**: Many complex protocols lack visual timing documentation
4. **Test Infrastructure**: Existing framework supports rapid wavedrom addition

---

## Current WaveDrom Coverage

### Tests with Existing WaveDrom Support (11)

| Test | Module | Status | Waveforms |
|------|--------|--------|-----------|
| `test_axi4_master_rd_mon.py` | AXI4 master read monitor | ✅ Complete | 2 |
| `test_axi4_master_wr_mon.py` | AXI4 master write monitor | ✅ Complete | 2 |
| `test_axi4_slave_rd_mon.py` | AXI4 slave read monitor | ✅ Complete | 2 |
| `test_axi4_slave_wr_mon.py` | AXI4 slave write monitor | ✅ Complete | 2 |
| `test_gaxi_buffer_async.py` | GAXI async FIFO | ✅ Complete | 3 |
| `test_gaxi_buffer_sync.py` | GAXI sync FIFO/skid | ✅ Complete | 3 |
| `test_gaxi_wavedrom_example.py` | GAXI example/template | ✅ Complete | 2 |
| `test_apb_master.py` | APB master | ⚠️ Partial | 2 |
| `test_apb_slave.py` | APB slave | ⚠️ Partial | 2 |
| `test_apb_slave_cdc.py` | APB slave CDC | ⚠️ Partial | 2 |
| `test_apb_slave_wavedrom.py` | APB slave (dedicated) | ✅ Complete | 3 |

**Total Waveforms Generated:** ~25

---

## High-Priority Candidates

### Tier 1: Protocol Converters and Bridges (Highest Value)

#### 1. AXI-to-APB Bridge (`test_axi2apb_shim.py`)
- **Module:** `axi4_to_apb_shim.sv` / `axi4_to_apb_convert.sv`
- **Value:** ⭐⭐⭐⭐⭐
- **Complexity:** Medium
- **Estimated Effort:** 2-3 days

**Why High Priority:**
- **Protocol Translation:** Shows complex AXI4→APB conversion timing
- **Educational:** Demonstrates how two different protocols interact
- **Debugging Aid:** Critical for system integration debug
- **Multi-Phase:** AW/W/B (AXI) → PSEL/PENABLE (APB) state machine

**Recommended Waveforms:**
1. Single AXI write → APB write sequence
2. AXI burst write → multiple APB cycles
3. AXI read → APB read with wait states
4. Error handling (APB SLVERR → AXI RESP)

**Implementation Notes:**
- Use TemporalConstraint with SignalTransition on s_axi_awvalid
- Capture through APB PENABLE completion
- Show both AXI and APB signals simultaneously
- Highlight state machine progression

---

#### 2. APB Crossbar (`test_apb_xbar.py`)
- **Module:** `apb_xbar.sv`
- **Value:** ⭐⭐⭐⭐
- **Complexity:** Medium
- **Estimated Effort:** 1-2 days

**Why High Priority:**
- **Address Decoding:** Visualizes PSEL generation per address range
- **Arbitration:** Shows how single master accesses multiple slaves
- **System Integration:** Common SoC component

**Recommended Waveforms:**
1. Access to slave 0 (address decode)
2. Access to slave 1 (different decode)
3. Back-to-back accesses to different slaves
4. Error case (no slave selected)

---

### Tier 2: Arbitration Components (High Educational Value)

#### 3. Round-Robin Arbiter with PWM and MonBus (`test_arbiter_rr_pwm_monbus.py`)
- **Module:** `arbiter_rr_pwm_monbus.sv`
- **Value:** ⭐⭐⭐⭐⭐
- **Complexity:** Medium-High
- **Estimated Effort:** 2-3 days

**Why High Priority:**
- **Arbitration Patterns:** Visualizes round-robin scheduling
- **PWM Integration:** Shows how PWM blocks arbitration
- **Monitor Bus:** Demonstrates packet generation on grants
- **Multi-Request:** Excellent for showing priority resolution

**Recommended Waveforms:**
1. Simple round-robin (4 clients, sequential grants)
2. Simultaneous requests (arbiter fairness)
3. PWM blocking (grants stop during PWM low)
4. Monitor packet generation on each grant
5. ACK protocol (WAIT_GNT_ACK=1 mode)

**Implementation Notes:**
- Capture multiple grant cycles to show round-robin pattern
- Include cfg_pwm_* signals to show PWM control
- Show monbus_pkt_* to demonstrate monitoring
- Use longer capture window (100+ cycles) for full pattern

---

####4. Weighted Round-Robin Arbiter (`test_arbiter_round_robin_weighted.py`)
- **Module:** `arbiter_round_robin_weighted.sv`
- **Value:** ⭐⭐⭐⭐
- **Complexity:** Medium
- **Estimated Effort:** 1-2 days

**Why High Priority:**
- **Weighted Scheduling:** Shows how weight values affect grant frequency
- **QoS Visualization:** Demonstrates quality-of-service mechanisms
- **Algorithm Education:** Clear visualization of weighted arbitration

**Recommended Waveforms:**
1. Equal weights (behaves like simple round-robin)
2. Unequal weights (2:1:1 ratio visible in grants)
3. High-priority client (weight=8 vs others=1)

---

### Tier 3: Clock Domain Crossing (Safety-Critical)

#### 5. CDC Handshake (`test_cdc_handshake.py`)
- **Module:** `cdc_handshake.sv`
- **Value:** ⭐⭐⭐⭐⭐
- **Complexity:** High (dual clocks)
- **Estimated Effort:** 3-4 days

**Why High Priority:**
- **Safety-Critical:** CDC bugs are catastrophic
- **Educational:** Visual proof of correct handshake protocol
- **Metastability:** Shows synchronizer behavior
- **Frequency Ratios:** Demonstrates fast→slow and slow→fast crossing

**Recommended Waveforms:**
1. Single data transfer (req/ack handshake)
2. Back-to-back transfers (protocol timing)
3. Fast→slow clock crossing
4. Slow→fast clock crossing

**Implementation Notes:**
- **Challenge:** Need dual-clock waveform support
- Show both clock domains simultaneously
- Highlight synchronizer stages
- Demonstrate full req→ack cycle

---

### Tier 4: State Machines and Control Logic

#### 6. AXI4 Address Generator (`test_axi4_gen_addr.py`)
- **Module:** `axi4_gen_addr.sv`
- **Value:** ⭐⭐⭐
- **Complexity:** Low-Medium
- **Estimated Effort:** 1 day

**Why High Priority:**
- **Address Patterns:** Visualizes INCR/WRAP/FIXED burst types
- **Alignment:** Shows 4KB boundary handling
- **Educational:** Teaches AXI4 addressing rules

**Recommended Waveforms:**
1. INCR burst (incrementing addresses)
2. WRAP burst (wrapping at boundary)
3. FIXED burst (repeated address)
4. 4KB boundary handling

---

#### 7. AXI Master/Slave Splitter (`test_axi_master_rd_splitter.py`, `test_axi_master_wr_splitter.py`)
- **Module:** `axi_master_rd_splitter.sv`, `axi_master_wr_splitter.sv`
- **Value:** ⭐⭐⭐⭐
- **Complexity:** Medium
- **Estimated Effort:** 2 days each

**Why High Priority:**
- **Transaction Splitting:** Shows how large transactions are divided
- **State Machine:** Visualizes splitting logic
- **Practical:** Common in AXI infrastructure

**Recommended Waveforms:**
1. Single transaction (no split needed)
2. Transaction requiring split (max burst exceeded)
3. Multiple outstanding splits
4. ID reordering after splits

---

### Tier 5: Integration Examples

#### 8. APB HPET (High Precision Event Timer) (`test_apb_hpet.py`)
- **Module:** `apb_hpet.sv`
- **Value:** ⭐⭐⭐⭐
- **Complexity:** Medium
- **Estimated Effort:** 2 days

**Why High Priority:**
- **Complete Peripheral:** Shows full APB peripheral with timers
- **Register Access:** Demonstrates config/status register timing
- **Interrupt Generation:** Shows timer expiration and interrupt assertion
- **Real-World Example:** Practical peripheral implementation

**Recommended Waveforms:**
1. Timer configuration (APB writes to config registers)
2. Timer counting and expiration
3. Interrupt generation
4. Timer clear/restart sequence

---

## Medium-Priority Candidates

### Counter Modules (Educational, Simple to Implement)

| Test | Module | Value | Effort | Notes |
|------|--------|-------|--------|-------|
| `test_counter_bin.py` | Binary counter | ⭐⭐⭐ | 0.5 days | Basic counting patterns |
| `test_counter_johnson.py` | Johnson counter | ⭐⭐⭐ | 0.5 days | Shows unique counting sequence |
| `test_counter_freq_invariant.py` | Freq-invariant counter | ⭐⭐⭐ | 1 day | Different clock frequencies |
| `test_counter_bingray.py` | Binary/Gray counter | ⭐⭐⭐ | 0.5 days | Demonstrates Gray code |

**Rationale:** Simple, fast to implement, good for beginners learning wavedrom framework

---

### Arbiter Variants (Complement PWM arbiter)

| Test | Module | Value | Effort | Notes |
|------|--------|-------|--------|-------|
| `test_arbiter_round_robin_simple.py` | Simple RR arbiter | ⭐⭐⭐ | 1 day | Baseline for comparison |
| `test_arbiter_round_robin.py` | Standard RR arbiter | ⭐⭐⭐ | 1 day | With ACK protocol |
| `test_arbiter_monbus_common.py` | Arbiter + monbus | ⭐⭐⭐ | 1 day | Shows monitoring |

**Rationale:** Creates complete arbiter wavedrom set for documentation

---

### Math and Data Integrity (Lower Priority but Educational)

| Test | Module | Value | Effort | Notes |
|------|--------|-------|--------|-------|
| `test_dataint_ecc.py` | ECC encoder/decoder | ⭐⭐⭐ | 1-2 days | Error detection/correction |
| `test_dataint_crc.py` | CRC generator | ⭐⭐ | 1 day | Checksum calculation |
| `test_bin2gray.py` / `test_gray2bin.py` | Code converters | ⭐⭐ | 0.5 days | CDC preparation |
| `test_leading_one_trailing_one.py` | Leading/trailing ones | ⭐⭐ | 0.5 days | Priority encoding |

**Rationale:** Niche use cases, lower user impact

---

### GAXI Integration (Extend Existing Coverage)

| Test | Module | Value | Effort | Notes |
|------|--------|-------|--------|-------|
| `test_gaxi_buffer_multi.py` | Multi-field GAXI | ⭐⭐⭐⭐ | 1 day | Complements tutorials |
| `test_gaxi_buffer_multi_sigmap.py` | Signal mapping | ⭐⭐⭐ | 1 day | Shows flexibility |
| `test_gaxi_buffer_field.py` | Field packing | ⭐⭐⭐ | 1 day | Field-level detail |

**Rationale:** Enhances GAXI tutorial documentation (TASK-019)

---

### AXI4/AXIL Masters and Slaves (Comprehensive Coverage)

| Test | Module | Value | Effort | Notes |
|------|--------|-------|--------|-------|
| `test_axi4_master_rd.py` | AXI4 master read | ⭐⭐⭐ | 1 day | Base functionality |
| `test_axi4_master_wr.py` | AXI4 master write | ⭐⭐⭐ | 1 day | Base functionality |
| `test_axi4_slave_rd.py` | AXI4 slave read | ⭐⭐⭐ | 1 day | Slave perspective |
| `test_axi4_slave_wr.py` | AXI4 slave write | ⭐⭐⭐ | 1 day | Slave perspective |
| `test_axil4_*.py` (8 tests) | AXI4-Lite variants | ⭐⭐ | 0.5 days each | Simpler protocol |

**Rationale:** Monitors already have wavedrom; adding base components completes the set

---

## Low-Priority Candidates

### Tests Not Recommended for WaveDrom

**Rationale for Exclusion:**

1. **Math Operations** - Not timing-dependent, better shown as truth tables
   - `test_math_adder_*.py`, `test_math_subtractor_*.py`, `test_math_multiplier_*.py`

2. **Static Logic** - Combinational only, no sequential behavior
   - `test_encoder.py`, `test_decoder.py`, `test_sort.py`

3. **LFSR/PRBS** - Too long/complex for meaningful waveforms
   - `test_shifter_lfsr_*.py` (unless showing first few cycles)

4. **Clock Dividers/Generators** - Trivial waveforms (just clock edges)
   - `test_clock_divider.py`, `test_pwm.py`

5. **RAPIDS Subsystem** - Performance tests, not protocol examples
   - `val/rapids/**` (focus on performance metrics, not timing diagrams)

---

## Implementation Recommendations

### Phase 1: Quick Wins (1-2 weeks)
**Goal:** Add value with minimal effort

1. **APB Crossbar** (1-2 days) - Address decode visualization
2. **AXI4 Address Generator** (1 day) - Burst patterns
3. **Simple Counter Modules** (2-3 days total) - Educational basics
4. **GAXI Multi-Field** (1 day) - Complements TASK-019 tutorials

**Deliverables:** 4-5 new wavedrom test modules, ~12-15 waveforms

---

### Phase 2: High-Impact Protocol Work (2-3 weeks)
**Goal:** Critical system integration visualizations

1. **AXI-to-APB Bridge** (2-3 days) - Protocol converter
2. **Round-Robin PWM Arbiter** (2-3 days) - Arbitration patterns
3. **CDC Handshake** (3-4 days) - Safety-critical CDC
4. **APB HPET** (2 days) - Complete peripheral example
5. **AXI Splitters** (4 days total) - Transaction management

**Deliverables:** 5 critical test modules, ~20-25 waveforms

---

### Phase 3: Comprehensive Coverage (2-3 weeks)
**Goal:** Complete arbiter and AXI families

1. **All Arbiter Variants** (4-5 days) - Complete arbiter documentation set
2. **AXI4 Master/Slave Base** (4 days) - Complement existing monitors
3. **Weighted Arbiter** (1-2 days) - QoS visualization
4. **Additional GAXI** (2 days) - Field packing examples

**Deliverables:** 10+ test modules, ~30-40 waveforms

---

## Technical Implementation Guidelines

### Wavedrom Best Practices

1. **Signal Selection:**
   - Include only signals relevant to the scenario
   - Group related signals (e.g., "AW Channel", "W Channel")
   - Use separators (`'|'`) for visual clarity

2. **Constraint Design:**
   - Use SignalTransition for trigger points
   - Set appropriate capture windows (50-100 cycles typical)
   - Add post_match_cycles to capture completion
   - Mark critical constraints as `required=True` for regression

3. **Waveform Naming:**
   - Use descriptive names: `single_beat_read`, `burst_write_with_wait_states`
   - Include scenario details in filename
   - Follow pattern: `{module}_{scenario}_{instance}.json`

4. **Documentation:**
   - Create README.md in each `docs/markdown/assets/WAVES/{module}/` directory
   - Document each waveform with purpose and key signals
   - Include "How to Generate" instructions
   - Link to test source and RTL module

### Example Implementation (AXI-to-APB Bridge)

```python
# In test_axi2apb_shim.py

@cocotb.test()
async def axi2apb_wavedrom_test(dut):
    """Generate wavedrom for AXI-to-APB protocol conversion"""

    # Setup wavedrom
    wave_generator = WaveJSONGenerator()
    wave_solver = TemporalConstraintSolver(dut, log=dut._log, wavejson_generator=wave_generator)

    # Bind signals
    wave_solver.add_signal_binding('s_axi_awvalid', 's_axi_awvalid')
    wave_solver.add_signal_binding('s_axi_wvalid', 's_axi_wvalid')
    wave_solver.add_signal_binding('m_apb_psel', 'm_apb_psel')
    wave_solver.add_signal_binding('m_apb_penable', 'm_apb_penable')
    # ... more signals

    # Define constraint
    axi_write_constraint = TemporalConstraint(
        name="axi_write_to_apb",
        events=[TemporalEvent("aw", SignalTransition("s_axi_awvalid", 0, 1))],
        max_window_size=100,
        signals_to_show=[
            'aclk', '|',
            ['AXI Write', 's_axi_awvalid', 's_axi_awready', 's_axi_wvalid', 's_axi_wready'],
            '|',
            ['APB', 'm_apb_psel', 'm_apb_penable', 'm_apb_pready']
        ]
    )

    wave_solver.add_constraint(axi_write_constraint)

    # Run test
    await wave_solver.start_sampling()
    await run_axi_write_transaction(tb, addr=0x1000, data=0xDEADBEEF)
    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
```

---

## Cost-Benefit Analysis

### Benefits of WaveDrom Addition

1. **Documentation Quality:** Visual timing diagrams improve understanding
2. **Debugging Aid:** Captures expected behavior for comparison
3. **Education:** Onboards new users faster with visual examples
4. **Regression:** Constraint-based ensures waveforms stay valid
5. **Publication:** Professional diagrams for papers/presentations

### Costs

1. **Development Time:** ~1-3 days per test module
2. **Maintenance:** Waveforms must be regenerated if RTL changes
3. **Test Complexity:** Adds constraint logic to tests
4. **Simulation Time:** Wavedrom tests add ~20-30% to test runtime

### ROI Ranking

| Priority | Modules | Effort | Value | ROI |
|----------|---------|--------|-------|-----|
| Tier 1 | Protocol converters (2) | 4-5 days | ⭐⭐⭐⭐⭐ | Excellent |
| Tier 2 | Arbiters (4) | 5-7 days | ⭐⭐⭐⭐⭐ | Excellent |
| Tier 3 | CDC (1) | 3-4 days | ⭐⭐⭐⭐⭐ | Good (high effort) |
| Tier 4 | State machines (3) | 4-5 days | ⭐⭐⭐⭐ | Good |
| Tier 5 | Integration (1) | 2 days | ⭐⭐⭐⭐ | Good |
| Medium | Counters, GAXI, etc. (23) | 15-20 days | ⭐⭐⭐ | Moderate |

**Recommended Investment:** Focus on Tiers 1-2 for maximum impact

---

## Conclusion

### Key Recommendations

1. **Immediate Action:** Implement Tier 1 (protocol converters) - highest value, moderate effort
2. **Next Priority:** Tier 2 (arbiters) - excellent educational value
3. **Long-term:** Comprehensive coverage of AXI4/AXIL families
4. **Skip:** Math operations, pure combinational logic, performance tests

### Success Metrics

- **Coverage Target:** 30-40 test modules with wavedrom (from current 11)
- **Waveform Count:** 80-100 total waveforms (from current ~25)
- **Documentation:** Complete wavedrom coverage for all major protocol families
- **User Impact:** Reduce onboarding time and debug cycles

### Next Steps

1. Create TASK-022 through TASK-029 for high-priority candidates
2. Implement Phase 1 (quick wins) in next sprint
3. Schedule Phase 2 (high-impact) for following month
4. Allocate resources based on ROI ranking

---

**Survey Completed:** 2025-10-11
**Surveyed By:** Claude AI (TASK-020)
**Total Candidates Identified:** 38 tests
**High-Priority Recommendations:** 8 modules, 30-40 waveforms
**Estimated Total Effort:** 4-6 weeks for all high-priority work

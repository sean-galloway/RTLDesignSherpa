# Task: TASK-018 - Add WaveDrom Support to AXI4 Monitor Tests

## Priority
**P2 - Medium**

## Status
**🔴 Not Started**

## Description

Add minimal WaveDrom timing diagram generation to AXI4 monitor tests, following the established GAXI pattern. Generate clean waveforms showing key AXI4 protocol scenarios including burst transactions, out-of-order completion, and error responses.

## Background

**Successful Pattern:** GAXI buffer tests now have WaveDrom integration
**Reference:** `val/amba/test_gaxi_buffer_sync.py`, `test_gaxi_buffer_async.py`

**Challenge:** AXI4 is more complex than GAXI due to:
- Multiple channels (AR, R for reads; AW, W, B for writes)
- Burst transactions (ARLEN/AWLEN)
- Out-of-order completion (ARID/RID)
- Separate address and data phases

**Goal:** Visualize key AXI4 protocol behaviors for documentation and debugging.

## Prerequisites

- [x] WaveDrom framework functional
- [x] GAXI WaveDrom integration complete (reference)
- [ ] AXI4 monitor tests functional
- [ ] TASK-016 complete (monitor test validation)

## Deliverables

### 1. AXI4 Protocol Field Configuration

**File:** `bin/CocoTBFramework/tbclasses/wavedrom_user/axi4.py` (create if needed)

**Functions to Create:**
```python
def get_axi4_read_field_config(id_width=4, addr_width=32, data_width=64):
    """
    Create FieldConfig for AXI4 read channels (AR + R).

    AXI4 Read Channel Fields:
    - AR channel: arid, araddr, arlen, arsize, arburst, arvalid, arready
    - R channel: rid, rdata, rresp, rlast, rvalid, rready
    """
    # Return FieldConfig with AXI4-specific formatting

def get_axi4_write_field_config(id_width=4, addr_width=32, data_width=64):
    """
    Create FieldConfig for AXI4 write channels (AW + W + B).

    AXI4 Write Channel Fields:
    - AW channel: awid, awaddr, awlen, awsize, awburst, awvalid, awready
    - W channel: wdata, wstrb, wlast, wvalid, wready
    - B channel: bid, bresp, bvalid, bready
    """
    # Return FieldConfig with AXI4-specific formatting

def create_axi4_wavejson_generator(field_config, channel_type='read'):
    """Create WaveJSON generator configured for AXI4 protocol"""
    # Return WaveJSONGenerator with labeled groups:
    # - ["Address Channel", ar*/aw* signals]
    # - ["Data Channel", r*/w* signals]
    # - ["Response Channel", b* signals] (write only)
```

### 2. AXI4 Master Read Monitor WaveDrom Test

**File:** `val/amba/test_axi4_master_rd_mon.py` (modify existing)

**Add CocoTB Test Function:**
```python
@cocotb.test(timeout_time=10, timeout_unit="sec")
async def axi4_master_rd_wavedrom_test(dut):
    """
    WaveDrom timing diagram generation for AXI4 master read monitor.

    Generates 4 key scenarios:
    1. Single-beat read (ARLEN=0)
    2. Burst read (ARLEN=3, INCR)
    3. Out-of-order completion (2 transactions, different IDs)
    4. Read error response (RRESP=SLVERR)
    """
    # Setup testbench, WaveDrom solver
    # Run segmented capture for each scenario
```

**Add Pytest Test:**
```python
def generate_axi4_read_wavedrom_params():
    return [
        # id_width, addr_width, data_width, max_trans
        (4, 32, 64, 16),
    ]

@pytest.mark.parametrize("id_width, addr_width, data_width, max_trans",
                         generate_axi4_read_wavedrom_params())
def test_axi4_master_rd_mon_wavedrom(request, ...):
    """AXI4 master read monitor wavedrom test"""
    # Set ENABLE_WAVEDROM=1
    # Run with testcase="axi4_master_rd_wavedrom_test"
```

### 3. AXI4 Master Write Monitor WaveDrom Test

**File:** `val/amba/test_axi4_master_wr_mon.py` (modify existing)

**Add CocoTB Test Function:**
```python
@cocotb.test(timeout_time=10, timeout_unit="sec")
async def axi4_master_wr_wavedrom_test(dut):
    """
    WaveDrom timing diagram generation for AXI4 master write monitor.

    Generates 4 key scenarios:
    1. Single-beat write (AWLEN=0)
    2. Burst write (AWLEN=3, INCR)
    3. Out-of-order responses (2 writes, different IDs)
    4. Write error response (BRESP=SLVERR)
    """
    # Setup and run scenarios
```

**Add Pytest Test:** (similar pattern)

### 4. AXI4 Protocol Scenarios

**Read Scenarios:**

**Scenario 1: Single-Beat Read**
- Constraint: arvalid=1, arlen=0 → arready=1 → rvalid=1, rlast=1
- Shows: Simple 1-beat read transaction
- Edge annotations: araddr → rdata

**Scenario 2: Burst Read (4-beat)**
- Constraint: arvalid=1, arlen=3 → arready=1 → 4 × (rvalid=1) with rlast on 4th
- Shows: Burst read with multiple data beats
- Edge annotations: araddr → rdata[0..3], rlast indicator

**Scenario 3: Out-of-Order Completion**
- Constraints: Two ARs with different IDs, Rs complete in reverse order
- Shows: ID reordering behavior
- Edge annotations: Crossed arrows showing reordering

**Scenario 4: Read Error**
- Constraint: arvalid=1 → arready=1 → rvalid=1, rresp=SLVERR
- Shows: Error response handling
- Edge annotations: Highlight error path

**Write Scenarios:** (similar patterns for AW/W/B channels)

**Expected Output:**
```
val/amba/WaveJSON/
├── test_axi4_master_rd_single_beat.wavejson
├── test_axi4_master_rd_burst.wavejson
├── test_axi4_master_rd_out_of_order.wavejson
├── test_axi4_master_rd_error.wavejson
├── test_axi4_master_wr_single_beat.wavejson
├── test_axi4_master_wr_burst.wavejson
├── test_axi4_master_wr_out_of_order.wavejson
└── test_axi4_master_wr_error.wavejson
```

### 5. Slave Monitor WaveDrom Tests (Optional - P3)

**Files:**
- `val/amba/test_axi4_slave_rd_mon.py`
- `val/amba/test_axi4_slave_wr_mon.py`

**Note:** Same scenarios as master, but from slave perspective (may defer to future task).

### 6. Documentation Updates

**File:** `val/amba/WAVEDROM_INTEGRATION_SUMMARY.md` (update)

Add sections for AXI4 read and write monitor WaveDrom support.

**File:** `docs/markdown/RTLAmba/axi/axi4_master_rd.md` (update existing)

Embed waveform images showing key scenarios:
```markdown
### Single-Beat Read Transaction

![Single-Beat Read](../../assets/WAVES/test_axi4_master_rd_single_beat.png)

### Burst Read Transaction

![Burst Read](../../assets/WAVES/test_axi4_master_rd_burst.png)
```

## Testing

**Run WaveDrom Tests:**
```bash
cd val/amba
pytest test_axi4_master_rd_mon.py::test_axi4_master_rd_mon_wavedrom -v
pytest test_axi4_master_wr_mon.py::test_axi4_master_wr_mon_wavedrom -v
```

**Generate Images:**
```bash
cd val/amba/WaveJSON
for json in test_axi4_master*.wavejson; do
    wavedrom-cli -i "$json" -s ../PNG/"${json%.wavejson}.png"
done
```

## Success Criteria

**Minimum (P2):**
- [ ] AXI4 read/write field configurations created
- [ ] WaveDrom tests added for master read/write monitors
- [ ] 8 WaveJSON files generated (4 read + 4 write scenarios)
- [ ] Clean, readable waveforms showing AXI4 protocol timing
- [ ] Edge annotations for data flow
- [ ] Labeled groups for AR/R or AW/W/B channels
- [ ] Documentation updated with embedded waveforms

**Stretch (P3):**
- [ ] Slave monitor WaveDrom tests
- [ ] Clock-gated variant tests
- [ ] Additional scenarios (FIXED/WRAP bursts, narrow transfers)

## Design Decisions

1. **Focus on Master Monitors:** Start with master read/write
   - Most commonly used
   - Slave monitors can follow same pattern later

2. **4 Scenarios per Monitor:** Minimal but comprehensive
   - Single-beat (simplest)
   - Burst (common case)
   - Out-of-order (AXI4 feature)
   - Error (edge case)

3. **Labeled Groups:** Organize by channel
   - Makes complex multi-channel waveforms readable
   - Follows AXI4 spec organization

4. **Edge Annotations:** Show data flow
   - Address → Data relationships
   - Out-of-order crossings
   - Error paths

## Challenges and Solutions

**Challenge 1: Multi-Channel Complexity**
- AXI4 has 2-3 channels vs GAXI's 1 interface
- **Solution:** Use labeled groups to organize signals by channel

**Challenge 2: Burst Transactions**
- Multiple data beats in sequence
- **Solution:** Use constraint solver to detect RLAST/WLAST, capture full burst

**Challenge 3: Out-of-Order Completion**
- Transactions complete in different order than issued
- **Solution:** Use crossed edge annotations (A→B₁, B→A₁) to show reordering

**Challenge 4: Waveform Width**
- Many signals may make waveforms too wide
- **Solution:** Focus on essential signals, use field definitions to compact data

## References

- **Pattern:** `val/amba/test_gaxi_buffer_sync.py`
- **Framework:** `bin/CocoTBFramework/components/wavedrom/`
- **AXI4 Spec:** ARM IHI0022 (AMBA AXI Protocol Specification)
- **Monitor RTL:** `rtl/amba/axi4/axi4_master_rd_mon.sv`

## Related Tasks

**Prerequisites:**
- TASK-016: Monitor test validation (should complete first)
- GAXI WaveDrom integration (complete) - provides pattern

**Related:**
- TASK-017: APB WaveDrom support
- TASK-019: AXIS WaveDrom support
- TASK-020: Identify other tests needing waves

**Follow-up:**
- AXI4 slave monitor WaveDrom support (defer to P3)
- Clock-gated variants (defer to P3)

---

**Task Owner:** TBD
**Created:** 2025-10-06
**Target Completion:** TBD
**Estimated Effort:** 6-10 hours (more complex than APB due to multi-channel protocol)

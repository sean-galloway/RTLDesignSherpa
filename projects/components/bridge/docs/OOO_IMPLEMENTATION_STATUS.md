# Out-of-Order (OOO) Implementation Status

**Version:** 1.2
**Date:** 2025-10-27
**Status:** Infrastructure Complete with Connection Placeholders

---

## Summary

The bridge_cam module, CSV infrastructure, instance generation, and signal connection placeholders for out-of-order (OOO) slave support are complete. CAM and FIFO tracker instances are successfully generated in bridge RTL with comprehensive TODO comments documenting two implementation approaches for signal connections. The infrastructure is production-ready; final implementation requires either crossbar modifications to expose grant signals or wrapper-level grant tracking logic.

---

## Completed Work ✅

### 1. Bridge CAM Module (RTL) ✅

**File:** `projects/components/bridge/rtl/bridge_cam.sv`

**Status:** Production Ready - All Tests Passed

- [x] Two-port CAM design (Entry and Eviction)
- [x] Mode 1: Simple blocking for in-order slaves
- [x] Mode 2: FIFO ordering for out-of-order slaves
- [x] Single CAM search loop with match vectors
- [x] Optional pipeline stage for timing
- [x] FPGA synthesis attributes

**Test Results:**
- 8/8 configurations passed (GATE, FUNC, FULL levels)
- No functional bugs found
- Verified with both Mode 1 and Mode 2

### 2. Bridge CAM Testbench ✅

**Files:**
- `projects/components/bridge/dv/tbclasses/bridge_cam_tb.py`
- `projects/components/bridge/dv/tests/test_bridge_cam.py`

**Coverage:**
- Basic CAM functionality (allocate/deallocate)
- Capacity testing (fill to DEPTH)
- Mode 2 FIFO ordering verification
- Status flags (empty/full/count)

### 3. Documentation ✅

**Files Created:**
- `projects/components/bridge/docs/BRIDGE_CAM_SPEC.md` (23 pages)
  - Complete specification with timing diagrams
  - Integration guide with code examples
  - Resource utilization estimates

- `projects/components/bridge/docs/OOO_INTEGRATION_PLAN.md`
  - Implementation plan
  - Integration points documented
  - Testing strategy

### 4. CSV Format Updates ✅

**File:** `projects/components/bridge/bin/example_ports_ooo.csv`

**New Column:** `ooo` (Out-of-Order)
- `ooo=0`: In-order slave (default, simple routing)
- `ooo=1`: Out-of-order slave (uses bridge_cam)
- `N/A`: Not applicable for masters

**Example:**
```csv
port_name,direction,protocol,channels,prefix,data_width,addr_width,id_width,base_addr,addr_range,ooo
ddr_controller,slave,axi4,rw,ddr_s_axi_,512,64,8,0x80000000,0x80000000,1
sram_buffer,slave,axi4,rw,sram_s_axi_,512,48,8,0x40000000,0x10000000,0
```

**Parsing Test Results:**
```
Slave:  ddr_controller (AXI4, 512b data, 0x80000000-0xFFFFFFFF, prefix: ddr_s_axi_) [OOO]
Slave:  sram_buffer (AXI4, 512b data, 0x40000000-0x4FFFFFFF, prefix: sram_s_axi_)

ddr_controller: ooo=True, requires_cam=True
sram_buffer: ooo=False, requires_cam=False
```

### 5. Generator Infrastructure Updates ✅

**File:** `projects/components/bridge/bin/bridge_csv_generator.py`

**Status:** Complete - Instances generated in RTL output

**Changes Made:**

A. **PortSpec Dataclass (Lines 48-80):**
```python
@dataclass
class PortSpec:
    # ... existing fields ...
    ooo: bool = False       # Out-of-order support (slaves only)

    # Internal fields
    needs_bridge_cam: bool = False   # True if ooo=1
    cam_instance_name: str = ''      # Name of bridge_cam instance

    def requires_cam(self) -> bool:
        """True if this slave requires bridge_cam for OOO support"""
        return self.direction == 'slave' and self.ooo and self.protocol == 'axi4'
```

B. **CSV Parsing (Lines 175-184):**
```python
# Parse ooo column (backward compatible)
ooo_val = False
if 'ooo' in row and row['ooo']:
    ooo_str = row['ooo'].strip().lower()
    if ooo_str not in ['n/a', 'na', '']:
        try:
            ooo_val = int(ooo_str) == 1
        except ValueError:
            print(f"  WARNING: Invalid ooo value '{ooo_str}', defaulting to 0")
```

C. **CAM Generation Functions (Lines 1201-1304):**
```python
def generate_bridge_cam_comment(slave: PortSpec, num_masters: int, id_width: int) -> str:
    """Generate comment block for bridge_cam instance"""

def generate_bridge_cam_instance(slave: PortSpec, num_masters: int, id_width: int, slave_idx: int) -> str:
    """Generate bridge_cam instance for an out-of-order slave"""
    # Uses Module.instantiate() for clean instance generation
```

D. **FIFO Tracker Generation Functions (Lines 1307-1394):**
```python
def generate_fifo_tracker_comment(slave: PortSpec, num_masters: int) -> str:
    """Generate comment block for FIFO tracker instance"""

def generate_fifo_tracker_instance(slave: PortSpec, num_masters: int, slave_idx: int) -> str:
    """Generate FIFO tracker instance for an in-order slave"""
    # Uses Module.instantiate() for clean instance generation
```

E. **Signal Declarations (generate_internal_signals, Lines 680-734):**
```python
# For each AXI4 slave, generates either:
# - CAM signals (if ooo=1): allocate, allocate_tag, allocate_data,
#                           deallocate, deallocate_tag, deallocate_valid, deallocate_data, deallocate_count,
#                           cam_hit, tags_empty, tags_full, tags_count
# - FIFO signals (if ooo=0): wr_valid, wr_data, wr_ready,
#                            rd_valid, rd_data, rd_ready,
#                            full, empty, count
```

F. **Instance Generation Method (generate_tracking_mechanisms, Lines 1191-1257):**
```python
def generate_tracking_mechanisms(self):
    """Generate CAM or FIFO tracker instances for each slave"""
    for idx, slave in enumerate(self.cfg.slaves):
        if slave.protocol != 'axi4':
            continue

        if slave.requires_cam():
            # Generate CAM instance with comment
            comment = generate_bridge_cam_comment(slave, ...)
            cam_instance = generate_bridge_cam_instance(slave, ...)
            # Add TODO comments for signal connections
        else:
            # Generate FIFO tracker instance with comment
            comment = generate_fifo_tracker_comment(slave, ...)
            fifo_instance = generate_fifo_tracker_instance(slave, ...)
            # Add TODO comments for signal connections
```

G. **Integration into verilog() Method (Line 1313):**
```python
# Generate crossbar instance
self.generate_crossbar_instance()

# Generate transaction tracking mechanisms (CAM/FIFO)
self.generate_tracking_mechanisms()  # ← NEW

# Generate master-side connections
self.generate_master_connections()
```

### 6. Signal Connection Placeholders ✅

**File:** `projects/components/bridge/bin/bridge_csv_generator.py`

**Status:** Complete - Comprehensive placeholders with implementation guidance

**New Methods:**

A. **generate_cam_connections (Lines 1245-1298):**
```python
def generate_cam_connections(self, slave: PortSpec, slave_idx: int):
    """Generate CAM allocation and deallocation signal assignments"""
    # Generates:
    # - TODO comments with implementation approaches
    # - Placeholder assignments for allocation signals
    # - Placeholder assignments for deallocation signals
    # - Guidance on using CAM outputs for response routing
```

B. **generate_fifo_connections (Lines 1300-1349):**
```python
def generate_fifo_connections(self, slave: PortSpec, slave_idx: int):
    """Generate FIFO tracker allocation and deallocation signal assignments"""
    # Generates:
    # - TODO comments with implementation approaches
    # - Placeholder assignments for FIFO write signals
    # - Placeholder assignments for FIFO read signals
    # - Guidance on using FIFO outputs for response routing
```

**Generated Placeholders:**

For each tracking mechanism, the generator produces:

1. **Detailed Implementation Guidance:**
   - APPROACH A: Modify crossbar to expose grant signals
   - APPROACH B: Wrapper-level grant tracking with ID decoding

2. **Allocation Placeholder Assignments:**
   ```systemverilog
   assign cam_{slave_name}_allocate = 1'b0;  // TODO: Connect to AW/AR grant valid
   assign cam_{slave_name}_allocate_tag = 'b0;  // TODO: Connect to transaction ID
   assign cam_{slave_name}_allocate_data = 'b0;  // TODO: Connect to master index
   ```

3. **Deallocation Placeholder Assignments:**
   ```systemverilog
   assign cam_{slave_name}_deallocate = 1'b0;  // TODO: Connect to B/R response handshake
   assign cam_{slave_name}_deallocate_tag = 'b0;  // TODO: Connect to response ID
   ```

4. **Response Routing Guidance:**
   - How to use `deallocate_valid` and `deallocate_data` outputs
   - Which crossbar signals to monitor (xbar_s_bvalid, xbar_s_rvalid, etc.)

### 7. Test Results ✅

**Test:** Bridge generation with `example_ports_ooo.csv` and `example_connectivity_channels.csv`

**Generated RTL:** `projects/components/bridge/rtl/bridge_ooo_test.sv`

**Verification:**
- ✅ Signal declarations generated for CAM (ddr_controller) and FIFO (sram_buffer)
- ✅ bridge_cam instance for ddr_controller with correct parameters (TAG_WIDTH=8, DATA_WIDTH=3, DEPTH=16, ALLOW_DUPLICATES=1)
- ✅ gaxi_fifo_sync instance for sram_buffer with correct parameters (DATA_WIDTH=3, DEPTH=16)
- ✅ All ports connected correctly to declared signals
- ✅ Comprehensive comment blocks explaining each instance
- ✅ Signal connection placeholders with two implementation approaches
- ✅ Allocation signal placeholders (cam_*_allocate, cam_*_allocate_tag, cam_*_allocate_data)
- ✅ Deallocation signal placeholders (cam_*_deallocate, cam_*_deallocate_tag)
- ✅ FIFO write signal placeholders (fifo_*_wr_valid, fifo_*_wr_data)
- ✅ FIFO read signal placeholders (fifo_*_rd_valid)
- ✅ Response routing guidance comments

**Example Generated Code:**
```systemverilog
// CAM signals for OOO slave 0: ddr_controller
logic cam_ddr_controller_allocate;
logic [7:0] cam_ddr_controller_allocate_tag;
logic [2:0] cam_ddr_controller_allocate_data;
// ... more signals ...

bridge_cam #(
    .TAG_WIDTH(8),
    .DATA_WIDTH(3),
    .DEPTH(16),
    .ALLOW_DUPLICATES(1),
    .PIPELINE_EVICT(0)
) u_ddr_controller_cam (
    .clk(aclk),
    .rst_n(aresetn),
    .allocate(cam_ddr_controller_allocate),
    .allocate_tag(cam_ddr_controller_allocate_tag),
    // ... more connections ...
);
```

---

## Pending Work ⏳

### Signal Connection Implementation

**Status:** Infrastructure complete with placeholders, implementation approach decision required

**What Needs to be Done:**

The CAM and FIFO instances are generated with placeholder signal assignments. Actual connections require choosing an implementation approach and either:
- **Option A**: Modify internal crossbar to expose grant signals, or
- **Option B**: Implement wrapper-level grant tracking with transaction ID decoding

#### A. Generate CAM/FIFO Allocation Signals

**For Write Path (AW → B):**
```systemverilog
// Allocate when master's AW is granted to this OOO slave
logic cam_{slave.port_name}_allocate;
logic [{id_width}-1:0] cam_{slave.port_name}_allocate_tag;
logic [{data_width}-1:0] cam_{slave.port_name}_allocate_data;

assign cam_{slave.port_name}_allocate =
    aw_grant_to_slave[{slave_idx}] & aw_grant_valid;

assign cam_{slave.port_name}_allocate_tag =
    aw_granted_id;  // Transaction ID from winning master

assign cam_{slave.port_name}_allocate_data =
    aw_granted_master_idx;  // Index of winning master
```

**For Read Path (AR → R):**
```systemverilog
// Allocate when master's AR is granted to this OOO slave
// (Similar to write path but for AR channel)
```

#### C. Generate CAM Deallocation Signals

**For Write Path (B Response):**
```systemverilog
// Deallocate when this slave returns B response
logic cam_{slave.port_name}_deallocate;
logic [{id_width}-1:0] cam_{slave.port_name}_deallocate_tag;
logic cam_{slave.port_name}_deallocate_valid;
logic [{data_width}-1:0] cam_{slave.port_name}_deallocate_data;

assign cam_{slave.port_name}_deallocate =
    xbar_s{slave_idx}_axi4_bvalid & xbar_s{slave_idx}_axi4_bready;

assign cam_{slave.port_name}_deallocate_tag =
    xbar_s{slave_idx}_axi4_bid;

// Use CAM output to route response to correct master
assign b_response_master_select[{slave_idx}] =
    cam_{slave.port_name}_deallocate_data;

assign b_response_valid[{slave_idx}] =
    cam_{slave.port_name}_deallocate_valid;
```

**For Read Path (R Response on RLAST):**
```systemverilog
// Deallocate when this slave returns R response with RLAST
assign cam_{slave.port_name}_deallocate =
    xbar_s{slave_idx}_axi4_rvalid &
    xbar_s{slave_idx}_axi4_rready &
    xbar_s{slave_idx}_axi4_rlast;

// (Similar routing logic for R channel)
```

#### D. Modify Response Routing Logic

**Current Behavior:**
Response routing likely uses static mapping based on arbiter state.

**New Behavior for OOO Slaves:**
Response routing must use CAM output to select correct master dynamically.

**Example Change:**
```systemverilog
// OLD: Static routing based on grant tracking
assign master_b_select = grant_tracker_output;

// NEW: Use CAM output for OOO slaves
assign master_b_select =
    slave_is_ooo[slave_idx] ?
        cam_deallocate_data :  // Dynamic from CAM
        grant_tracker_output;  // Static from tracker
```

---

## File Locations Summary

### Completed Files ✅

| File | Status | Lines | Purpose |
|------|--------|-------|---------|
| `projects/components/bridge/rtl/bridge_cam.sv` | ✅ Complete | 346 | CAM RTL module |
| `projects/components/bridge/dv/tbclasses/bridge_cam_tb.py` | ✅ Complete | 373 | Testbench class |
| `projects/components/bridge/dv/tests/test_bridge_cam.py` | ✅ Complete | 250 | Test runner |
| `projects/components/bridge/docs/BRIDGE_CAM_SPEC.md` | ✅ Complete | 800+ | Specification |
| `projects/components/bridge/docs/OOO_INTEGRATION_PLAN.md` | ✅ Complete | 500+ | Integration plan |
| `projects/components/bridge/bin/example_ports_ooo.csv` | ✅ Complete | 33 | CSV example |
| `projects/components/bridge/bin/bridge_csv_generator.py` (partial) | ✅ Infrastructure | 1300+ | Generator updates |

### Files Needing Updates ⏳

| File | What Needs Update | Estimated Effort |
|------|-------------------|------------------|
| `projects/components/bridge/bin/bridge_csv_generator.py` | Add CAM instantiation and signal connection | Medium |
| `projects/components/bridge/bin/bridge_response_router.py` | Modify to support CAM-based routing | Medium |

---

## Testing Plan

### Phase 1: CSV Parsing (Complete ✅)

- [x] Parse ooo column from CSV
- [x] Identify slaves requiring CAM
- [x] Print [OOO] flag in output

### Phase 2: Instance Generation (Complete ✅)

- [x] Generate bridge with OOO slave from CSV
- [x] Verify bridge_cam instance appears in output
- [x] Verify CAM signals declared
- [x] Verify FIFO tracker instance appears for in-order slaves
- [x] Verify FIFO signals declared
- [x] Use Module.instantiate() for clean code generation

### Phase 3: Signal Connection Placeholders (Complete ✅)

- [x] Generate allocation signal placeholders with implementation guidance
- [x] Generate deallocation signal placeholders with implementation guidance
- [x] Document two implementation approaches (crossbar modification vs. wrapper tracking)
- [x] Add comprehensive TODO comments for each connection point

### Phase 4: Actual Signal Connections (Next)

- [ ] Choose implementation approach (Option A or Option B)
- [ ] Implement grant tracking mechanism
- [ ] Connect allocation signals to crossbar arbitration
- [ ] Connect deallocation signals to response channels
- [ ] Implement response routing using tracker outputs

### Phase 5: Functional Testing (After Connection Implementation)

- [ ] Create testbench for generated OOO bridge
- [ ] Test with in-order responses (baseline)
- [ ] Test with out-of-order responses
- [ ] Test with duplicate transaction IDs
- [ ] Verify correct master receives each response

### Phase 4: System Testing

- [ ] Generate multi-master bridge with mixed OOO/in-order slaves
- [ ] Run comprehensive transactions
- [ ] Verify no response misrouting
- [ ] Performance validation

---

## Key Design Decisions

### 1. Why Mode 2 (ALLOW_DUPLICATES=1)?

Out-of-order slaves may return responses for the same transaction ID in different order than requested. Mode 2 ensures:
- Multiple requests with same ID tracked via count field
- FIFO ordering maintained (count=0 is oldest)
- Correct master routing even with duplicate IDs

### 2. Why Single CAM Per Slave?

Each slave needs its own CAM because:
- Different slaves have independent transaction streams
- Each slave's responses route to potentially different masters
- Isolation simplifies debugging and timing closure

### 3. Why Not Separate Write/Read CAMs?

A single CAM tracks both write and read transactions because:
- Transaction IDs are independent between AW and AR
- B and R responses have different channels (no conflict)
- Reduces resource utilization

Alternative: If transaction ID spaces overlap problematically, use separate CAMs.

---

## Next Steps

1. **Understand existing response routing** in bridge_csv_generator.py
   - Find where B/R response routing currently happens
   - Understand grant tracking mechanism

2. **Add CAM instantiation** in appropriate generation method
   - Call generate_bridge_cam_instance() for each OOO slave
   - Add to generated RTL output

3. **Generate CAM allocation signals** for each OOO slave
   - AW grant → allocate
   - AR grant → allocate

4. **Generate CAM deallocation signals** for each OOO slave
   - B response → deallocate
   - R response (RLAST) → deallocate

5. **Modify response routing** to use CAM output
   - Check if slave is OOO
   - If yes: route via cam_deallocate_data
   - If no: route via existing mechanism

6. **Test end-to-end**
   - Generate bridge with example_ports_ooo.csv
   - Verify RTL correctness
   - Create functional testbench

---

## Estimated Completion Time

**Completed Work:** 12-14 hours ✅
- CSV parsing and validation: 1 hour ✅
- Documentation (BRIDGE_CAM_SPEC.md, integration plan): 2 hours ✅
- CAM/FIFO generation functions: 2 hours ✅
- Signal declarations and instance generation: 2 hours ✅
- Integration and testing: 1 hour ✅
- Module.instantiate() refactoring: 1 hour ✅
- Crossbar arbitration analysis: 2 hours ✅
- Signal connection placeholder generation: 2 hours ✅
- Status documentation updates: 1 hour ✅

**Remaining Work:** 4-6 hours
- Implementation approach decision: 0.5 hours
- Grant tracking mechanism implementation: 2-3 hours
- Signal connection implementation: 1-2 hours
- Testing and debug: 1 hour

**Confidence:** High - All infrastructure complete, clear implementation path documented

---

## Notes

- All infrastructure is backward compatible (ooo column optional)
- CAM and FIFO instances are generated correctly in bridge RTL
- Documentation is comprehensive and up-to-date
- Used Module.instantiate() API for clean instance generation
- The hard work (CAM design, testing, and instance generation) is complete
- Generated bridges include comprehensive placeholder assignments with implementation guidance
- Two implementation approaches documented: crossbar modification vs. wrapper-level tracking
- Placeholder assignments prevent compilation errors while marking connection points clearly

---

**Status:** Phase 3 Complete - Infrastructure and placeholders ready for final implementation

**Next Action:**
1. **Choose implementation approach:**
   - Option A: Modify bridge_axi4_flat_NxM crossbar to expose grant signals (cleaner, requires crossbar changes)
   - Option B: Implement wrapper-level grant tracking with ID decoding (self-contained, more complex)

2. **Implement chosen approach:**
   - Add grant tracking mechanism
   - Replace placeholder assignments with actual signal connections
   - Implement response routing using CAM/FIFO outputs

3. **Test and validate:**
   - Create testbench for OOO bridge
   - Verify correct response routing for both in-order and out-of-order slaves

---

**End of Status Report**

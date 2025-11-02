# STREAM Architectural Notes

**Date:** 2025-10-17
**Purpose:** Document key architectural decisions and design clarifications

---

## 1. Separation of Concerns: Scheduler vs Data Engines

**CRITICAL:** Rigid separation between coordinator and workers

### 1.1 Scheduler Role (Coordinator)

**What Scheduler Does:**
- Tracks total beats remaining for each transfer
- Requests access to data engines via `datard_valid` / `datawr_valid`
- Provides: address, total beats remaining, channel ID
- Updates internal counters based on completion feedback

**What Scheduler Does NOT Do:**
- ❌ Does NOT dictate burst lengths
- ❌ Does NOT configure AXI transaction details
- ❌ Does NOT manage SRAM buffer directly

### 1.2 Data Engine Role (Autonomous Workers)

**What Engines Do:**
- Accept requests via `datard_valid` / `datawr_valid` + `datard_ready` / `datawr_ready`
- **Autonomously decide burst length** based on:
  - Internal configuration registers
  - SRAM buffer space available
  - AXI protocol constraints
  - Performance optimization
- Execute AXI transactions
- Report completion via `done_strobe` + `beats_done`

**What Engines Do NOT Do:**
- ❌ Do NOT wait for scheduler to tell them burst size
- ❌ Do NOT track total transfer progress (scheduler's job)

### 1.3 Interface Contract

**Scheduler → Engine Request:**
```systemverilog
output logic        datard_valid;           // "I need read access"
input  logic        datard_ready;           // "I'm granting you access"
output logic [63:0] datard_addr;            // "Start reading from this address"
output logic [31:0] datard_beats_remaining; // "Total beats left in transfer"
output logic [3:0]  datard_channel_id;      // "This is my channel ID"
```

**Engine → Scheduler Completion:**
```systemverilog
input  logic        datard_done_strobe;     // "I completed a burst"
input  logic [31:0] datard_beats_done;      // "I moved this many beats"
input  logic        datard_error;           // "I encountered an error"
```

**Key Point:** Scheduler says "what" (how many beats total), Engine decides "how" (burst size).

---

## 2. Burst Length Configuration

### 2.1 Configuration Mechanism

Burst lengths are NOT passed via the `datard_*` / `datawr_*` interfaces. Instead:

**Option 1: Internal Engine Registers (Recommended for V1)**
```systemverilog
// Inside axi_read_engine.sv
parameter int DEFAULT_BURST_LEN = 8;
logic [7:0] r_burst_len = DEFAULT_BURST_LEN;

// Engine uses r_burst_len internally
assign ar_len = r_burst_len - 1;  // AXI burst length encoding
```

**Option 2: Configuration Registers (Later, like HPET)**
- PeakRDL-generated register interface
- Software-programmable burst lengths per engine
- Similar to HPET timer configuration approach
- **NOT implemented in Phase 1**

### 2.2 Asymmetric Burst Lengths

Different engines can use different burst lengths:

```
Example Configuration:
  AXI Read Engine  → 8 beats per burst
  AXI Write Engine → 16 beats per burst
```

**Why This Works:**
- SRAM buffer decouples read and write rates
- Scheduler doesn't care about burst sizing
- Each engine optimizes independently

---

## 3. MonBus AXIL Group

**Source:** Copied identically from RAPIDS `monbus_axil_group.sv`

**Why Identical:**
- MonBus protocol is standardized across all projects
- Error/interrupt handling proven in RAPIDS
- AXIL interface for configuration reused

**Adaptations:**
- Header comment updated to mention STREAM
- Functionally unchanged

**Interfaces:**
- **Inputs:** Multiple monitor bus streams (one per channel)
- **Outputs:**
  - AXIL slave (error/interrupt FIFO read)
  - AXIL master (mon packet writes to memory)
  - `irq_out` (interrupt when error FIFO not empty)

---

## 4. Configuration Strategy

### 4.1 Phase 1: Hardcoded Defaults

**Current approach** (for initial implementation):
- Burst lengths: Compile-time parameters
- Channel enables: APB registers
- MonBus filtering: Hardcoded conservative defaults

### 4.2 Later: PeakRDL-Generated Registers

**Future approach** (like HPET):
1. Define register map in `.rdl` file
2. Use `peakrdl regblock` to generate RTL
3. Software-programmable configuration
4. Same pattern as `projects/components/apb_hpet/`

**Benefits:**
- Industry-standard register generation
- Auto-generated documentation
- Consistent with HPET approach

---

## 5. Data Flow: Request-Complete Cycle

### 5.1 Read Phase Example

```
Cycle 0: Scheduler asserts datard_valid, datard_beats_remaining=64
         Engine asserts datard_ready (grants access)

Cycle 1: Engine starts AXI AR transaction (burst_len=8, decided internally)

Cycle 8: Engine completes 8-beat read
         Engine asserts datard_done_strobe=1, datard_beats_done=8

Cycle 9: Scheduler decrements beats_remaining = 64 - 8 = 56
         Scheduler keeps datard_valid=1 (more beats remain)

Cycle 10: Engine starts next AXI AR transaction (burst_len=16, decided internally)
          (Engine chose larger burst because more SRAM space available)

Cycle 26: Engine completes 16-beat read
          Engine asserts datard_done_strobe=1, datard_beats_done=16

Cycle 27: Scheduler decrements beats_remaining = 56 - 16 = 40
          ...continues until beats_remaining == 0
```

### 5.2 Write Phase Example

```
Similar to read phase, but with datawr_* signals
Engine may use different burst length than read engine
SRAM buffering handles rate differences
```

---

## 6. APB Configuration (PeakRDL-Generated, Deferred)

### 6.1 Why Deferred

From user feedback:
> "The apb config will be the last thing done. They will have configs done along the lines of how they are done for the hpet."

**Rationale:**
- Focus on core data path first
- Configuration details defined after functional validation
- Consistency with HPET register approach

### 6.2 PeakRDL-Based Approach (Following HPET Pattern)

**Implementation Pattern:**
- Define register map in `stream_regs.rdl`
- Generate RTL using `peakrdl_generate.py` (similar to HPET)
- Create APB wrapper with optional CDC (`apb_slave_cdc`)
- Wire register outputs to STREAM control signals

**Workflow:**
```bash
cd projects/components/stream/regs
../../bin/peakrdl_generate.py stream_regs.rdl --copy-rtl ../rtl/stream_macro
```

**Reference Implementation:**
- `projects/components/apb_hpet/peakrdl/hpet_regs.rdl` - Register definition example
- `projects/components/apb_hpet/rtl/apb_hpet.sv` - Wrapper with CDC example
- `projects/components/stream/regs/README.md` - STREAM-specific workflow

**Location:**
- Register definition: `regs/stream_regs.rdl` (to be created)
- Generated RTL: `regs/generated/rtl/` (auto-generated)
- Integration wrapper: `rtl/stream_macro/` (to be created)

---

## 7. Key Differences from PRD Section 5.3/5.4

### 7.1 PRD Error (Corrected Here)

**PRD showed (WRONG):**
```systemverilog
input  logic [7:0]  datard_burst_len;       // ❌ Scheduler specifies burst
```

**Corrected Architecture:**
```systemverilog
// NO burst_len signal in interface
// Engine decides internally based on config
```

### 7.2 Corrected Interfaces

**Read Interface (Corrected):**
```systemverilog
// Scheduler → Engine
output logic        datard_valid;
input  logic        datard_ready;
output logic [63:0] datard_addr;
output logic [31:0] datard_beats_remaining;  // Total remaining
output logic [3:0]  datard_channel_id;

// Engine → Scheduler (completion)
input  logic        datard_done_strobe;
input  logic [31:0] datard_beats_done;       // What engine actually moved
input  logic        datard_error;
```

**Write Interface (Corrected):**
```systemverilog
// Scheduler → Engine
output logic        datawr_valid;
input  logic        datawr_ready;
output logic [63:0] datawr_addr;
output logic [31:0] datawr_beats_remaining;  // Total remaining
output logic [3:0]  datawr_channel_id;

// Engine → Scheduler (completion)
input  logic        datawr_done_strobe;
input  logic [31:0] datawr_beats_done;       // What engine actually moved
input  logic        datawr_error;
```

---

## 8. Implementation Priority

### 8.1 Phase 1 (Complete)

1. ✅ Fix scheduler interfaces (remove burst_len)
2. ✅ Copy monbus_axil_group from RAPIDS
3. ✅ Document architecture (this file)
4. ✅ Update CLAUDE.md with corrected patterns

### 8.2 Phase 2 (Next)

1. Implement AXI Read Engine v1 (basic, hardcoded burst length)
2. Implement AXI Write Engine v1 (basic, hardcoded burst length)
3. Implement channel arbiter
4. Integration testing

### 8.3 Phase 3 (Later)

1. Define register map in PeakRDL
2. Generate configuration registers
3. Add AXIL slave interface for register access
4. Software programmable burst lengths

---

## 9. Verification Implications

### 9.1 Testbench Structure

Testbenches must respect separation of concerns:

```python
# Scheduler testbench
class SchedulerTB(TBBase):
    async def test_descriptor_flow(self):
        # Scheduler provides beats_remaining
        assert self.dut.datard_beats_remaining.value == 64
        # Scheduler does NOT specify burst_len
        # No self.dut.datard_burst_len attribute!
```

```python
# Engine testbench
class AXIReadEngineTB(TBBase):
    async def test_burst_decision(self):
        # Engine decides burst length internally
        # Check AXI AR channel for burst length
        assert self.dut.m_axi_ar_len.value == 7  # 8-beat burst (len=7)
```

### 9.2 Integration Tests

```python
# Integration testbench
class IntegrationTB(TBBase):
    async def test_transfer_complete(self):
        # Kick off transfer
        await self.write_descriptor(addr=0x1000, len=64)

        # Monitor completion strobes
        beats_done = 0
        while beats_done < 64:
            await self.wait_for_strobe('datard_done_strobe')
            beats_done += int(self.dut.datard_beats_done.value)

        # Verify scheduler decremented correctly
        assert self.dut.datard_beats_remaining.value == 0
```

---

## 10. Summary

**Key Takeaways:**

1. **Scheduler = Coordinator:** Tracks work, doesn't dictate how it's done
2. **Engines = Autonomous:** Decide burst lengths internally based on config/constraints
3. **Interface Contract:** `beats_remaining` (scheduler) vs `beats_done` (engine)
4. **Configuration:** Phase 1 hardcoded, later PeakRDL-generated like HPET
5. **MonBus AXIL:** Identical to RAPIDS (proven design)

**Mantras:**

> "Scheduler says WHAT, Engine decides HOW"

> "Rigid separation of concerns"

> "No FSMs in data path engines - use streaming pipelines"

---

**Document Owner:** STREAM Architecture Team
**Last Updated:** 2025-10-17
**Next Review:** After Phase 2 implementation

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

# Claude Code Guide: RAPIDS Subsystem

**Version:** 1.0
**Last Updated:** 2025-10-11
**Purpose:** AI-specific guidance for working with RAPIDS subsystem

---

## Quick Context

**What:** Rapid AXI Programmable In-band Descriptor System - Custom DMA-style accelerator with AXIS network interfaces
**Status:** Active development - "beats" rearchitecture is the current RTL
**Your Role:** Help users understand architecture, fix bugs, extend functionality

> **Status (2026-07-22):** RAPIDS was rearchitected to the "beats" design. Current RTL lives in
> `rtl/fub_beats/`, `rtl/macro_beats/`, and `rtl/top_beats/rapids_beats_top.sv` (plus control
> engines in `rtl/fub/`). The old `rapids_fub/`/`rapids_macro/` modules (scheduler.sv,
> program_engine.sv, network_slave.sv, ...) and the old `docs/rapids_spec/` tree are gone.
> Sections below that describe the pre-beats design are marked accordingly.

**Complete Specification:**
- `projects/components/dmas/rapids/docs/rapids_beats_has/` - Architecture spec (HAS); index: `rapids_beats_has_index.md`
- `projects/components/dmas/rapids/docs/rapids_beats_mas/` - Micro-architecture spec (MAS); index: `rapids_beats_mas_index.md`
- Built PDFs: `docs/RAPIDS_Beats_HAS_v0.8.pdf`, `docs/RAPIDS_Beats_MAS_v0.7.pdf`

---

## Global Requirements Reference

**IMPORTANT: Check `/GLOBAL_REQUIREMENTS.md` before starting RAPIDS work**

All mandatory requirements are consolidated in the global requirements document:
- **See:** `/GLOBAL_REQUIREMENTS.md` - Repository-wide mandatory requirements
- **RAPIDS-Specific:** Attribution format, BFM usage requirements
- **Universal:** TB location, three methods, TBBase inheritance, 100% success

This CLAUDE.md provides RAPIDS-specific guidance. Also review:
- Root `/CLAUDE.md` - Repository-wide patterns
- `projects/components/CLAUDE.md` - Project area standards (reset macros, FPGA attributes)
- `bin/TBClasses/` - Shared TB framework (flat protocol dirs: `gaxi/`, `axi4/`, `apb/`, ...);
  the full CocoTBFramework (components/, tbclasses/) lives in the separate RTLDesignSherpa-DV repo

---

## Critical Rules for This Subsystem

### Rule #0.1: Testbench Location and Test Structure (MANDATORY)

**See:** `/GLOBAL_REQUIREMENTS.md` Section 2.1. Test structure itself --
Pattern B, the `cocotb_test_*` prefix, pytest wrapper naming -- is the
`test-patterns` skill.

RAPIDS keeps all of its verification in the project area:

```
projects/components/dmas/rapids/dv/
├── tbclasses/     # 22 TB classes: scheduler_tb, descriptor_engine_tb,
│                  # rapids_core_beats_tb, rapids_beats_top_tb, ...
├── components/    # RAPIDS-specific BFMs (data_mover_bfm.py)
└── tests/         # runners by layer: fub/ fub_beats/ macro/ macro_beats/ top_beats/
```

**Scoring choice (GR 2.4).** The descriptor and program engines are in-order,
so they verify by queue access -- `monitor._recvQ.popleft()` compared against
an expected value. The memory model is for integration tests, where several
masters are in flight and order is not guaranteed. Reaching for the memory
model on an in-order engine buys nothing and hides ordering bugs.

---

### Rule #0.5: Config Before Reset (RAPIDS-specific)

The three mandatory TB methods are `/GLOBAL_REQUIREMENTS.md` Section 2.2. What
is particular to RAPIDS is **when** configuration is applied: several modules
latch config during reset, so a value written after `deassert_reset()` is
simply never seen.

Set these in `setup_clocks_and_reset()` *before* asserting reset:

| Signal | Why it must be early |
|---|---|
| `cfg_initial_credit` | the credit counter initialises to `(1 << cfg)` during reset |
| `cfg_use_credit` | selects the flow-control mode the counter comes up in |
| `cfg_timeout_threshold` | watchdog loads at reset |
| `cfg_sram_depth` | must be stable before the memory controllers leave reset |

(The credit signals belong to the retired pre-beats `scheduler.sv`;
`rtl/fub_beats/scheduler_beats.sv` has no credit management yet. The
config-before-reset rule still holds for the beats modules.)

---

###  Rule #0.75: Audit Signal Naming BEFORE Writing Testbenches

Why factory prefix collisions break BFM discovery, and the audit tool that
catches them, are in `vault/handbook/design/naming-and-style.md`. Run
`bin/audit_signal_naming_conflicts.py` over `rtl/` before writing a TB.
What is RAPIDS-specific is below.

**Known RAPIDS Conflicts:**
See `projects/components/dmas/rapids/known_issues/scheduler_group_signal_naming_conflicts.md` for conflicts documented against the pre-beats scheduler_group.sv (the patterns still apply to `scheduler_group_beats.sv`):
- `desc` prefix: 4 internal + 4 external (AR/R channels)
- `prog` prefix: 4 internal + 6 external (AW/W/B channels)

**Recommended Workflow:**
1. Write RTL module with signals
2. **Run audit script to detect conflicts**
3. Fix naming conflicts (rename internal signals with `_to_sched` suffix)
4. Write testbench using factory pattern matching

**Three Solutions When Conflicts Found:**
1. **Rename internal signals** (recommended): `desc_valid` → `desc_to_sched_valid`
2. **Use explicit signal_map**: Bypass pattern matching with manual signal mapping
3. **Test at higher level**: Where internal signals aren't visible (e.g., rapids_top)

**Complete Guide:** `bin/SIGNAL_NAMING_AUDIT.md`

---

### Rule #1: MANDATORY BFM Usage for FUB-Level Tests

Never hand-drive a valid/ready handshake and never write a custom protocol
driver. The interface-to-BFM map, the factory list, the trap list and the
extract-vs-embed criteria are in `vault/handbook/dv/bfm-usage.md`.

RAPIDS-specific: the network interfaces are **AXIS**, so they take the `axis4`
factories; the custom valid/ready interfaces (program, descriptor) take GAXI.
`dv/components/data_mover_bfm.py` is the one extracted RAPIDS BFM.

Manual driving is acceptable for throwaway debug and for clock/reset init --
never in a production testbench.

---

### Rule #2: Know the Known Issues

Check `projects/components/dmas/rapids/known_issues/` (and `active/`) before
diagnosing anything.

Historical: the pre-beats `scheduler.sv` credit counter was hardcoded to 0,
then fixed with exponential encoding (0->1, 1->2, ..., 15->inf). That scheduler
was replaced by `rtl/fub_beats/scheduler_beats.sv`, which has no credit
management yet, and its `known_issues/scheduler.md` write-up was retired with
it. Do not chase that bug in beats code.

---

### Rule #3: RAPIDS is Complex - Understand Block Interactions

**Key Interaction Patterns:**

1. **Descriptor Flow:**
   ```
   Software → AXIL4 → Descriptor Engine → Scheduler → Data Paths
   ```

2. **Sink Data Path (Network → Memory):**
   ```
   Network Slave → Sink SRAM Control → Sink AXI Write Engine → System Memory
   ```

3. **Source Data Path (Memory → Network):**
   ```
   System Memory → Source AXI Read Engine → Source SRAM Control → Network Master
   ```

4. **Monitoring:**
   ```
   All Blocks → MonBus Reporter → MonBus Output
   ```

**Never work on one block in isolation without understanding its upstream/downstream dependencies!**

### Rule #4: Test Strategy is Multi-Layered

**RAPIDS testing follows this hierarchy:**

1. **FUB (Functional Unit Block) Tests:** `projects/components/dmas/rapids/dv/tests/fub_beats/` (+ `fub/` for control engines)
   - Individual block testing
   - Focus: Module-level functionality
   - Example: Scheduler FSM, Descriptor Engine FIFO

2. **Macro Tests:** `projects/components/dmas/rapids/dv/tests/macro_beats/` (+ `macro/` for the monbus group)
   - Multi-block scenarios
   - Focus: Block-to-block interfaces
   - Example: Scheduler group, sink/source data path end-to-end

3. **Top Tests:** `projects/components/dmas/rapids/dv/tests/top_beats/`
   - Full RAPIDS operation
   - Focus: Realistic traffic patterns
   - Example: Complete DMA transfer with monitoring

**When creating/modifying tests, ensure appropriate test layer is used!**

---

## Architecture Quick Reference

### Block Organization

```
RAPIDS Beats Architecture (rtl/)
├── fub_beats/                       (per-block engines)
│   ├── scheduler_beats.sv           (per-channel scheduler FSM)
│   ├── descriptor_engine_beats.sv   (descriptor fetch, parsing)
│   ├── axi_read_engine_beats.sv     (AXI4 read from system memory)
│   ├── axi_write_engine_beats.sv    (AXI4 write to system memory)
│   ├── alloc_ctrl_beats.sv          (SRAM space allocation)
│   ├── drain_ctrl_beats.sv          (SRAM drain control)
│   └── latency_bridge_beats.sv      (latency-hiding bridge)
├── fub/                             (control engines)
│   ├── ctrlrd_engine.sv             (control read engine)
│   └── ctrlwr_engine.sv             (control write engine)
├── macro_beats/                     (assemblies)
│   ├── scheduler_group_beats.sv / scheduler_group_array_beats.sv
│   ├── snk_data_path_beats.sv / snk_data_path_axis_beats.sv   (AXIS network → SRAM → memory)
│   ├── src_data_path_beats.sv / src_data_path_axis_beats.sv   (memory → SRAM → AXIS network)
│   ├── snk_sram_controller_beats.sv / src_sram_controller_beats.sv
│   ├── rapids_config_block.sv + rapids_*_regs.rdl             (APB CSRs via PeakRDL)
│   └── rapids_core_beats.sv         (core integration)
├── macro/
│   └── monbus_axil_group_2in.sv     (MonBus aggregation / AXI-Lite drain)
└── top_beats/
    └── rapids_beats_top.sv          (top level: APB config, AXI4 masters, AXIS in/out, MonBus)
```

**See:** `docs/rapids_beats_mas/ch02_fub_blocks/` and `docs/rapids_beats_mas/ch03_macro_blocks/` for detailed block descriptions

### Module Quick Reference

| Module | Location | Purpose | Documentation (docs/rapids_beats_mas/) |
|--------|----------|---------|---------------|
| **scheduler_beats.sv** | `fub_beats/` | Per-channel scheduler FSM | `ch02_fub_blocks/01_scheduler.md` |
| **descriptor_engine_beats.sv** | `fub_beats/` | Descriptor fetch, parsing | `ch02_fub_blocks/02_descriptor_engine.md` |
| **axi_read_engine_beats.sv** | `fub_beats/` | Memory reads | `ch02_fub_blocks/03_axi_read_engine.md` |
| **axi_write_engine_beats.sv** | `fub_beats/` | Memory writes | `ch02_fub_blocks/04_axi_write_engine.md` |
| **alloc_ctrl_beats.sv** | `fub_beats/` | SRAM allocation | `ch02_fub_blocks/05_beats_alloc_ctrl.md` |
| **drain_ctrl_beats.sv** | `fub_beats/` | SRAM drain control | `ch02_fub_blocks/06_beats_drain_ctrl.md` |
| **latency_bridge_beats.sv** | `fub_beats/` | Latency-hiding bridge | `ch02_fub_blocks/07_beats_latency_bridge.md` |
| **snk_data_path_beats.sv** | `macro_beats/` | Sink data path | `ch03_macro_blocks/03_sink_data_path.md` |
| **src_data_path_beats.sv** | `macro_beats/` | Source data path | `ch03_macro_blocks/07_source_data_path.md` |
| **rapids_core_beats.sv** | `macro_beats/` | Core integration | `ch03_macro_blocks/11_rapids_core_beats.md` |
| **rapids_beats_top.sv** | `top_beats/` | Top-level integration | `ch03_macro_blocks/14_rapids_beats_top.md` |

### Interface Summary

| Interface | Type | Width | Purpose | Specification |
|-----------|------|-------|---------|---------------|
| **APB4** | Slave | 32-bit | Control/status registers | `docs/rapids_beats_has/ch03_interfaces/04_apb_interface.md` |
| **AXI4 (Sink)** | Master | Configurable | Write to system memory | `docs/rapids_beats_mas/ch04_interfaces/01_axi4_interface_spec.md` |
| **AXI4 (Source)** | Master | Configurable | Read from system memory | `docs/rapids_beats_mas/ch04_interfaces/01_axi4_interface_spec.md` |
| **AXIS (Sink)** | Slave | Configurable | Network ingress (tid = channel) | `docs/rapids_beats_mas/ch04_interfaces/02_axis_interface_spec.md` |
| **AXIS (Source)** | Master | Configurable | Network egress (tid = channel) | `docs/rapids_beats_mas/ch04_interfaces/02_axis_interface_spec.md` |
| **MonBus** | Master | 64-bit | Monitor packet output | `docs/rapids_beats_mas/ch04_interfaces/03_monbus_interface_spec.md` |

---

## Common User Questions and Responses

### Q: "How does the scheduler work?"

**A: Direct answer:**

The scheduler is a complex FSM that coordinates RAPIDS operations:

1. **Idle State:** Waits for descriptors from Descriptor Engine
2. **Parse State:** Extracts descriptor fields (address, length, control)
3. **Credit Check:** Verifies credit availability (if credit mode enabled)
4. **Execute State:** Activates appropriate data path (sink or source)
5. **Monitor State:** Tracks operation progress
6. **Complete State:** Generates completion packets, updates credits

**Key FSM States:**
- `IDLE` → `PARSE` → `CREDIT_CHECK` → `EXECUTE` → `MONITOR` → `COMPLETE` → `IDLE`

**Credit Management:**
- Historical: the pre-beats scheduler.sv implemented exponential credit encoding
  (0→1, 1→2, 2→4, ..., 15→∞) - see Q&A below for the historical details
- Current: `rtl/fub_beats/scheduler_beats.sv` has no credit management yet (planned later phase)

**See:**
- `projects/components/dmas/rapids/docs/rapids_beats_mas/ch02_fub_blocks/01_scheduler.md` - Complete FSM specification
- `projects/components/dmas/rapids/known_issues/README.md` - Known bugs and workarounds

### Q: "How do I configure RAPIDS?"

> **Status (2026-07-22):** The beats top (`rapids_beats_top.sv`) exposes an APB4 config slave
> (`s_apb_*`) with PeakRDL-generated registers (`rtl/macro_beats/rapids_regs.rdl`); access
> registers by name via the generated regmap, not hardcoded offsets. The AXIL4 write sequence
> below is from the pre-beats design and is kept for historical flavor only.

**A: Configuration via memory-mapped register interface:**

```systemverilog
// 1. Initialize RAPIDS via AXIL4 writes
// Configure SRAM depths
write_axil(ADDR_SINK_SRAM_DEPTH, 1024);
write_axil(ADDR_SOURCE_SRAM_DEPTH, 1024);

// Set timeout thresholds
write_axil(ADDR_TIMEOUT_THRESHOLD, 1000);

// Configure initial credits (exponential encoding)
// 0→1, 1→2, 2→4, 3→8, 4→16, etc.
write_axil(ADDR_INITIAL_CREDIT, 4);  // 4 = 16 credits (2^4)
write_axil(ADDR_CREDIT_ENABLE, 1);   // Enable credit mode (now fixed!)

// 2. Load descriptors
write_descriptor(addr, length, control_bits);

// 3. Enable operation
write_axil(ADDR_ENABLE, 1);
```

**See:**
- `projects/components/dmas/rapids/docs/rapids_beats_has/ch05_programming/03_initialization.md` - Programming model
- `projects/components/dmas/rapids/docs/rapids_beats_has/ch05_programming/02_register_map.md` - Register definitions

### Q: "What's the data flow for network to memory transfer?"

**A: Sink path data flow:**

```
1. Network Packet Arrives
   ↓
2. Network Slave receives packet
   - Validates packet format
   - Handshakes with Network interface
   ↓
3. Sink SRAM Control buffers data
   - Writes to SRAM
   - Manages write pointers
   - Handles backpressure
   ↓
4. Sink AXI Write Engine
   - Reads from SRAM
   - Generates AXI4 write transactions
   - Bursts data to system memory
   ↓
5. Completion Reporting
   - Generates MonBus completion packet
   - Updates scheduler state
```

**Key Considerations:**
- SRAM acts as buffer to decouple network from memory timing
- AXI4 bursts used for efficient memory access
- Backpressure propagates from memory to network

**See:** `projects/components/dmas/rapids/docs/rapids_beats_mas/ch03_macro_blocks/03_sink_data_path.md`

### Q: "What's the credit counter bug and how does exponential encoding work?"

> **Status (2026-07-22):** Historical. This bug and fix lived in the retired pre-beats
> scheduler.sv; `rtl/fub_beats/scheduler_beats.sv` currently has no credit management
> (planned for a later phase). Kept as background for when credits return.

**A: Scheduler credit counter exponential encoding (pre-beats):**

The scheduler uses **exponential credit encoding** to provide a wide range of credit values (1 to 16384) with a compact 4-bit configuration:

**Encoding Table:**
| `cfg_initial_credit` | Actual Credits | Use Case |
|---------------------|----------------|----------|
| 0 | 1 | Minimum (2^0) |
| 1 | 2 | Very low traffic (2^1) |
| 2 | 4 | Low traffic (2^2) |
| 3 | 8 | (2^3) |
| 4 | 16 | Typical (2^4) |
| 5 | 32 | (2^5) |
| 6 | 64 | Medium traffic (2^6) |
| 7 | 128 | (2^7) |
| 8 | 256 | High traffic (2^8) |
| 10 | 1024 | Very high traffic (2^10) |
| 14 | 16384 | Maximum finite (2^14) |
| 15 | ∞ (0xFFFFFFFF) | Unlimited credits |

**FIXED Implementation (in the retired pre-beats scheduler.sv):**
```systemverilog
// Exponential credit encoding: 0→1, 1→2, 2→4, ..., 14→16384, 15→∞
r_descriptor_credit_counter <= (cfg_initial_credit == 4'hF) ? 32'hFFFFFFFF :
                              (cfg_initial_credit == 4'h0) ? 32'h00000001 :
                              (32'h1 << cfg_initial_credit);
```

**Was Broken (Before Fix):**
```systemverilog
r_descriptor_credit_counter <= 32'h0;  // WRONG: Hardcoded to 0
```

**Impact (Before Fix):**
- Credit-based flow control didn't work
- All operations blocked if credit mode enabled
- Descriptors never processed

**Encoding Rationale:**
- Compact 4-bit config covers wide range: 1 to 16384 credits
- Fine-grained control for low traffic (1, 2, 4, 8)
- High-throughput support (256, 1024, 16384)
- Special unlimited mode (15 → ∞)

**Important:** Exponential encoding applies **only at initialization**. Once running, the counter operates linearly (increment/decrement by 1).

**See:**
- `projects/components/dmas/rapids/docs/rapids_beats_mas/ch02_fub_blocks/01_scheduler.md` - Current scheduler specification
- `projects/components/dmas/rapids/known_issues/README.md` - Issue tracking (the old scheduler.md write-up was retired with the pre-beats RTL)

### Q: "How do I run RAPIDS tests?"

**A: Multi-layered test approach:**

```bash
# All of these go through the area Makefile. A bare pytest drops the level,
# the derived worker count and the reruns, and skips clean-all -- see
# vault/handbook/dv/running-regressions.md
cd projects/components/dmas/rapids/dv/tests

# 1. FUB tests - individual blocks. AREAS narrows the sweep;
#    the dispatcher's areas are: fub fub_beats macro macro_beats top_beats
make run-scheduler_beats-gate AREAS=fub_beats
make run-all-gate AREAS=fub_beats      # every beats FUB test
make run-all-gate AREAS=fub            # control engines

# 2. Macro tests - multi-block scenarios
make run-all-func AREAS=macro_beats

# 3. Top tests - full RAPIDS operation
make run-all-func AREAS=top_beats

# Waves: WAVES=1 via the target, not --vcd. create_view_cmd() writes a
# ready-made gtkwave command beside the log.
make run-scheduler_beats-gate-waves AREAS=fub_beats
```

**Test Organization:**
- **FUB tests:** Focus on individual block functionality
- **Macro tests:** Verify block-to-block interfaces
- **Top tests:** Validate complete data flows

**Current status:** regenerate it -- `dv/tests/analyze_beats_coverage.py`
writes to `dv/tests/coverage_reports/`. The ~80% figure that sat here was a
pre-beats snapshot, as is `docs/RAPIDS_Validation_Status_Report.md`, which
remains the written-up version of that era.

---

## Integration Patterns

### Pattern 1: Basic RAPIDS Instantiation

```systemverilog
rapids_top #(
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),
    .Network_DATA_WIDTH(64),
    .SRAM_DEPTH(1024),
    .MAX_DESCRIPTORS(16)
) u_rapids (
    // Clock and Reset
    .aclk               (system_clk),
    .aresetn            (system_rst_n),

    // AXIL4 Control Interface
    .s_axil_awaddr      (ctrl_awaddr),
    .s_axil_awvalid     (ctrl_awvalid),
    .s_axil_awready     (ctrl_awready),
    .s_axil_wdata       (ctrl_wdata),
    .s_axil_wstrb       (ctrl_wstrb),
    .s_axil_wvalid      (ctrl_wvalid),
    .s_axil_wready      (ctrl_wready),
    .s_axil_bresp       (ctrl_bresp),
    .s_axil_bvalid      (ctrl_bvalid),
    .s_axil_bready      (ctrl_bready),
    .s_axil_araddr      (ctrl_araddr),
    .s_axil_arvalid     (ctrl_arvalid),
    .s_axil_arready     (ctrl_arready),
    .s_axil_rdata       (ctrl_rdata),
    .s_axil_rresp       (ctrl_rresp),
    .s_axil_rvalid      (ctrl_rvalid),
    .s_axil_rready      (ctrl_rready),

    // AXI4 Memory Interface (Sink - Write)
    .m_axi_sink_awaddr  (mem_sink_awaddr),
    .m_axi_sink_awlen   (mem_sink_awlen),
    .m_axi_sink_awsize  (mem_sink_awsize),
    .m_axi_sink_awburst (mem_sink_awburst),
    .m_axi_sink_awvalid (mem_sink_awvalid),
    .m_axi_sink_awready (mem_sink_awready),
    // ... additional AXI4 sink write channel signals

    // AXI4 Memory Interface (Source - Read)
    .m_axi_source_araddr  (mem_source_araddr),
    .m_axi_source_arlen   (mem_source_arlen),
    .m_axi_source_arsize  (mem_source_arsize),
    .m_axi_source_arburst (mem_source_arburst),
    .m_axi_source_arvalid (mem_source_arvalid),
    .m_axi_source_arready (mem_source_arready),
    // ... additional AXI4 source read channel signals

    // Network Network Interface (Sink - Receive)
    .s_network_tdata       (net_rx_data),
    .s_network_tvalid      (net_rx_valid),
    .s_network_tready      (net_rx_ready),
    .s_network_tlast       (net_rx_last),
    // ... additional Network sink signals

    // Network Network Interface (Source - Transmit)
    .m_network_tdata       (net_tx_data),
    .m_network_tvalid      (net_tx_valid),
    .m_network_tready      (net_tx_ready),
    .m_network_tlast       (net_tx_last),
    // ... additional Network source signals

    // MonBus Output
    .monbus_pkt_valid   (rapids_mon_valid),
    .monbus_pkt_ready   (rapids_mon_ready),
    .monbus_pkt_data    (rapids_mon_data)
);
```

### Pattern 2: Configuration Sequence

```systemverilog
// Recommended initialization sequence
initial begin
    // 1. Assert reset
    aresetn = 0;
    repeat(10) @(posedge aclk);
    aresetn = 1;

    // 2. Configure RAPIDS via AXIL4
    axil_write(ADDR_SINK_SRAM_DEPTH, 1024);
    axil_write(ADDR_SOURCE_SRAM_DEPTH, 1024);
    axil_write(ADDR_TIMEOUT_THRESHOLD, 1000);
    axil_write(ADDR_INITIAL_CREDIT, 4);  // 4 = 16 credits (2^4, exponential encoding)
    axil_write(ADDR_CREDIT_ENABLE, 1);  // Enable credit mode (now fixed!)

    // 3. Load descriptors
    for (int i = 0; i < num_descriptors; i++) begin
        axil_write(ADDR_DESC_ADDR, descriptor[i].addr);
        axil_write(ADDR_DESC_LEN, descriptor[i].length);
        axil_write(ADDR_DESC_CTRL, descriptor[i].control);
        axil_write(ADDR_DESC_COMMIT, 1);
    end

    // 4. Enable RAPIDS operation
    axil_write(ADDR_ENABLE, 1);
end
```

### Pattern 3: MonBus Integration

```systemverilog
// Always add downstream FIFO for MonBus
gaxi_fifo_sync #(
    .DATA_WIDTH(64),
    .DEPTH(256)
) u_rapids_mon_fifo (
    .i_clk      (aclk),
    .i_rst_n    (aresetn),
    .i_data     (monbus_pkt_data),
    .i_valid    (monbus_pkt_valid),
    .o_ready    (monbus_pkt_ready),
    .o_data     (fifo_mon_data),
    .o_valid    (fifo_mon_valid),
    .i_ready    (consumer_ready)
);
```

---

## Anti-Patterns to Catch

### Anti-Pattern 1: Not Understanding Exponential Credit Encoding

```systemverilog
WRONG:
.cfg_initial_credit(4'd16),  // Thinks this gives 16 credits - it doesn't!

CORRECTED:
"Credits use exponential encoding:
- cfg_initial_credit = 4 → 16 credits (2^4)
- cfg_initial_credit = 8 → 256 credits (2^8)
- cfg_initial_credit = 15 → ∞ credits (unlimited)
(Pre-beats behavior; scheduler_beats.sv has no credit management yet. See the encoding
table in the credit-counter Q&A above.)"
```

### Anti-Pattern 2: Insufficient SRAM Depth

```systemverilog
WRONG:
.SRAM_DEPTH(16)  // Too small for realistic packets

CORRECTED:
"SRAM depth should match typical packet sizes.
Recommended: 1024-4096 entries depending on data width and packet sizes."
```

### Anti-Pattern 3: No MonBus Downstream Handling

```systemverilog
WRONG:
assign monbus_pkt_ready = 1'b1;  // Always ready = potential packet loss

CORRECTED:
"Connect to FIFO or proper consumer:
gaxi_fifo_sync #(.DATA_WIDTH(64), .DEPTH(256)) u_mon_fifo (
    .i_valid(monbus_pkt_valid),
    .i_data(monbus_pkt_data),
    .o_ready(monbus_pkt_ready),
    ...
);"
```

### Anti-Pattern 4: Testing Individual Blocks in Isolation

```systemverilog
WRONG:
"Only test scheduler without descriptor engine"

CORRECTED:
"RAPIDS blocks are tightly coupled. Always test:
1. FUB tests for basic block functionality
2. Integration tests for block interactions
3. System tests for complete flows"
```

---

## Debugging Workflow

### Issue: Scheduler Not Processing Descriptors

**Check in order:**
1. Credit configuration correct? (Remember exponential encoding!)
2. Descriptors loaded via AXIL4?
3. RAPIDS enabled? (`ADDR_ENABLE = 1`)
4. Reset properly deasserted?
5. Descriptor engine FIFO not empty?

**Debug commands:**
```bash
cd projects/components/dmas/rapids/dv/tests
make run-scheduler_beats-gate AREAS=fub_beats          # -v --tb=short by default
make run-scheduler_beats-gate-waves AREAS=fub_beats    # WAVES=1, not --vcd
# create_view_cmd() writes the gtkwave command beside the log
```

### Issue: Data Path Stalls

**Check in order:**
1. SRAM depth sufficient?
2. Downstream interfaces ready?
3. AXI4 backpressure handling?
4. Network flow control?
5. Buffer overflow/underflow detection?

**Waveform Analysis:**
- Check SRAM read/write pointers
- Verify AXI4 handshakes
- Inspect Network TREADY signals

### Issue: MonBus Packets Not Generated

**Check in order:**
1. Operations completing successfully?
2. MonBus ready signal asserted?
3. MonBus reporter enabled?
4. Downstream FIFO not full?

---

## Testing Guidance

### Running Tests

Tests are organised by layer under `dv/tests/`: `fub/` and `fub_beats/` for
single blocks, `macro/` and `macro_beats/` for multi-block scenarios,
`top_beats/` for full RAPIDS operation. `make list` enumerates the roots.

This area's Makefile takes an `AREAS` variable (default
`fub fub_beats macro macro_beats top_beats`) to scope a run to some layers:

```bash
cd projects/components/dmas/rapids/dv/tests

make run-all-gate AREAS=fub_beats          # one layer
make run-scheduler_beats-gate AREAS=fub_beats
make clean-all && make run-all-full-parallel   # everything; clean-all first
```

Target grammar, the levels and why `clean-all` is not optional:
`vault/handbook/dv/running-regressions.md`.

### Test Coverage Status

Generate it, do not read it from here -- a pasted table is stale the day after
it is written. `dv/tests/analyze_beats_coverage.py` writes to
`dv/tests/coverage_reports/`.

---

## Key Documentation Links

**Specification** (`projects/components/dmas/rapids/docs/`):
- `rapids_beats_has/rapids_beats_has_index.md` - architecture spec (HAS)
- `rapids_beats_mas/rapids_beats_mas_index.md` - micro-architecture spec (MAS)
- MAS `ch02_fub_blocks/`, `ch03_macro_blocks/`, `ch04_interfaces/` - per-block
  and interface detail; HAS `ch05_programming/` - the programming model

**This component:** `PRD.md`, `TASKS.md`, `known_issues/`.

**Validation:** `docs/RAPIDS_Validation_Status_Report.md` -- test results, but a
**pre-beats snapshot** (last updated 2026-07-22; it still discusses
program_engine, network_slave and the retired `scheduler.sv`). `PRD.md` labels
it the same way. For current numbers run `dv/tests/analyze_beats_coverage.py`.

**Framework BFM docs:** `../RTLDesignSherpa-DV/docs/components/<family>/`
(published at sean-galloway.github.io/RTLDesignSherpa-DV).

---

## Verification Patterns

These were ~270 lines of general DV method sitting in a component file. They
now live in the handbook, where every area can find them:

- **Asynchronous outputs need a background monitor** --
  `vault/handbook/dv/async-output-capture.md`. This is RAPIDS' own lesson: the
  descriptor-engine test found 5 of 12 descriptors and filed it as a 42%
  engine defect, when the engine was correct and the test was not watching.
- **Delay profiles** -- `vault/handbook/dv/randomization.md`. RAPIDS'
  `DelayProfile` enum re-implements `DEFAULT_PROFILES`; name a catalogue
  profile instead.
- **Extract a BFM or embed it** -- `vault/handbook/dv/bfm-usage.md`, which uses
  RAPIDS' own `data_mover_bfm.py` (extracted) and the embedded AXI responder in
  `descriptor_engine_tb.py` as the worked pair.
- **100% success is required** -- `/GLOBAL_REQUIREMENTS.md` 3.3, which names
  this file as its source. A 70% threshold hides a defect rather than
  tolerating it.

---

## Documentation Generation

Both specs build from their index file into DOCX and PDF, written into
`docs/`. Use the wrapper scripts -- they apply the house style:

```bash
cd projects/components/dmas/rapids/docs
./generate_has_pdf.sh --rev 0.8     # RAPIDS_Beats_HAS_v0.8.docx/.pdf
./generate_mas_pdf.sh --rev 0.7     # RAPIDS_Beats_MAS_v0.7.docx/.pdf
```

They call `bin/md_to_docx.py`, which follows the markdown links out of the
index, demotes headings and builds the ToC. Pipeline details, the LaTeX/PDF
engine choice and the caption traps: `vault/handbook/authoring/doc-pipeline.md`.

---

**Version:** 1.2
**Last Updated:** 2025-10-14
**Maintained By:** RTL Design Sherpa Project

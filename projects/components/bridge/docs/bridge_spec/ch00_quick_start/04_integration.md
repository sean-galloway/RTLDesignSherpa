### Quick Start - Integration

#### Overview

Now that your bridge is generated and tested, let's integrate it into a SystemVerilog design.

**What You'll Learn:**
- How to instantiate the bridge in your RTL
- Connect AXI4 masters and slaves
- Clock and reset connections
- File list integration

**Time Required:** 10-15 minutes

---

#### Prerequisites

Before integration:
- ✅ Bridge generated (see 02_first_bridge.md)
- ✅ Tests passing (see 03_simulation.md)
- ✅ Understanding of your SoC architecture
- ✅ AXI4 master/slave components ready

---

#### Integration Steps Overview

```
1. Add bridge files to your project
2. Instantiate bridge in your top-level
3. Connect masters and slaves
4. Connect clocks and resets
5. Compile and verify
```

---

#### Step 1: Add Bridge Files to Project

**Option A: Use Generated Filelist**

Your generated bridge includes a `.f` filelist:

```
rtl/generated/my_first_bridge/my_first_bridge.f
```

**Contents:**
```systemverilog
// Bridge package
rtl/generated/my_first_bridge/my_first_bridge_pkg.sv

// Bridge components
rtl/generated/my_first_bridge/cpu_master_adapter.sv
rtl/generated/my_first_bridge/dma_master_adapter.sv
rtl/generated/my_first_bridge/my_first_bridge_xbar.sv
rtl/generated/my_first_bridge/my_first_bridge.sv

// Dependencies (if any)
rtl/amba/axi4_slave_wr.sv      // Timing isolation wrappers
rtl/amba/axi4_slave_rd.sv
rtl/common/skid_buffer.sv      // Skid buffers
// ... other dependencies
```

**Add to your compilation:**
```bash
# Verilator
verilator -f rtl/generated/my_first_bridge/my_first_bridge.f your_top.sv

# Vivado
read_verilog -f rtl/generated/my_first_bridge/my_first_bridge.f

# VCS
vcs -f rtl/generated/my_first_bridge/my_first_bridge.f
```

**Option B: Manual File Addition**

If you prefer manual control, add individual files to your project's compile order.

---

#### Step 2: Instantiate Bridge in Your Design

**Example: SoC Top-Level**

```systemverilog
module my_soc_top (
    input  logic        clk,
    input  logic        rst_n,
    // ... other ports
);

    // =========================================
    // Clock and Reset
    // =========================================
    logic aclk;
    logic aresetn;
    
    assign aclk = clk;
    assign aresetn = rst_n;

    // =========================================
    // AXI4 Signal Declarations
    // =========================================
    
    // CPU Master Signals (connects to CPU core)
    logic [3:0]   cpu_m_axi_awid;
    logic [31:0]  cpu_m_axi_awaddr;
    logic [7:0]   cpu_m_axi_awlen;
    logic [2:0]   cpu_m_axi_awsize;
    logic [1:0]   cpu_m_axi_awburst;
    logic         cpu_m_axi_awlock;
    logic [3:0]   cpu_m_axi_awcache;
    logic [2:0]   cpu_m_axi_awprot;
    logic         cpu_m_axi_awvalid;
    logic         cpu_m_axi_awready;
    // ... (W, B, AR, R channels)
    
    // DMA Master Signals (connects to DMA engine)
    logic [3:0]   dma_m_axi_awid;
    // ... (all AXI4 channels)
    
    // DDR Slave Signals (connects to DDR controller)
    logic [3:0]   ddr_s_axi_awid;
    logic [31:0]  ddr_s_axi_awaddr;
    // ... (all AXI4 channels)
    
    // SRAM Slave Signals (connects to SRAM controller)
    logic [3:0]   sram_s_axi_awid;
    // ... (all AXI4 channels)

    // =========================================
    // Master Components
    // =========================================
    
    // CPU Core (generates AXI4 master transactions)
    cpu_core u_cpu (
        .clk            (aclk),
        .rst_n          (aresetn),
        // AXI4 Master Interface
        .m_axi_awid     (cpu_m_axi_awid),
        .m_axi_awaddr   (cpu_m_axi_awaddr),
        // ... connect all AXI4 signals
    );
    
    // DMA Engine (generates AXI4 master transactions)
    dma_engine u_dma (
        .clk            (aclk),
        .rst_n          (aresetn),
        // AXI4 Master Interface
        .m_axi_awid     (dma_m_axi_awid),
        // ... connect all AXI4 signals
    );

    // =========================================
    // BRIDGE INSTANTIATION
    // =========================================
    
    my_first_bridge u_bridge (
        .aclk           (aclk),
        .aresetn        (aresetn),
        
        // CPU Master Interface (inputs to bridge)
        .cpu_m_axi_awid     (cpu_m_axi_awid),
        .cpu_m_axi_awaddr   (cpu_m_axi_awaddr),
        .cpu_m_axi_awlen    (cpu_m_axi_awlen),
        .cpu_m_axi_awsize   (cpu_m_axi_awsize),
        .cpu_m_axi_awburst  (cpu_m_axi_awburst),
        .cpu_m_axi_awlock   (cpu_m_axi_awlock),
        .cpu_m_axi_awcache  (cpu_m_axi_awcache),
        .cpu_m_axi_awprot   (cpu_m_axi_awprot),
        .cpu_m_axi_awvalid  (cpu_m_axi_awvalid),
        .cpu_m_axi_awready  (cpu_m_axi_awready),
        // ... (W, B, AR, R channels)
        
        // DMA Master Interface (inputs to bridge)
        .dma_m_axi_awid     (dma_m_axi_awid),
        // ... (all DMA AXI4 signals)
        
        // DDR Slave Interface (outputs from bridge)
        .ddr_s_axi_awid     (ddr_s_axi_awid),
        .ddr_s_axi_awaddr   (ddr_s_axi_awaddr),
        // ... (all DDR AXI4 signals)
        
        // SRAM Slave Interface (outputs from bridge)
        .sram_s_axi_awid    (sram_s_axi_awid),
        // ... (all SRAM AXI4 signals)
    );

    // =========================================
    // Slave Components
    // =========================================
    
    // DDR Controller (receives AXI4 slave transactions)
    ddr_controller u_ddr (
        .clk            (aclk),
        .rst_n          (aresetn),
        // AXI4 Slave Interface
        .s_axi_awid     (ddr_s_axi_awid),
        .s_axi_awaddr   (ddr_s_axi_awaddr),
        // ... connect all AXI4 signals
    );
    
    // SRAM Controller (receives AXI4 slave transactions)
    sram_controller u_sram (
        .clk            (aclk),
        .rst_n          (aresetn),
        // AXI4 Slave Interface
        .s_axi_awid     (sram_s_axi_awid),
        // ... connect all AXI4 signals
    );

endmodule
```

---

#### Step 3: Signal Connection Checklist

**Master Interface Connections (Bridge Inputs):**

| Signal Type | Count | Direction | Notes |
|-------------|-------|-----------|-------|
| AW Channel | ~12 signals | Input | Write address channel |
| W Channel | ~4 signals | Input | Write data channel |
| B Channel | ~3 signals | Output | Write response channel |
| AR Channel | ~12 signals | Input | Read address channel |
| R Channel | ~5 signals | Output | Read data channel |

**Slave Interface Connections (Bridge Outputs):**

| Signal Type | Count | Direction | Notes |
|-------------|-------|-----------|-------|
| AW Channel | ~12 signals | Output | Write address channel |
| W Channel | ~4 signals | Output | Write data channel |
| B Channel | ~3 signals | Input | Write response channel |
| AR Channel | ~12 signals | Output | Read address channel |
| R Channel | ~5 signals | Input | Read data channel |

**Total Signals (2 masters × 2 slaves):**
- ~200-250 signal connections
- Generator creates consistent naming for easy connection

---

#### Step 4: Clock and Reset Strategy

**Single Clock Domain (Simplest):**
```systemverilog
// All components share same clock
assign aclk = system_clk;
assign aresetn = system_rst_n;

my_first_bridge u_bridge (
    .aclk    (aclk),
    .aresetn (aresetn),
    // ...
);
```

**Multiple Clock Domains (CDC Required):**
```systemverilog
// Masters on fast clock
assign master_aclk = cpu_clk;      // 400 MHz

// Slaves on slow clock  
assign slave_aclk = mem_clk;       // 200 MHz

// Bridge on fast clock with CDC at outputs
my_first_bridge u_bridge (
    .aclk    (master_aclk),
    .aresetn (master_aresetn),
    // ...
);

// CDC FIFOs between bridge and slaves
axi_cdc_fifo u_ddr_cdc (
    .s_aclk         (master_aclk),
    .s_aresetn      (master_aresetn),
    .s_axi_*        (ddr_s_axi_*),      // From bridge
    
    .m_aclk         (slave_aclk),
    .m_aresetn      (slave_aresetn),
    .m_axi_*        (ddr_cdc_s_axi_*),  // To DDR controller
);
```

**Reset Sequence:**
1. Assert `aresetn = 0` for at least 10 clock cycles
2. De-assert `aresetn = 1` on clock edge
3. Bridge clears all internal state
4. Ready for transactions

---

#### Step 5: Address Map Verification

**Verify your configuration matches your SoC address map:**

```systemverilog
// In your TOML configuration:
[[slaves]]
name = "ddr_slave"
base_addr = 0x00000000    # Must match DDR base address!
size = 0x40000000         # Must match DDR size!

[[slaves]]
name = "sram_slave"
base_addr = 0x40000000    # Must match SRAM base address!
size = 0x10000000         # Must match SRAM size!
```

**Address Decode Logic:**
```
CPU writes to 0x00001000:
  → Address decoder: 0x00001000 in [0x00000000, 0x40000000)?
  → YES → Route to DDR slave
  → Transaction reaches DDR controller

CPU writes to 0x40000100:
  → Address decoder: 0x40000100 in [0x40000000, 0x50000000)?
  → YES → Route to SRAM slave
  → Transaction reaches SRAM controller

CPU writes to 0x80000000:
  → Address decoder: No match found
  → Bridge returns DECERR (decode error)
  → Transaction fails gracefully
```

---

#### Step 6: Compile and Verify

**Synthesis Check (Vivado Example):**

```tcl
# Add bridge files
read_verilog -f rtl/generated/my_first_bridge/my_first_bridge.f

# Add your design
read_verilog my_soc_top.sv

# Synthesize
synth_design -top my_soc_top -part xcvu9p-flga2104-2-i

# Check for errors
report_timing_summary
report_utilization
```

**Expected Results:**
- No syntax errors
- No unconnected ports
- Timing clean (or with known violations)
- LUT/FF usage as expected (~2K-5K LUTs for 2x2 bridge)

---

#### Common Integration Issues

**Issue 1: Port Width Mismatch**
```
Error: Port 'cpu_m_axi_awaddr' is 32 bits, but signal 'cpu_awaddr' is 64 bits
```

**Solution:**
- Check TOML `addr_width` matches your component's address width
- Regenerate bridge with correct widths

**Issue 2: Unconnected Signals**
```
Warning: Signal 'cpu_m_axi_awqos' is unconnected
```

**Solution:**
- AXI4 QoS signals may be optional
- Tie to appropriate values if unused: `assign cpu_m_axi_awqos = 4'b0;`

**Issue 3: Timing Violation**
```
Critical Path: cpu_master_adapter → crossbar (failed by 0.5 ns)
```

**Solution:**
- See Chapter 6: Performance for pipeline options
- Consider adding FIFOs at adapter outputs
- Reduce clock frequency temporarily

---

#### Integration Checklist

Before releasing your design:

- [ ] All bridge files added to compilation
- [ ] Bridge instantiated in top-level
- [ ] All masters connected (inputs)
- [ ] All slaves connected (outputs)
- [ ] Clock connected to `aclk`
- [ ] Reset connected to `aresetn`
- [ ] Address map verified against TOML
- [ ] No unconnected ports
- [ ] Synthesis clean (no errors)
- [ ] Timing analyzed (no critical violations)
- [ ] Simulation clean (if available)

---

#### Example Projects

**Reference Implementations:**

```
projects/components/bridge/examples/
├── simple_2x2/           # Basic 2 master, 2 slave
├── cpu_with_dma/         # CPU + DMA + memory hierarchy
└── soc_integration/      # Full SoC with peripherals
```

**See Chapter 4: Programming → Integration Examples** for complete working examples.

---

#### Next Steps

**Integration complete?** ✅

You now have a working SoC with AXI4 crossbar!

**Additional Resources:**
- **Chapter 1: Overview** - Understand bridge architecture
- **Chapter 2: Blocks** - Detailed micro-architecture
- **Chapter 3: Interfaces** - Complete signal specifications
- **Chapter 4: Programming** - Advanced configuration
- **Chapter 6: Performance** - Optimization and pipelining

---

#### Troubleshooting Resources

**Having issues?**
- **Chapter 5: Verification** - Test execution and debugging
- **Appendix A: Generator** - Understanding the generator internals
- **Appendix B: Internals** - Advanced development topics

---

**Integration Complete!** 🎉

Your bridge is now integrated into your SoC design. You've completed the Quick Start guide!

**What You've Accomplished:**
- ✅ Installed tools and dependencies
- ✅ Generated your first bridge (2x2 configuration)
- ✅ Ran simulations and verified functionality
- ✅ Integrated bridge into SystemVerilog design
- ✅ Ready for synthesis or further development

**Key Takeaways:**
- Bridge generator simplifies AXI4 crossbar creation
- Generated RTL is production-ready
- Integration is straightforward with consistent signal naming
- Address map configuration is critical
- CocoTB provides comprehensive verification

---

**Welcome to the Bridge Component!**

You're now ready to create complex SoC interconnects with confidence. Explore the full specification for advanced features:
- Mixed data widths
- Channel-specific masters (rd/wr optimization)
- APB protocol conversion
- Deep pipeline options
- And much more!

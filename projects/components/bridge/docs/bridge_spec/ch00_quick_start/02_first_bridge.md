### Quick Start - Your First Bridge

#### Overview

In this tutorial, you'll generate a simple **2×2 AXI4 crossbar bridge** (2 masters, 2 slaves) in under 5 minutes.

**What You'll Create:**
- 2 master interfaces (CPU, DMA)
- 2 slave interfaces (DDR, SRAM)
- Full AXI4 protocol support
- Address-based routing
- Generated in ~1000 lines of SystemVerilog

---

#### Step 1: Create Configuration Directory

```bash
cd ~/github/rtldesignsherpa/projects/components/bridge
mkdir -p my_bridges
cd my_bridges
```

---

#### Step 2: Create TOML Configuration

Create a file named `my_first_bridge.toml`:

```toml
bridge_name = "my_first_bridge"

[[masters]]
name = "cpu_master"
prefix = "cpu_m_axi_"
type = "axi4"
channels = "rw"           # Read-write (full 5-channel AXI4)
data_width = 64
addr_width = 32
id_width = 4

[[masters]]
name = "dma_master"
prefix = "dma_m_axi_"
type = "axi4"
channels = "rw"
data_width = 64
addr_width = 32
id_width = 4

[[slaves]]
name = "ddr_slave"
prefix = "ddr_s_axi_"
type = "axi4"
channels = "rw"
data_width = 64
addr_width = 32
id_width = 4
base_addr = 0x00000000
size = 0x40000000          # 1GB

[[slaves]]
name = "sram_slave"
prefix = "sram_s_axi_"
type = "axi4"
channels = "rw"
data_width = 64
addr_width = 32
id_width = 4
base_addr = 0x40000000
size = 0x10000000          # 256MB

[[connectivity]]
master = "cpu_master"
slaves = ["ddr_slave", "sram_slave"]

[[connectivity]]
master = "dma_master"
slaves = ["ddr_slave", "sram_slave"]
```

---

#### Step 3: Create Connectivity CSV

Create a file named `my_first_bridge_connectivity.csv`:

```csv
,ddr_slave,sram_slave
cpu_master,1,1
dma_master,1,1
```

**What This Means:**
- `1` = connection allowed
- `0` = connection blocked (not used here)
- Both masters can access both slaves

---

#### Step 4: Generate the Bridge

**Run the generator:**

```bash
cd ~/github/rtldesignsherpa/projects/components/bridge

python bin/bridge_generator.py \
    --config my_bridges/my_first_bridge.toml \
    --connectivity my_bridges/my_first_bridge_connectivity.csv \
    --output rtl/generated/ \
    --verbose
```

**Expected Output:**
```
Bridge Generator v2.1
=====================
Reading configuration: my_bridges/my_first_bridge.toml
Reading connectivity: my_bridges/my_first_bridge_connectivity.csv
Validating configuration...
  ✓ 2 masters, 2 slaves
  ✓ Address ranges validated
  ✓ Connectivity matrix validated

Generating package: rtl/generated/my_first_bridge/my_first_bridge_pkg.sv
Generating adapters:
  ✓ cpu_master_adapter.sv
  ✓ dma_master_adapter.sv
Generating crossbar: my_first_bridge_xbar.sv
Generating top-level: my_first_bridge.sv
Generating filelist: my_first_bridge.f

Generation complete! ✅
Output: rtl/generated/my_first_bridge/
```

---

#### Step 5: Examine Generated Files

```bash
cd rtl/generated/my_first_bridge
ls -la
```

**Generated Files:**
```
my_first_bridge/
├── my_first_bridge.sv           # Top-level bridge module
├── my_first_bridge_pkg.sv       # Package with types
├── my_first_bridge_xbar.sv      # Crossbar routing logic
├── cpu_master_adapter.sv        # CPU adapter
├── dma_master_adapter.sv        # DMA adapter
└── my_first_bridge.f            # Filelist for compilation
```

**Quick Look at Top-Level:**
```systemverilog
module my_first_bridge (
    input  logic        aclk,
    input  logic        aresetn,
    
    // CPU Master Interface (64-bit)
    input  logic [3:0]  cpu_m_axi_awid,
    input  logic [31:0] cpu_m_axi_awaddr,
    // ... all AXI4 signals
    
    // DMA Master Interface (64-bit)
    input  logic [3:0]  dma_m_axi_awid,
    // ...
    
    // DDR Slave Interface (64-bit)
    output logic [3:0]  ddr_s_axi_awid,
    output logic [31:0] ddr_s_axi_awaddr,
    // ...
    
    // SRAM Slave Interface (64-bit)
    output logic [3:0]  sram_s_axi_awid,
    // ...
);
```

---

#### Step 6: Quick Lint Check

**Verify the generated RTL with Verilator:**

```bash
cd ~/github/rtldesignsherpa/projects/components/bridge

verilator --lint-only \
    -f rtl/generated/my_first_bridge/my_first_bridge.f \
    rtl/generated/my_first_bridge/my_first_bridge.sv
```

**Expected Output:**
```
%Info: my_first_bridge.sv: No lint warnings
```

**If you see warnings:**
- Most warnings are informational
- Check for actual errors (not warnings)
- See Chapter 5: Verification → Troubleshooting

---

#### Understanding the Generated Bridge

**Architecture:**
```
┌──────────────────────────────────────────────────────────┐
│              my_first_bridge Top-Level                   │
│                                                          │
│  CPU Master  ──▶ [cpu_master_adapter] ──┐             │
│                                          │              │
│  DMA Master  ──▶ [dma_master_adapter] ──┤              │
│                                          ▼              │
│                                   [Crossbar 2x2]        │
│                                          │              │
│                                          ├──▶ DDR Slave │
│                                          └──▶ SRAM Slave│
└──────────────────────────────────────────────────────────┘
```

**Key Features:**
- **Adapters**: Handle width conversion, address decode, timing isolation
- **Crossbar**: Routes transactions based on address ranges
- **Arbitration**: Fair round-robin when both masters target same slave
- **ID Tracking**: Supports out-of-order completion via transaction IDs

---

#### Next-Level: Try Different Configurations

**Example 2: Mixed Data Widths**
```toml
# masters/cpu has 32-bit data
data_width = 32

# slaves/ddr has 64-bit data  
data_width = 64
```
*Generator automatically inserts width converters!*

**Example 3: Channel-Specific Masters**
```toml
# Read-only master (saves 39% ports)
channels = "rd"

# Write-only master (saves 61% ports)
channels = "wr"
```
*Optimizes for dedicated memory transfer engines!*

**Example 4: APB Slaves**
```toml
[[slaves]]
type = "apb"           # APB slave instead of AXI4
# Generator inserts AXI4-to-APB protocol converter
```

---

#### Common Beginner Mistakes

**❌ Mistake 1: Overlapping Address Ranges**
```toml
base_addr = 0x00000000, size = 0x80000000  # Slave 0
base_addr = 0x40000000, size = 0x80000000  # Slave 1 (OVERLAP!)
```
**✅ Solution:** Generator validates and reports error

**❌ Mistake 2: Disconnected Masters**
```csv
,ddr_slave,sram_slave
cpu_master,0,0          # CPU can't access anything!
```
**✅ Solution:** At least one connection per master

**❌ Mistake 3: Mismatched ID Widths**
```toml
masters.id_width = 4    # 4-bit IDs
slaves.id_width = 2     # 2-bit IDs (MISMATCH!)
```
**✅ Solution:** Keep id_width consistent (or generator extends)

---

#### Troubleshooting

**Problem: `FileNotFoundError: my_first_bridge.toml`**
- Check file path and name
- Ensure you're in the correct directory

**Problem: `Address overlap detected`**
- Check base_addr and size for each slave
- Use non-overlapping ranges

**Problem: `Verilator: syntax error`**
- Check TOML syntax (proper quotes, brackets)
- Validate with: `python -c "import toml; toml.load('my_first_bridge.toml')"`

---

#### Next Steps

Your bridge is generated! Now what?

- **[03_simulation.md](03_simulation.md)** - Test your bridge with CocoTB
- **[04_integration.md](04_integration.md)** - Integrate into your SoC

---

**Congratulations!** 🎉

You've generated your first AXI4 crossbar bridge. The entire process took under 5 minutes, and you have production-ready RTL.

**Key Takeaways:**
- TOML configuration is human-readable
- Generator handles complex logic automatically
- Lint-clean RTL generated
- Ready for simulation and synthesis

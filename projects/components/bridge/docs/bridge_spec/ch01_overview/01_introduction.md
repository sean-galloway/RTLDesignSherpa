### Bridge - Introduction

#### What is Bridge?

**Bridge** is a Python-based AXI4 crossbar generator that creates parameterized SystemVerilog RTL from human-readable CSV configuration files. It solves the problem of manually writing complex AXI4 crossbars by automating RTL generation, converter insertion, and signal routing.

![Bridge Architecture Concept](../assets/images/bridge_concept.svg)

**Key Innovation:** CSV-driven configuration makes complex crossbars accessible to:
- RTL designers without deep AXI4 expertise
- System architects defining interconnect topology
- Verification engineers needing configurable testbenches
- Students learning AXI4 protocol and interconnects

#### The Problem Bridge Solves

**Manual AXI4 Crossbar Development is Error-Prone:**

Creating an AXI4 crossbar manually requires:
1. Writing 5 separate channel multiplexers (AW, W, B, AR, R)
2. Implementing per-slave arbitration for each channel
3. Managing ID-based response routing for out-of-order support
4. Handling burst locking and interleaving constraints
5. Inserting width converters for data width mismatches
6. Inserting protocol converters for APB/AXI4 mixed systems
7. Wiring hundreds of signals with consistent naming

**Bridge Automates All of This:**
- Define ports and connectivity in CSV files
- Run generator script
- Get production-ready SystemVerilog RTL

#### Key Features

**CSV Configuration:**
- **ports.csv** - Define each master and slave port with custom signal prefixes
- **connectivity.csv** - Specify which masters connect to which slaves
- Human-readable, version-control friendly

**Automatic Converter Insertion:**
- **Width converters** - Handle data width mismatches (upsize/downsize)
- **Protocol converters** - Convert AXI4 to APB for peripheral slaves
- Optimized for resource efficiency

**Channel-Specific Masters (New in Phase 2):**
- **Write-only masters** (wr) - Generate AW, W, B channels only
- **Read-only masters** (rd) - Generate AR, R channels only
- **Full masters** (rw) - Generate all 5 channels
- Matches real hardware architectures (RAPIDS, STREAM)
- Reduces resource usage (fewer ports, less logic)

**Flexible Topology:**
- M masters x N slaves (1-32 masters, 1-256 slaves)
- Partial connectivity - not all masters need access to all slaves
- Mixed protocols - AXI4 and APB slaves in same crossbar
- Mixed data widths - 32b, 64b, 128b, 512b, etc.

#### Applications

**SoC Interconnects:**
- Multi-core processor memory subsystems
- Accelerator integration (GPU, DSP, custom logic)
- DMA engine routing
- Peripheral bus bridges

**Memory Systems:**
- Multi-port DDR controllers
- SRAM buffer sharing
- Cache coherency interconnects
- Memory-mapped I/O

**Rapid Prototyping:**
- Quick topology exploration
- Performance analysis
- Design space exploration
- Educational projects

#### Example Use Case: RAPIDS Accelerator

The RAPIDS (Rapid AXI Programmable In-band Descriptor System) accelerator has:
- **Descriptor write master** - Writes control descriptors to memory (write-only)
- **Sink write master** - Writes incoming data packets to memory (write-only)
- **Source read master** - Reads outgoing data packets from memory (read-only)
- **CPU configuration master** - Configures registers via APB (full AXI4 converted to APB)

**Manual Crossbar:** Would require full 5-channel interfaces for all masters (wasteful)

**Bridge CSV Configuration:**
```csv
port_name,direction,protocol,channels,prefix,data_width,...
rapids_descr_wr,master,axi4,wr,rapids_descr_m_axi_,512,...
rapids_sink_wr,master,axi4,wr,rapids_sink_m_axi_,512,...
rapids_src_rd,master,axi4,rd,rapids_src_m_axi_,512,...
cpu_master,master,axi4,rw,cpu_m_axi_,64,...
```

**Result:** Optimized RTL with only the channels each master actually uses.

#### Design Philosophy

**Human-Friendly Configuration:**
CSV files are easy to read, write, and maintain. No programming knowledge required. Version control diffs show exactly what changed.

**Resource Efficiency:**
Generate only what's needed. Write-only masters don't get read channels. Read-only masters don't get write channels. Width converters only for necessary directions.

**Standards Compliance:**
Full AMBA AXI4 protocol compliance. Generated RTL passes Verilator lint. Compatible with industry-standard tools.

**Reusability:**
Same generator supports diverse topologies. Parameterized RTL adapts to configuration. Easy integration into larger designs.

#### Workflow

**1. Define Configuration:**
```csv
# ports.csv
port_name,direction,protocol,channels,prefix,data_width,addr_width,id_width,base_addr,addr_range
cpu_master,master,axi4,rw,cpu_m_axi_,64,32,4,N/A,N/A
ddr_controller,slave,axi4,rw,ddr_s_axi_,512,64,8,0x80000000,0x80000000
```

```csv
# connectivity.csv
master\slave,ddr_controller
cpu_master,1
```

**2. Generate RTL:**
```bash
python3 bridge_csv_generator.py \
    --ports ports.csv \
    --connectivity connectivity.csv \
    --name my_bridge \
    --output rtl/
```

**3. Integrate:**
```systemverilog
my_bridge u_bridge (
    .aclk      (sys_clk),
    .aresetn   (sys_rst_n),
    // Master ports
    .cpu_m_axi_awaddr  (cpu_awaddr),
    // ... other signals
    // Slave ports
    .ddr_s_axi_awaddr  (ddr_awaddr),
    // ... other signals
);
```

#### Comparison with Other Generators

| Feature | Manual RTL | APB Crossbar | Delta (AXIS) | **Bridge (AXI4)** |
|---------|-----------|--------------|--------------|-------------------|
| **Configuration** | Verilog code | Python script | Python script | **CSV files** |
| **Protocol** | Any | APB | AXI-Stream | **AXI4 Full** |
| **Channels** | All 5 manual | 1 | 1 | **5 (configurable)** |
| **Out-of-Order** | Manual | No | No | **Yes (ID-based)** |
| **Mixed Protocols** | Manual | No | No | **Yes (AXI4 + APB)** |
| **Width Converters** | Manual | No | No | **Yes (automatic)** |
| **Channel-Specific** | Manual | N/A | N/A | **Yes (wr/rd/rw)** |
| **Learning Curve** | High | Low | Low | **Very Low** |

#### Development Status

**Phase 1 Complete:** CSV parsing, port generation, converter identification
**Phase 2 Complete:** Channel-specific masters, optimized converters
**Phase 3 Planned:** APB converter implementation, slave-side downsize

**Current Capabilities:**
- Generate AXI4 crossbar with custom port prefixes ✅
- Parse CSV configuration files ✅
- Identify required converters (width, protocol) ✅
- Generate master-side width upsizers ✅
- Support channel-specific masters (wr/rd/rw) ✅
- Generate crossbar instantiation ✅

**Future Enhancements:**
- Implement APB converter placeholders 🔲
- Add slave-side width downsizers 🔲
- Support variable-width internal crossbar 🔲
- Add performance monitoring hooks 🔲

#### Documentation Organization

This specification is organized as follows:

- **Chapter 1 (this chapter)**: Overview, features, applications, workflow
- **Chapter 2**: CSV generator design and CSV file formats
- **Chapter 3**: Generated RTL structure and components
  - **Arbiter FSMs** - Per-slave AW/AR arbitration state machines ([3.2](../ch03_generated_rtl/02_arbiter_fsms.md))
  - **Crossbar Core** - Internal NxM interconnect matrix
  - **Width Converters** - Data width upsize/downsize
  - **APB Converters** - AXI4-to-APB protocol conversion
- **Chapter 4**: Usage examples for common scenarios

**Related Documentation:**
- `../../PRD.md` - Detailed product requirements
- `../../CLAUDE.md` - AI integration guide for development
- `../../CSV_BRIDGE_STATUS.md` - Phase-by-phase implementation status
- `../../bin/bridge_csv_generator.py` - Generator source code

**PlantUML FSM Diagrams:**
- [AW Arbiter FSM](../assets/puml/aw_arbiter_fsm.svg) - Write address arbiter state machine
- [AR Arbiter FSM](../assets/puml/ar_arbiter_fsm.svg) - Read address arbiter state machine

**Graphviz Block Diagrams:**
- [Bridge 2×2 Configuration](../assets/graphviz/bridge_2x2.svg) - 2 masters, 2 slaves block diagram
- [Bridge 1×4 Configuration](../assets/graphviz/bridge_1x4.svg) - 1 master, 4 slaves block diagram

---

**Next:** [1.2 - Architecture](02_architecture.md)

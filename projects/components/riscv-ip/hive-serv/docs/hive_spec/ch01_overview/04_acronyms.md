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

# Chapter 1.4: Acronyms and Glossary

## A

**AXIS (AXI4-Stream)**
- Streaming interface protocol, subset of AXI with no addressing
- Used for packet-oriented data transfer in HIVE system
- TUSER field carries packet type encoding (PKT_DATA, CDA, PKT_CONFIG, PKT_STATUS)

**AXI4**
- Advanced eXtensible Interface version 4
- AMBA standard for high-performance memory-mapped communication
- Not directly used in HIVE (RAPIDS uses AXI4 for DDR access)

**AXI4-Lite**
- Simplified subset of AXI4 for control/status registers
- Used for HIVE-C external host interface
- 32-bit data width typical

---

## B

**BRAM (Block RAM)**
- Dedicated memory blocks in FPGA fabric
- Used for instruction/data memory in HIVE-C and SERV monitors
- Each block: 36Kb on Xilinx Artix-7

---

## C

**CDA (Compute Direct Access)**
- Packet type for descriptor injection from HIVE-C to RAPIDS
- Encoded as TUSER=2'b01 in AXIS packets
- Replaces the generic term "PKT_DESC" in HIVE context
- Format: 256-bit descriptor structure

**CDC (Clock Domain Crossing)**
- Transfer of signals between different clock domains
- Requires special synchronization (FIFOs, synchronizers) to prevent metastability

---

## D

**Delta Network**
- 4×4 mesh Network-on-Chip for compute fabric
- Packet-switched interconnect with virtual channels
- 16 compute tiles (0-15) + 2 virtual tiles (16=RAPIDS, 17=HIVE-C)

**DMA (Direct Memory Access)**
- Hardware engine for memory transfers without CPU intervention
- RAPIDS implements DMA functionality with inband descriptor injection

**DSP (Digital Signal Processor)**
- Dedicated multiply-accumulate blocks in FPGA
- Used for compute elements in Delta Network tiles
- HIVE consumes zero DSPs (all available for compute)

---

## F

**Flit (Flow Control Unit)**
- Atomic packet fragment in Network-on-Chip
- Smallest unit of flow control
- HIVE uses 128-bit flits for Delta Network

**FPGA (Field-Programmable Gate Array)**
- Reconfigurable hardware platform
- Target: Digilent NexysA7 100T (Xilinx Artix-7)

---

## H

**HIVE (Hierarchical Intelligent Vector Environment)**
- Distributed control and monitoring subsystem
- Coordinates RAPIDS DMA engine and Delta Network
- Hierarchical RISC-V architecture (1 VexRiscv + 16 SERV cores)

**HIVE-C (HIVE Controller)**
- Master VexRiscv controller in HIVE system
- Virtual Tile 17 in Delta Network topology
- Responsibilities: RAPIDS coordination, network reconfiguration, performance monitoring

---

## I

**Inband Control**
- Control messages sent through data network rather than separate bus
- HIVE-C injects CDA packets through Delta Network to RAPIDS
- Lower latency than memory-mapped polling (10-20 cycles vs. 100+)

---

## L

**LUT (Look-Up Table)**
- Basic logic element in FPGA
- 6-input LUT typical in Xilinx Artix-7
- HIVE budget: ~14,100 LUTs

---

## M

**MM2S (Memory-to-Stream)**
- Data path direction: DDR memory → Delta Network
- RAPIDS reads from memory, sends to compute tiles via AXIS

**MTBF (Mean Time Between Failures)**
- Reliability metric for CDC synchronizers
- Higher MTBF = lower metastability risk

---

## N

**NoC (Network-on-Chip)**
- Packet-switched interconnect for on-chip communication
- Delta Network implements 4×4 mesh NoC topology

---

## P

**PKT_DATA**
- Packet type for compute data (activations, weights, results)
- Encoded as TUSER=2'b00
- Routed through Delta Network to compute tiles

**PKT_CONFIG**
- Packet type for configuration commands
- Encoded as TUSER=2'b10
- Routed to tile configuration registers or Delta Network routers

**PKT_STATUS**
- Packet type for status/monitoring data
- Encoded as TUSER=2'b11
- Routed to HIVE-C monitoring aggregator (virtual tile 17)

**PLL (Phase-Locked Loop)**
- Clock generation and frequency synthesis
- Used to derive different clock frequencies from single source

---

## R

**RAPIDS (Rapid AXI Programmable In-band Descriptor System)**
- Custom DMA engine with network interfaces
- Virtual Tile 16 in Delta Network topology
- Controlled by HIVE-C via CDA packet injection

**RISC-V**
- Open-source instruction set architecture
- HIVE uses VexRiscv and SERV implementations

---

## S

**S2MM (Stream-to-Memory)**
- Data path direction: Delta Network → DDR memory
- RAPIDS receives from compute tiles via AXIS, writes to memory
- 16 independent S2MM channels (one per compute tile)

**SERV (Small Embedded RISC-V)**
- World's smallest RISC-V core, bit-serial implementation
- RV32I instruction set
- Used for per-tile traffic monitoring (16 monitors in HIVE)

**SimPy**
- Discrete-event simulation framework in Python
- Used for HIVE performance modeling and "what-if" analysis

**SoC (System-on-Chip)**
- Complete system integrated on single chip
- HIVE+RAPIDS+Delta forms educational SoC platform

---

## T

**TDEST (AXIS Destination Field)**
- AXI-Stream sideband signal for routing
- Encodes destination tile ID (0-15 compute, 16 RAPIDS, 17 HIVE-C)

**TID (AXIS Transaction ID Field)**
- AXI-Stream sideband signal for transaction identification
- CRITICAL: Encodes source tile ID for RAPIDS S2MM channel routing
- Hardware-enforced override for compute element packets (security)

**TLAST (AXIS Last Field)**
- AXI-Stream signal indicating last beat of packet

**TUSER (AXIS User Field)**
- AXI-Stream sideband signal for user-defined control
- HIVE uses TUSER[1:0] for packet type encoding:
  - 2'b00 = PKT_DATA
  - 2'b01 = CDA (Compute Direct Access)
  - 2'b10 = PKT_CONFIG
  - 2'b11 = PKT_STATUS

---

## U

**UART (Universal Asynchronous Receiver-Transmitter)**
- Serial communication interface
- Used for HIVE-C external host interface (alternative to AXI4-Lite)

---

## V

**VC (Virtual Channel)**
- Logically independent queue sharing physical link
- Delta Network uses 2 VCs for deadlock avoidance
- Enables concurrent traffic classes on same physical link

**VexRiscv**
- RISC-V core generator written in SpinalHDL
- RV32IM configuration for HIVE-C
- 5-stage pipeline, configurable performance/area tradeoff

**Virtual Tile**
- Logical endpoint in Delta Network not corresponding to physical tile
- Virtual Tile 16: RAPIDS DMA engine
- Virtual Tile 17: HIVE-C master controller

---

## X

**XY Routing**
- Dimension-ordered routing algorithm
- First route in X-dimension (East/West), then Y-dimension (North/South)
- Deadlock-free with 2 virtual channels

---

**Next:** [References](05_references.md)

**Back to:** [Index](../hive_index.md) | [Clocks and Reset](03_clocks_and_reset.md)

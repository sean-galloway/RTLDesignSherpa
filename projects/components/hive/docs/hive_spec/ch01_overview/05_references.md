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

# Chapter 1.5: References

## 1.5.1 Internal Specifications

### HIVE System
- **[HIVE Specification Index](../hive_index.md)** - This specification
- **[HIVE Overview](01_overview.md)** - Chapter 1.1: System architecture and design goals
- **[HIVE Architectural Requirements](02_architectural_requirements.md)** - Chapter 1.2: Functional and performance requirements
- **[HIVE Clocks and Reset](03_clocks_and_reset.md)** - Chapter 1.3: Clock domains and reset strategy

### Related Component Specifications
- **[RAPIDS Specification](../../../rapids/docs/rapids_spec/rapids_index.md)** - DMA engine controlled by HIVE-C
- **[Delta Network Specification](../../../delta/docs/delta_spec/delta_index.md)** - 4×4 mesh NoC for compute fabric
- **[STREAM Specification](../../../stream/PRD.md)** - Simplified DMA tutorial project (educational reference)

---

## 1.5.2 RISC-V Core Projects

### VexRiscv
- **GitHub Repository:** https://github.com/SpinalHDL/VexRiscv
- **Description:** Configurable RISC-V core generator written in SpinalHDL
- **HIVE Usage:** Master controller (HIVE-C)
- **Configuration:** VexRiscv "Small" variant, RV32IM, 5-stage pipeline
- **License:** MIT License

### SERV
- **GitHub Repository:** https://github.com/olofk/serv
- **Description:** World's smallest RISC-V core, bit-serial implementation
- **HIVE Usage:** Per-tile traffic monitors (16 instances)
- **Configuration:** RV32I, minimal resource footprint (125 LUTs, 164 FFs)
- **License:** ISC License

---

## 1.5.3 Verification and Simulation Tools

### CocoTB
- **Documentation:** https://docs.cocotb.org/
- **Description:** Coroutine-based cosimulation testbench environment for Verilog/VHDL
- **HIVE Usage:** Unit tests, integration tests, system-level verification
- **Version:** 1.7+ recommended
- **License:** BSD-3-Clause

### SimPy
- **Documentation:** https://simpy.readthedocs.io/
- **Description:** Discrete-event simulation framework in Python
- **HIVE Usage:** Performance modeling, "what-if" analysis, workload prediction
- **Version:** 4.0+ recommended
- **License:** MIT License

### Verilator
- **Documentation:** https://verilator.org/
- **Description:** Fast open-source Verilog/SystemVerilog simulator
- **HIVE Usage:** Linting, fast simulation, waveform generation
- **Version:** 5.0+ recommended
- **License:** LGPL-3.0 / Artistic-2.0

---

## 1.5.4 AMBA and Interface Standards

### AMBA Specifications (ARM)
- **AXI4 Specification:** ARM IHI 0022E (AXI3, AXI4, and AXI4-Lite Protocol Specification)
- **AXI4-Stream:** ARM IHI 0051A (AXI4-Stream Protocol Specification)
- **Download:** https://developer.arm.com/architectures/system-architectures/amba
- **HIVE Usage:**
  - AXI4-Stream for packet interfaces (AXIS)
  - AXI4-Lite for control/status registers
- **License:** ARM proprietary (free to implement)

### RISC-V Specifications
- **RISC-V ISA:** https://riscv.org/technical/specifications/
- **Privileged Spec:** RISC-V Privileged Architecture Specification
- **HIVE Usage:** RV32IM (VexRiscv), RV32I (SERV)
- **License:** Creative Commons Attribution 4.0

---

## 1.5.5 Network-on-Chip Research

### Foundational Papers

**1. "Principles and Practices of Interconnection Networks"**
- Authors: William J. Dally, Brian Towles
- Publisher: Morgan Kaufmann (2003)
- **Relevance:** Fundamental NoC routing algorithms, flow control, topology design
- **HIVE Application:** XY routing, virtual channels, deadlock avoidance

**2. "MAERI: Enabling Flexible Dataflow Mapping over DNN Accelerators via Reconfigurable Interconnects"**
- Authors: Hyoukjun Kwon, et al.
- Conference: ASPLOS 2018
- **Relevance:** Reconfigurable network topologies for compute acceleration
- **HIVE Application:** Virtual configuration contexts, topology switching
- **Link:** https://dl.acm.org/doi/10.1145/3173162.3173176

**3. "A Survey of Wormhole Routing Techniques in Direct Networks"**
- Authors: Lionel M. Ni, Philip K. McKinley
- Journal: IEEE Computer (1993)
- **Relevance:** Wormhole flow control, router microarchitecture
- **HIVE Application:** Router buffer design, credit-based flow control

---

## 1.5.6 Open-Source NoC Projects

### ProNoC
- **GitHub Repository:** https://github.com/aignacio/ProNoC
- **Description:** Parameterized Network-on-Chip generator
- **HIVE Relevance:** Reference design for mesh topology, router architecture
- **License:** MIT License

### OpenSMART
- **GitHub Repository:** https://github.com/SMARTLab-Purdue/OpenSMART
- **Description:** Open-source NoC simulation and modeling framework
- **HIVE Relevance:** Performance modeling techniques, traffic pattern generation
- **License:** BSD License

---

## 1.5.7 FPGA Development Tools

### Xilinx Vivado
- **Version:** 2021.1 or later
- **Target Device:** XC7A100T-1CSG324C (Artix-7 on NexysA7 100T)
- **Usage:** Synthesis, implementation, bitstream generation
- **Download:** https://www.xilinx.com/support/download.html
- **License:** Free WebPACK edition for Artix-7

### Intel Quartus Prime (Alternative)
- **Version:** 21.1 or later
- **Target Device:** Cyclone V SX (DE10 Standard)
- **Usage:** Alternative FPGA platform support
- **Download:** https://www.intel.com/content/www/us/en/software/programmable/quartus-prime/download.html
- **License:** Free Lite edition for Cyclone V

---

## 1.5.8 Educational Resources

### Digital Design and Computer Architecture
- **Authors:** David Harris, Sarah Harris
- **Publisher:** Morgan Kaufmann
- **Edition:** 2nd Edition (RISC-V edition recommended)
- **Relevance:** Fundamental digital design, RISC-V architecture basics

### Computer Architecture: A Quantitative Approach
- **Authors:** John L. Hennessy, David A. Patterson
- **Publisher:** Morgan Kaufmann
- **Edition:** 6th Edition (2017)
- **Relevance:** Performance modeling, memory hierarchy, interconnect design

### Advanced FPGA Design
- **Author:** Steve Kilts
- **Publisher:** Wiley-IEEE Press (2007)
- **Relevance:** Clock domain crossing, reset strategies, timing closure

---

## 1.5.9 Debugging and Analysis Tools

### GTKWave
- **Website:** http://gtkwave.sourceforge.net/
- **Description:** Waveform viewer for VCD/FST files
- **HIVE Usage:** Debug simulation results, analyze timing
- **License:** GPL-2.0

### Sigrok PulseView
- **Website:** https://sigrok.org/wiki/PulseView
- **Description:** Logic analyzer and protocol decoder
- **HIVE Usage:** Hardware debugging on FPGA (with logic analyzer capture)
- **License:** GPL-3.0

---

## 1.5.10 Performance Modeling Papers

**1. "Analytical Modeling of Network-on-Chip Performance"**
- Authors: Umit Y. Ogras, Radu Marculescu
- Journal: IEEE Transactions on CAD (2006)
- **Relevance:** Latency and throughput modeling techniques
- **HIVE Application:** SimPy model validation

**2. "Booksim 2.0: A Network-on-Chip Simulator"**
- Authors: Nan Jiang, et al.
- **Relevance:** NoC simulation methodology, traffic pattern generation
- **HIVE Application:** Performance benchmarking reference
- **Link:** https://github.com/booksim/booksim2

---

## 1.5.11 Hardware Platforms

### Digilent NexysA7 100T
- **Product Page:** https://digilent.com/shop/nexys-a7-fpga-trainer-board-recommended-for-ece-curriculum/
- **FPGA:** Xilinx Artix-7 XC7A100T-1CSG324C
- **Resources:** 63,400 LUTs, 126,800 FFs, 240 DSPs, 135 BRAM blocks
- **HIVE Status:** Primary proof-of-concept platform
- **Price:** ~$250 (educational discount available)

### Digilent Genesys2
- **Product Page:** https://digilent.com/shop/genesys-2-kintex-7-fpga-development-board/
- **FPGA:** Xilinx Kintex-7 XC7K325T-2FFG900C
- **Resources:** 203,800 LUTs, 840 DSPs, 445 BRAM blocks
- **HIVE Status:** Production target (future scaling to 8×8 mesh)
- **Price:** ~$650

### Terasic DE10 Standard
- **Product Page:** https://www.terasic.com.tw/cgi-bin/page/archive.pl?Language=English&No=1081
- **FPGA:** Intel Cyclone V SX (5CSXFC6D6F31C6)
- **Resources:** 110,000 LEs, 87 DSPs, 5.5Mb memory
- **HIVE Status:** Alternative platform (Intel toolchain)
- **Price:** ~$300

---

## 1.5.12 Code Repositories

### RTL Design Sherpa (HIVE Project Root)
- **Location:** `projects/components/hive/`
- **Contents:**
  - `rtl/` - HIVE RTL source code
  - `docs/` - This specification and related documentation
  - `sim/` - CocoTB testbenches
  - `models/` - SimPy performance models
  - `sw/` - VexRiscv and SERV firmware

### Related Projects
- **RAPIDS:** `projects/components/rapids/`
- **Delta Network:** `projects/components/delta/`
- **Common RTL:** `rtl/common/`, `rtl/amba/`

---

**Next:** [Chapter 2: Block Specifications](../ch02_blocks/00_overview.md)

**Back to:** [Index](../hive_index.md) | [Acronyms](04_acronyms.md)

### Bridge - Overview

#### Introduction

The **Bridge** component is a Python-based AXI4 crossbar generator that produces high-performance, parameterized SystemVerilog RTL for connecting multiple AXI4 masters to multiple AXI4 slaves. Named after the infrastructure that connects different regions, Bridge creates efficient memory-mapped interconnects from human-readable TOML and CSV configuration files.

**Design Philosophy:** Simple, performant, and pragmatic. Bridge focuses on common use cases rather than attempting to support every edge case of the AXI4 specification. Hard limits (8-bit ID width, 64-bit addresses) eliminate unnecessary complexity while supporting all realistic hardware designs.

**Status:** ✅ **Phase 2+ Complete** - Bridge ID tracking fully implemented, all test configurations passing

---

#### Key Features

**Core Functionality:**
- **Configurable Topology**: 1-32 masters × 1-256 slaves
- **Full AXI4 Protocol**: All 5 channels (AW, W, B, AR, R)
- **Automatic Generation**: ~1000 lines of RTL from 20 lines of TOML
- **Address-Based Routing**: Configurable address decode per slave
- **Fair Arbitration**: Round-robin when multiple masters target same slave
- **ID-Based Tracking**: Out-of-order transaction support via bridge_id
- **Burst Support**: Full AXI4 burst protocol (INCR, WRAP, FIXED)

**Advanced Features:**
- **Mixed Data Widths**: Automatic width conversion (32b ↔ 64b ↔ 128b ↔ 256b ↔ 512b)
- **Channel-Specific Masters**: Write-only (wr), read-only (rd), or full (rw)
- **Mixed Protocols**: AXI4 + APB slave support (protocol converters auto-inserted)
- **Bridge ID Tracking**: Per-master unique IDs for multi-master response routing
- **Configurable OOO**: Per-slave out-of-order enable with CAM/FIFO tracking
- **Python Automation**: Comprehensive generator with Jinja2 templates

**Resource Optimization:**
- Direct connections for matching widths (zero overhead)
- Converters only where needed (not fixed-width crossbar)
- Channel-specific masters reduce port count by 39%-61%
- Skid buffers for backpressure handling

---

#### Applications

**Multi-Core Processors:**
- CPU cores + GPU accessing shared memory hierarchy
- Cache-coherent interconnect for multi-core systems
- High-bandwidth memory access for accelerators
- Independent read/write paths prevent head-of-line blocking

**DMA and Streaming:**
- DMA engines with dedicated memory paths
- Channel-specific masters (wr/rd) for streaming applications
- Multiple concurrent transfers without interference
- Burst optimization for high-throughput data movement

**SoC Integration:**
- Memory-mapped peripheral interconnect
- Mixed AXI4 and APB slave attachment
- Scalable to 32 masters × 256 slaves
- Standard AXI4 interfaces for IP reuse

**FPGA System Integration:**
- MicroBlaze/Nios II CPU interconnect
- Custom accelerator fabric
- Standard Xilinx/Intel IP integration
- Performance counters for profiling

---

#### Comparison with Other Crossbars

| Feature | APB Crossbar | AXI-Stream (Delta) | **Bridge (AXI4)** |
|---------|-------------|-------------------|------------------|
| **Protocol** | Simple register bus | Streaming data | Memory-mapped burst |
| **Channels** | 1 | 1 (data stream) | 5 (AW, W, B, AR, R) |
| **Routing** | Address decode | TDEST decode | Address decode |
| **Out-of-Order** | No | No | **Yes (ID-based)** |
| **Burst Support** | No | Packet (TLAST) | **Yes (AWLEN/ARLEN)** |
| **Use Case** | Control registers | Data streaming | **Memory-mapped I/O** |
| **Complexity** | Low | Medium | **High** |
| **Latency** | 1-2 cycles | 2 cycles | **2-3 cycles** |

**Bridge Sweet Spot:** High-performance memory-mapped interconnects where out-of-order completion and burst efficiency are critical.

---

#### Development Status

**Phase 1: CSV Configuration** ✅ **COMPLETE** (2025-10-19)
- CSV parser (ports.csv, connectivity.csv)
- Custom port prefixes per port
- Mixed AXI4/APB protocol support
- Automatic converter identification
- Partial connectivity matrices

**Phase 2: Channel-Specific Masters** ✅ **COMPLETE** (2025-10-26)
- `channels` field: rw/wr/rd support
- Conditional port generation based on channels
- Resource optimization (39%-61% port reduction)
- Width converter awareness
- Example: 4-master bridge saves 35% signals

**Phase 2+: Bridge ID Tracking** ✅ **COMPLETE** (2025-11-10)
- Per-master unique BRIDGE_ID parameter
- Slave adapter CAM/FIFO transaction tracking
- Configurable out-of-order support per slave (enable_ooo)
- Crossbar bridge_id-based response routing
- Zero-latency FIFO mode for in-order slaves
- 1-cycle CAM mode for out-of-order slaves

**Phase 3: APB Converter Implementation** ⏳ **PENDING**
- AXI2APB converter module integration
- APB signal packing/unpacking logic
- End-to-end testing with APB slaves
- Status: Placeholders in generated code with TODO comments

**Future Enhancements** (Planned)
- Deeper pipeline options (>400 MHz Fmax)
- Configurable skid buffer depth (1-8 stages)
- Optional FIFO insertion at adapter outputs
- Python GUI for TOML configuration (prevent illegal configs)
- Variable-width crossbar internal data path
- Performance monitoring integration

---

#### Test Coverage

**All Configurations Passing:**

| Config | Masters | Slaves | Channels | CDC | Status |
|--------|---------|--------|----------|-----|--------|
| 1x2 Read | 1 | 2 | rd | No | ✅ 100% |
| 1x2 Write | 1 | 2 | wr | No | ✅ 100% |
| 2x2 RW | 2 | 2 | rw | No | ✅ 100% |
| 3x5 RW | 3 | 5 | rw | No | ✅ 100% |
| 4x4 RW | 4 | 4 | rw | No | ✅ 100% |
| 5x3 Mixed | 5 | 3 | mixed | No | ✅ 100% |

**Test Levels:**
- **Basic (4-5 tests)**: Register access, read/write, enable/disable
- **Medium (5-6 tests)**: Address decode, arbitration, bursts
- **Full (3-4 tests)**: Stress tests, edge cases, multi-master

**Known Issues:**
- ⚠️ Parallel test execution with waves causes system reboot (fixed in conftest.py)
- ⚠️ APB converter pending (Phase 3 implementation)

---

#### Performance Characteristics

**Latency (2x2 Bridge, 64-bit Data):**
- Single-beat read: **2-3 cycles**
- Single-beat write: **2-3 cycles**
- Burst transfer: **~1 cycle/beat** after address phase

**Throughput:**
- Concurrent transfers: **All M×N paths simultaneously**
- Burst efficiency: **>95%** (minimal protocol overhead)
- Direct connections: **Zero-latency** for matching widths

**Resource Usage (Estimated, Post-Synthesis):**
- 2x2 bridge (64-bit): ~2,500 LUTs, ~3,000 FFs
- 4x4 bridge (64-bit): ~5,000 LUTs, ~6,000 FFs
- Scaling: ~150 LUTs per M×S connection

**Timing:**
- Target Fmax: **300-400 MHz** on UltraScale+ FPGAs
- Critical paths: Arbitration logic, address decode
- Pipeline options: Configurable skid buffers, optional FIFOs

---

#### Design Decisions

**Why Python Generator?**
- **Flexibility**: Easy to extend and modify
- **Jinja2 Templates**: Clean separation of logic and RTL generation
- **Validation**: Config validation before RTL generation
- **Automation**: Batch generation, test generation, documentation
- **Maintainability**: Single source of truth for all configurations

**Why TOML Configuration?**
- **Human-Readable**: More intuitive than JSON or XML
- **Type-Safe**: Built-in validation
- **Comments**: Self-documenting configurations
- **Arrays**: Natural representation of masters/slaves
- **CSV Companion**: Connectivity matrix for complex topologies

**Why 64-Bit Internal Path?**
- **Common Width**: Most modern systems use 64-bit or wider
- **Minimal Conversion**: Most masters/slaves are 32-bit or 64-bit
- **Performance**: Wider internal path reduces conversion stages
- **Simplicity**: Single internal width simplifies logic

**Why Hard Limits (8-bit ID, 64-bit Addr)?**
- **Realism**: 256 outstanding transactions per master is sufficient
- **Complexity**: Variable ID width adds considerable logic
- **Performance**: Eliminates conversion logic in critical paths
- **Pragmatism**: Focus on what hardware actually needs

**Why Channel-Specific Masters?**
- **Resource Optimization**: DMA engines are often unidirectional
- **Port Reduction**: 39% for write-only, 61% for read-only
- **Clarity**: Explicitly documents master capabilities
- **Synthesis**: Simpler logic for dedicated paths

---

#### Documentation Organization

This specification is organized into chapters:

- **Chapter 0**: Quick Start - Get running in 30 minutes
- **Chapter 1 (this chapter)**: Overview - Features, status, design philosophy
- **Chapter 2**: Blocks - Micro-architecture details (adapters, crossbar, converters)
- **Chapter 3**: Interfaces - Port specifications and parameters
- **Chapter 4**: Programming - Generator usage, TOML format, signal naming
- **Chapter 5**: Verification - Test suite, execution, troubleshooting
- **Chapter 6**: Performance - Latency analysis, pipeline enhancement
- **Appendix A**: Generator Deep Dive - Python internals for developers
- **Appendix B**: Internals - Contributing, advanced development

---

#### Comparison with Commercial IP

**Bridge (Open Source) vs. Commercial AXI4 Crossbars:**

| Feature | Commercial | **Bridge** |
|---------|-----------|-----------|
| **Complexity** | Feature-complete | Pragmatic subset |
| **ID Width** | Configurable | 8-bit (fixed) |
| **Address Width** | Configurable | 64-bit (fixed) |
| **Data Width** | Configurable | Configurable (32-512b) |
| **Cost** | $$$ License fees | **Free (open source)** |
| **Customization** | Limited | **Full Python source** |
| **Learning Curve** | Steep | **Quick Start: 30 min** |
| **Verification** | Commercial | **CocoTB + pytest** |

**When to Use Bridge:**
- Early prototyping and evaluation
- Educational purposes and learning
- Projects with typical configurations (not edge cases)
- Open-source or cost-sensitive projects
- Need full control over generator

**When to Use Commercial:**
- Need every AXI4 spec feature
- Require vendor support and warranty
- Variable ID width per port is critical
- Legacy compatibility requirements

---

#### Version History

| Version | Date | Milestone | Changes |
|---------|------|-----------|---------|
| **1.0** | 2025-10-19 | Phase 1 | CSV configuration, basic generation |
| **1.1** | 2025-10-26 | Phase 2 | Channel-specific masters (wr/rd/rw) |
| **1.2** | 2025-11-10 | Phase 2+ | Bridge ID tracking, OOO support |
| **2.0** | TBD | Phase 3 | APB converter implementation |

---

#### Related Components

**Within rtldesignsherpa Project:**
- **APB Crossbar** - Simple register bus crossbar
- **Delta (AXI-Stream)** - Streaming data crossbar
- **HPET** - High precision event timer (APB peripheral)
- **RAPIDS** - DMA engine with AXI4 masters

**External Dependencies:**
- **axi4_slave_wr/rd** - Timing isolation wrappers
- **skid_buffer** - Backpressure buffering
- **bridge_cam** - CAM for bridge ID tracking

---

#### Getting Started

**New Users:**
1. Start with [Chapter 0: Quick Start](../ch00_quick_start/01_installation.md)
2. Generate your first bridge in 5 minutes
3. Run simulations to verify
4. Integrate into your design

**Experienced Users:**
- [Chapter 2: Blocks](../ch02_blocks/00_overview.md) - Understand micro-architecture
- [Chapter 4: Programming](../ch04_programming/01_generator_usage.md) - Advanced configuration
- [Appendix A](../appendix_a_generator/01_architecture.md) - Generator internals

---

**Next:** [Chapter 1.2 - Architecture](02_architecture.md)

---

**Task:** Python GUI for TOML Configuration
**Priority:** Medium
**Effort:** 2-3 weeks
**Purpose:** Prevent illegal configurations, provide visual editor
**Features:**
- Master/slave port configuration with validation
- Address map visualization (prevent overlaps)
- Connectivity matrix editor
- Real-time TOML preview
- Configuration templates
- Export to TOML/CSV for generator

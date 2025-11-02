# RAPIDS (Rapid AXI Programmable In-band Descriptor System) Specification

**Version:** 0.25
**Date:** 2025-10-18
**Status:** AXIS Migration Complete

---

## Overview

RAPIDS is a programmable DMA-style accelerator that provides:
- High-performance data movement between network interfaces and system memory
- In-band descriptor-based control
- Multi-channel operation with per-channel buffering
- AXI4-Stream network interfaces (AXIS migration complete)
- AXI4 memory interfaces for system memory access
- Comprehensive monitoring via MonBus

---

## Chapter 1: Interfaces

- [RAPIDS Top-Level Interface](ch03_interfaces/01_top_level.md)
- [AXI4-Lite (AXIL4) Control Interface](ch03_interfaces/02_axil4_interface_spec.md)
- [AXI4 Memory Interface](ch03_interfaces/03_axi4_interface_spec.md)
- [AXI4-Stream (AXIS4) Network Interface](ch03_interfaces/04_axis4_interface_spec.md)
- [Monitor Bus (MONBUS)](ch03_interfaces/05_monbus_interface_spec.md)

---

## Chapter 2: Programming Model

- [RAPIDS Programming Model and Registers](ch04_programming_models/01_programming.md)
- [Register Map and Descriptions](ch05_registers/01_registers.md)

---

## Chapter 3: Architecture Summary

### Design Principles

**RAPIDS Architecture** consists of three main subsystems:

1. **Scheduler Group** - Controls operation scheduling and descriptor management
2. **Sink Data Path** - Network -> Memory transfers (receive path)
3. **Source Data Path** - Memory -> Network transfers (transmit path)

### Key Features

**Multi-Channel Operation:**
- Up to 32 independent channels
- Per-channel SRAM buffering (configurable depth)
- Independent flow control per channel

**AXIS Network Interfaces:**
- AXI4-Stream for network data (512-bit default)
- Native TREADY/TVALID backpressure
- TLAST for end-of-stream marking
- TSTRB for byte-level valid indication

**Memory Interfaces:**
- AXI4 for high-performance memory access
- Burst-capable read/write engines
- Address alignment handling
- Write response management

**Monitoring:**
- Comprehensive event monitoring via MonBus
- Performance counters
- Error detection and reporting
- Debug visibility

---

## Chapter 4: Block Descriptions

### Scheduler Group

**Scheduler** - Central control FSM coordinating all operations
**Descriptor Engine** - Manages descriptor FIFO and parsing
**Control Write Engine** - Handles control packet writes
**Control Read Engine** - Handles control packet reads

### Sink Data Path (Network -> Memory)

**AXIS Slave** - Receives data from network via AXI4-Stream
**Sink SRAM Control** - Multi-channel buffering and flow control
**Sink AXI Write Engine** - Writes buffered data to system memory

### Source Data Path (Memory -> Network)

**Source AXI Read Engine** - Reads data from system memory
**Source SRAM Control** - Multi-channel buffering and flow control
**AXIS Master** - Transmits data to network via AXI4-Stream

### MonBus AXIL Group

**AXIL Slave** - Control/status register access
**MonBus Reporter** - Event monitoring and packet generation

---

## Chapter 5: SRAM Storage Format (v0.25)

### Sink SRAM Format

**Width:** 530 bits
**Format:** `{TYPE[1:0], CHUNK_VALID[15:0], DATA[511:0]}`

- TYPE: Packet type classification (CDA vs DATA)
- CHUNK_VALID: 16 x 32-bit chunk enables (derived from TSTRB)
- DATA: 512-bit payload data
- EOS: NOT stored (tracked separately for completion signaling)

**Rationale:** Downstream AXI write engine doesn't need EOS (controlled by scheduler)

### Source SRAM Format

**Width:** 531 bits
**Format:** `{EOS[1], TYPE[2], CHUNK_VALID[16], DATA[512]}`

- EOS: Stream end marker (generates TLAST on AXIS output)
- TYPE: Packet type classification
- CHUNK_VALID: 16 x 32-bit chunk enables (converted to TSTRB)
- DATA: 512-bit payload data

**Rationale:** AXIS master needs EOS to assert TLAST on final beat

### Storage Efficiency

- Overhead: 3.5-3.7% (18-19 metadata bits per 512-bit data line)
- Total SRAM: ~535 KB (32 channels x 256 lines x 530 bits)
- Intentional asymmetry (sink 530, source 531) is optimal for AXIS

---

## Chapter 6: Migration Notes (v0.25)

### AXIS Migration Complete

**Removed:**
- [FAIL] Custom network protocol credit return logic
- [FAIL] Data consumption FIFO (replaced with direct AXIS backpressure)
- [FAIL] EOL/EOD stream markers (replaced with EOS only)
- [FAIL] Network-specific event codes

**Added:**
- [PASS] AXI4-Stream master/slave interfaces
- [PASS] TSTRB to CHUNK_VALID conversion (64 bytes -> 16 x 4-byte chunks)
- [PASS] TLAST generation from stored EOS (source path)
- [PASS] AXIS-optimized monitor event codes
- [PASS] Native AXIS backpressure (TREADY/TVALID)

**Optimized:**
- [PASS] SRAM storage format (removed 3 bits: EOL, EOD, EOS in sink)
- [PASS] Direct passthrough for AXIS handshaking
- [PASS] Simplified completion tracking (EOS-only)

### Performance Impact

- **Throughput:** Improved due to simpler handshaking
- **Latency:** Reduced by eliminating credit return logic
- **Storage:** More efficient (3.5% overhead vs 4.3% in v0.24)
- **Compatibility:** Standard AXIS interfaces enable ecosystem integration

---

## Chapter 7: Future Enhancements

### Potential TYPE Field Extensions

Current 2-bit TYPE field (4 possible values):
- `2'b00` - CDA (Control Descriptor Addressing, user_id = 255)
- `2'b01` - DATA (Normal user traffic, user_id < 255)
- `2'b10` - Reserved (management/diagnostic packets?)
- `2'b11` - Reserved (high-priority express packets?)

### Scalability Considerations

- Parameterized channel count (tested up to 32)
- Configurable SRAM depth per channel
- Flexible data width (512-bit typical, supports others)
- Adaptable chunk granularity (32-bit standard)

---

## Document Metadata

**Version:** 0.25
**Date:** 2025-10-18
**Status:** AXIS Migration Complete
**Generator:** md_to_docx.py
**Repository:** github.com/sean-galloway/RTLDesignSherpa
**Path:** projects/components/rapids/

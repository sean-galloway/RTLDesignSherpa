# Chapter 1: Overview - Introduction

## Purpose

The Converters component provides essential data width conversion and protocol conversion modules that enable seamless integration between components with different data widths or communication protocols.

## Problem Statement

Modern SoC designs frequently encounter two integration challenges:

1. **Data Width Mismatch**
   - CPU: 64-bit data bus
   - DDR Controller: 512-bit data bus
   - PCIe Endpoint: 128-bit data bus
   - Result: Direct connection impossible

2. **Protocol Incompatibility**
   - AXI4 masters (CPU, DMA)
   - APB peripherals (UART, GPIO, SPI)
   - Custom register interfaces (PeakRDL)
   - Result: Protocol bridge required

## Solution Approach

### Data Width Converters

**Generic Building Blocks:**
- `axi_data_upsize` - Accumulates narrow beats into wide beats
- `axi_data_dnsize` - Splits wide beats into narrow beats

**Full AXI4 Integration:**
- `axi4_dwidth_converter_wr` - Write path converter (AW + W + B)
- `axi4_dwidth_converter_rd` - Read path converter (AR + R)

### Protocol Converters

**AXI4 ↔ AXI4-Lite:**
- `axi4_to_axil4_rd` - AXI4→AXIL4 read converter (burst decomposition)
- `axi4_to_axil4_wr` - AXI4→AXIL4 write converter (burst decomposition)
- `axi4_to_axil4` - Full bidirectional converter
- `axil4_to_axi4_rd` - AXIL4→AXI4 read converter (protocol upgrade)
- `axil4_to_axi4_wr` - AXIL4→AXI4 write converter (protocol upgrade)
- `axil4_to_axi4` - Full bidirectional converter

**Other Protocol Converters:**
- `axi4_to_apb_convert` - Full AXI4-to-APB bridge
- `peakrdl_to_cmdrsp` - Register interface adapter

## Key Benefits

### Reusability
- Generic modules work with any width ratio
- Configurable parameters for custom use cases
- Self-contained building blocks

### Performance
- Upsize: 100% throughput (single buffer)
- Downsize: 80% (single buffer) or 100% (dual buffer)
- Minimal latency overhead

### Flexibility
- Configurable sideband handling
- Optional burst tracking
- Dual-buffer mode for high-performance paths

## Component Scope

### In Scope
- Integer width ratios (2:1, 4:1, 8:1, 16:1, etc.)
- AXI4 and APB protocol support
- Configurable throughput vs area trade-offs
- Generic building blocks for custom converters

### Out of Scope
- Non-integer width ratios (e.g., 3:2 conversion)
- AXI4-Stream protocol (different component)
- Complex buffering beyond dual-buffer
- Clock domain crossing (use separate CDC modules)

## Target Applications

1. **CPU-to-DDR Integration** - 64-bit CPU to 512-bit memory controller
2. **DMA Engines** - Variable width data movers
3. **Mixed Protocol Systems** - AXI4 to APB peripheral buses
4. **FPGA Fabric Interfaces** - Width matching for IP integration
5. **Register Access** - PeakRDL to custom control protocols

## Document Organization

This specification is organized into four chapters:

1. **Overview** (This chapter) - Purpose, scope, and architecture
2. **Data Width Converters** - Generic and full AXI4 modules
3. **Protocol Converters** - AXI4-to-APB and PeakRDL adapters
4. **Usage Examples** - Configuration, scenarios, and integration

---

**Next:** [02_architecture.md](02_architecture.md) - System architecture and module hierarchy

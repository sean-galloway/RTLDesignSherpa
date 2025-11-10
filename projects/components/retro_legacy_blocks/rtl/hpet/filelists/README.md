# HPET Component File Lists

## Overview

This directory contains hierarchical file lists for the HPET (High Precision Event Timer) component, following the RAPIDS subsystem methodology. File lists enable clean dependency management and make simulation/synthesis setup more maintainable.

## Directory Structure

```
filelists/
├── component/           # Individual component blocks
│   ├── hpet_regs.f     # PeakRDL-generated register block
│   ├── hpet_core.f     # HPET timer core logic
│   └── hpet_config_regs.f  # Register wrapper (hwif → core)
│
└── integration/         # Top-level integration
    └── apb_hpet.f      # Complete APB-interfaced HPET
```

## Usage

### With Verilator

```bash
# Set repository root
export REPO_ROOT=/path/to/rtldesignsherpa

# Compile complete APB HPET
verilator -cc \
  -f $REPO_ROOT/rtl/amba/components/hpet/filelists/integration/apb_hpet.f \
  --top-module apb_hpet \
  -GNUM_TIMERS=8 \
  -GVENDOR_ID=0x8086 \
  -GREVISION_ID=0x01
```

### With pytest/cocotb-test

```python
import os

# Get repository root
repo_root = os.environ.get('REPO_ROOT', os.path.abspath('../../../'))

# Use file list for clean source specification
run(
    verilog_sources=[
        '-f',
        os.path.join(repo_root, 'rtl/amba/components/hpet/filelists/integration/apb_hpet.f')
    ],
    toplevel='apb_hpet',
    parameters={
        'NUM_TIMERS': 2,
        'VENDOR_ID': 0x8086,
        'REVISION_ID': 0x01
    },
    # ... other run() parameters
)
```

### Manual File List Expansion

```bash
# View all files in dependency order
export REPO_ROOT=/path/to/rtldesignsherpa
verilator -E -f rtl/amba/components/hpet/filelists/integration/apb_hpet.f
```

## File List Hierarchy

### Component Level

#### `component/hpet_regs.f`
- **Purpose:** PeakRDL-generated register block
- **Contents:**
  - `hpet_regs_pkg.sv` - Package with hwif types
  - `hpet_regs.sv` - Register block implementation
- **Dependencies:** None (leaf node)
- **Generated:** Via PeakRDL from `peakrdl/hpet_regs.rdl`

#### `component/hpet_core.f`
- **Purpose:** HPET timer core logic
- **Contents:**
  - `counter_bin.sv` - Binary counter (rtl/common/)
  - `hpet_core.sv` - Timer array and interrupt logic
- **Dependencies:** Common modules only
- **Parameterized:** NUM_TIMERS (2, 3, 8 supported)

#### `component/hpet_config_regs.f`
- **Purpose:** Register wrapper connecting hwif ↔ core
- **Contents:**
  - Includes `hpet_regs.f` (PeakRDL block)
  - `hpet_config_regs.sv` - Wrapper logic
- **Dependencies:** hpet_regs.f
- **Role:** Adapts PeakRDL hwif signals to HPET core interface

### Integration Level

#### `integration/apb_hpet.f`
- **Purpose:** Complete APB-interfaced HPET timer
- **Contents:**
  - Includes `component/hpet_core.f`
  - Includes `component/hpet_config_regs.f`
  - APB slave infrastructure (apb_slave.sv, apb_slave_cdc.sv)
  - PeakRDL adapter (peakrdl_to_cmdrsp.sv)
  - FIFOs and handshaking (gaxi_fifo_sync, cdc_handshake)
  - `apb_hpet.sv` - Top-level module
- **Dependencies:** All component file lists + APB infrastructure
- **Instantiates:** All HPET components with APB interface

## Dependency Graph

```
apb_hpet.f (integration)
├── hpet_core.f (component)
│   ├── counter_bin.sv (common)
│   └── hpet_core.sv
├── hpet_config_regs.f (component)
│   ├── hpet_regs.f (component)
│   │   ├── hpet_regs_pkg.sv (PeakRDL)
│   │   └── hpet_regs.sv (PeakRDL)
│   └── hpet_config_regs.sv (wrapper)
├── APB infrastructure
│   ├── apb_slave.sv
│   ├── apb_slave_cdc.sv
│   ├── peakrdl_to_cmdrsp.sv
│   └── CDC/FIFO utilities
└── apb_hpet.sv (top-level)
```

## HPET Architecture

The HPET component consists of three main layers:

### 1. Register Layer (PeakRDL-Generated)
- **Files:** `hpet_regs_pkg.sv`, `hpet_regs.sv`
- **Role:** APB/command-response register interface
- **Generated:** From `peakrdl/hpet_regs.rdl`
- **Parameterized:** NUM_TIMERS=8 (maximum, synthesis optimizes unused)

### 2. Wrapper Layer
- **File:** `hpet_config_regs.sv`
- **Role:** Adapts PeakRDL hwif signals to HPET core interface
- **Key Functions:**
  - Counter write detection (edge-based)
  - Interrupt status mapping (hwset → W1C)
  - Timer configuration distribution
  - Width adaptation (8-bit hwif → NUM_TIMERS-bit core)

### 3. Core Layer
- **File:** `hpet_core.sv`
- **Role:** Timer array, counter, interrupt generation
- **Key Functions:**
  - Main counter (64-bit, free-running or writable)
  - Per-timer comparators (one-shot and periodic modes)
  - Interrupt status generation
  - 32-bit/64-bit timer modes

## Parameterization

### Single Parameterized RTL
The HPET uses a **single parameterized design** that supports multiple configurations:

```systemverilog
module apb_hpet #(
    parameter NUM_TIMERS = 8,        // 2, 3, or 8 timers
    parameter VENDOR_ID = 16'h0001,  // Customizable vendor ID
    parameter REVISION_ID = 16'h0001 // Customizable revision
) (
    // ... ports ...
);
```

### Test Configurations

| Configuration | NUM_TIMERS | VENDOR_ID | REVISION_ID | Description |
|---------------|------------|-----------|-------------|-------------|
| Intel-like | 2 | 0x8086 | 0x01 | 2-timer Intel HPET |
| AMD-like | 3 | 0x1022 | 0x02 | 3-timer AMD HPET |
| Custom | 8 | 0xABCD | 0x10 | 8-timer extended HPET |

### Why Single Parameterized Design?

**✅ Advantages:**
1. **Single source of truth** - One set of files to maintain
2. **No duplication** - Bug fixes apply to all configurations
3. **Flexible instantiation** - Choose timer count at synthesis time
4. **Standard practice** - Verilog parameters are idiomatic
5. **Synthesis optimization** - Unused timers automatically removed

**Implementation Details:**
- PeakRDL block generated with `NUM_TIMERS=8` (maximum)
- Wrapper adapts 8-bit hwif signals to `NUM_TIMERS`-bit core
- Generate loops only instantiate needed timers
- Synthesis tools optimize away unused timer logic

## PeakRDL Integration

### Register Generation

```bash
cd rtl/amba/components/hpet/peakrdl
peakrdl regblock hpet_regs.rdl -o generated/
cp generated/rtl/hpet_regs.sv/*.sv ../
```

### Generated Files
- `hpet_regs_pkg.sv` - SystemVerilog package with hwif types
- `hpet_regs.sv` - Register block implementation
- `generated/docs/hpet_regs.md` - Register documentation

### Key Features
- **Hardware interface (hwif):** Input/output structs for register access
- **W1C semantics:** Interrupt status uses hwset + W1C
- **Address decode:** Auto-generated from RDL specification
- **Parameterized:** Vendor ID, Revision ID, NUM_TIMERS

## Maintenance

### Adding New Dependencies

When adding new RTL dependencies:

1. **Component-level:** Add to appropriate `component/*.f` file
2. **Integration-level:** Add to `integration/apb_hpet.f`
3. **Update README:** Document new dependencies in this file

### Regenerating PeakRDL

When updating register map:

1. Modify `peakrdl/hpet_regs.rdl`
2. Regenerate: `peakrdl regblock hpet_regs.rdl -o generated/`
3. Copy: `cp generated/rtl/hpet_regs.sv/*.sv ../`
4. **DO NOT** manually edit generated files
5. File lists automatically pick up new files

### Testing File Lists

Verify file lists work correctly:

```bash
export REPO_ROOT=/path/to/rtldesignsherpa

# Test component-level file list
verilator --lint-only \
  -f $REPO_ROOT/rtl/amba/components/hpet/filelists/component/hpet_core.f \
  --top-module hpet_core

# Test integration-level file list
verilator --lint-only \
  -f $REPO_ROOT/rtl/amba/components/hpet/filelists/integration/apb_hpet.f \
  --top-module apb_hpet \
  -GNUM_TIMERS=8
```

## Related Documentation

- **PeakRDL Specification:** `../peakrdl/hpet_regs.rdl`
- **Integration Status:** `../PEAKRDL_INTEGRATION_COMPLETE.md`
- **Test Examples:** `val/integ_amba/test_apb_hpet.py`
- **RAPIDS File Lists:** `rtl/rapids/filelists/` (reference methodology)

---

**Version:** 1.0
**Last Updated:** 2025-10-16
**Maintained By:** RTL Design Sherpa Project

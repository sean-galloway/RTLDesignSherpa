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

# WaveDrom Protocol Presets Reference

**Complete guide to all protocol-specific constraint libraries**

---

## Overview

Protocol presets provide pre-configured temporal constraints for standard bus protocols. Each preset includes field configurations, constraint patterns, and boundary detection tuned for the specific protocol.

### Available Protocols

| Protocol | File | Template Class | Status |
|----------|------|----------------|--------|
| **GAXI** | `gaxi.py` | `GAXIWaveDromTemplate` | ✅ Production |
| **APB** | `apb.py` | `APBWaveDromTemplate` | ✅ Production |
| **AXI4** | `axi4.py` | *(manual setup)* | ✅ Ready |
| **AXI4-Lite** | `axil4.py` | *(manual setup)* | ✅ Ready |
| **AXI-Stream** | `axis.py` | *(manual setup)* | ✅ Ready |

*Location: `bin/CocoTBFramework/tbclasses/wavedrom_user/`*

---

## GAXI (Generic AXI) Protocol

**Simple valid/ready handshake - basis for all other protocols**

### Presets

#### `basic_handshake`
**Constraints:** 1
- `handshake`: Detects valid→ready sequences

**Use Case:** Quick verification that transactions occur

```python
from CocoTBFramework.tbclasses.wavedrom_user.gaxi import GAXIWaveDromTemplate

gaxi_wave = GAXIWaveDromTemplate(
    dut=dut,
    signal_prefix="wr_",
    data_width=32,
    preset="basic_handshake"
)
```

#### `comprehensive`
**Constraints:** 4
- `handshake`: Valid→ready sequences
- `back2back`: Continuous transfers (no idle)
- `stall`: Backpressure (valid=1, ready=0)
- `idle`: Both signals low

**Use Case:** Full protocol behavior analysis

```python
preset="comprehensive"  # Most common choice
```

#### `performance`
**Constraints:** 3
- `handshake`: Valid→ready sequences
- `back2back`: Continuous transfers
- `stall`: Extended window (100 cycles)

**Use Case:** Throughput optimization, identifying bottlenecks

```python
preset="performance"
```

#### `debug`
**Constraints:** 3 (all with extended windows)
- `handshake`: 100 cycle window
- `stall`: 200 cycle window
- `idle`: 50 cycle window

**Use Case:** Debugging stuck or misbehaving interfaces

```python
preset="debug"
```

### Field Configuration

```python
from CocoTBFramework.tbclasses.wavedrom_user.gaxi import get_gaxi_field_config

# Simple data-only
config = get_gaxi_field_config(data_width=32)

# With address
config = get_gaxi_field_config(data_width=32, addr_width=16)

# Multi-field (like APB)
config = get_gaxi_field_config(
    data_width=32,
    addr_width=16,
    ctrl_width=4,
    num_data_fields=2  # Creates data0, data1
)
```

---

## APB (AMBA Peripheral Bus) Protocol

**Register access protocol with setup and access phases**

### Presets

#### `basic_rw`
**Constraints:** 2
- `apb_write_sequence`: PSEL→PWRITE=1→PENABLE→PREADY
- `apb_read_sequence`: PSEL→PWRITE=0→PENABLE→PREADY

**Use Case:** Basic read/write verification

```python
from CocoTBFramework.tbclasses.wavedrom_user.apb import APBWaveDromTemplate

apb_wave = APBWaveDromTemplate(
    dut=dut,
    signal_prefix="apb_",
    data_width=32,
    addr_width=32,
    preset="basic_rw"
)
```

#### `comprehensive`
**Constraints:** 8
- Write/read sequences
- Setup/access phases
- Write/read completion
- Complete transactions
- Error responses

**Use Case:** Full APB protocol analysis

```python
preset="comprehensive"
```

#### `debug`
**Constraints:** 5
- PSEL activity detection
- PREADY activity detection
- PENABLE activity detection
- Write data changes
- Read data capture

**Use Case:** Signal activity troubleshooting

```python
preset="debug"
```

#### `timing`
**Constraints:** 6
- Write/read transactions
- Setup/access phases
- Wait state sequences
- Complete transactions

**Use Case:** Timing analysis and wait state behavior

```python
preset="timing"
```

#### `error`
**Constraints:** 4
- Write/read transactions (optional)
- Error transaction (PSLVERR)
- Wait state sequences

**Use Case:** Error handling verification

```python
preset="error"
```

### Field Configuration

APB uses utility function:

```python
from CocoTBFramework.components.wavedrom.utility import get_apb_field_config

config = get_apb_field_config(
    data_width=32,
    addr_width=32,
    strb_width=4,
    use_signal_names=True  # Use signal names vs descriptions
)
```

---

## AXI4 (Full) Protocol

**5-channel protocol with bursts and out-of-order support**

### Presets

#### `write_basic`
**Constraints:** 3 (AW + W + B channels)
- `aw_handshake`: Write address channel
- `w_handshake`: Write data channel (with WLAST)
- `b_handshake`: Write response channel

**Use Case:** Write transaction verification

```python
from CocoTBFramework.tbclasses.wavedrom_user.axi4 import setup_axi4_constraints_with_boundaries

setup_axi4_constraints_with_boundaries(
    wave_solver=wave_solver,
    preset_name="write_basic",
    signal_prefix="m_axi_",
    id_width=4,
    data_width=64
)
```

#### `read_basic`
**Constraints:** 2 (AR + R channels)
- `ar_handshake`: Read address channel
- `r_handshake`: Read data channel (with RLAST)

**Use Case:** Read transaction verification

```python
preset_name="read_basic"
```

#### `comprehensive`
**Constraints:** 5 (all channels)
- All write_basic constraints
- All read_basic constraints

**Use Case:** Full AXI4 protocol analysis

```python
preset_name="comprehensive"
```

#### `debug`
**Constraints:** 5 (all with 100 cycle windows)
- Extended windows for all channels

**Use Case:** Debugging hung transactions

```python
preset_name="debug"
```

### Field Configuration

Uses AXI4 field config helper:

```python
from CocoTBFramework.components.axi4.axi4_field_configs import get_axi4_field_configs

field_configs = get_axi4_field_configs(
    id_width=8,
    addr_width=32,
    data_width=64,
    user_width=0,  # 0 to disable user signals
    channels=['AW', 'W', 'B', 'AR', 'R']
)

aw_config = field_configs['AW']
w_config = field_configs['W']
# etc.
```

### Manual Setup (No Template Class Yet)

```python
from CocoTBFramework.components.wavedrom.constraint_solver import TemporalConstraintSolver
from CocoTBFramework.tbclasses.wavedrom_user.axi4 import setup_axi4_constraints_with_boundaries

wave_solver = TemporalConstraintSolver(dut=dut, log=dut._log)
wave_solver.add_clock_group('default', dut.axi_aclk)

# Auto-bind each channel
wave_solver.auto_bind_signals('axi4_aw', signal_prefix='m_axi_', field_config=aw_config)
wave_solver.auto_bind_signals('axi4_w', signal_prefix='m_axi_', field_config=w_config)
# etc.

# Setup constraints
setup_axi4_constraints_with_boundaries(
    wave_solver=wave_solver,
    preset_name="comprehensive",
    signal_prefix="m_axi_",
    id_width=4,
    data_width=64
)
```

---

## AXI4-Lite Protocol

**Simplified AXI4 (no bursts, single outstanding transaction)**

### Presets

Same as AXI4: `write_basic`, `read_basic`, `comprehensive`, `debug`

**Key Differences from AXI4:**
- No ID signals
- No burst support (LEN, SIZE, BURST removed)
- No LOCK, CACHE, QOS, REGION
- Only PROT remains
- Simpler field configuration

### Field Configuration

```python
from CocoTBFramework.tbclasses.wavedrom_user.axil4 import get_axil4_channel_field_config

aw_config = get_axil4_channel_field_config('AW', addr_width=32, data_width=32)
w_config = get_axil4_channel_field_config('W', addr_width=32, data_width=32)
b_config = get_axil4_channel_field_config('B', addr_width=32, data_width=32)
ar_config = get_axil4_channel_field_config('AR', addr_width=32, data_width=32)
r_config = get_axil4_channel_field_config('R', addr_width=32, data_width=32)
```

### Setup Function

```python
from CocoTBFramework.tbclasses.wavedrom_user.axil4 import setup_axil4_constraints_with_boundaries

setup_axil4_constraints_with_boundaries(
    wave_solver=wave_solver,
    preset_name="comprehensive",
    signal_prefix="m_axil_",
    addr_width=32,
    data_width=32
)
```

---

## AXI-Stream (AXIS) Protocol

**Data streaming with optional packet boundaries (TLAST)**

### Presets

#### `basic_handshake`
**Constraints:** 1
- `handshake`: TVALID→TREADY sequences

**Use Case:** Verify stream is flowing

```python
from CocoTBFramework.tbclasses.wavedrom_user.axis import setup_axis_constraints_with_boundaries

setup_axis_constraints_with_boundaries(
    wave_solver=wave_solver,
    preset_name="basic_handshake",
    signal_prefix="axis_",
    data_width=64,
    include_tlast=True
)
```

#### `comprehensive`
**Constraints:** 5
- `handshake`: TVALID→TREADY
- `packet`: TVALID=1, TREADY=1, TLAST=1
- `back2back`: Continuous transfers
- `stall`: Backpressure
- `idle`: Both low

**Use Case:** Full stream behavior analysis

```python
preset_name="comprehensive"
```

#### `performance`
**Constraints:** 3
- `handshake`: TVALID→TREADY
- `back2back`: Continuous transfers
- `stall`: Extended window (100 cycles)

**Use Case:** Throughput optimization

```python
preset_name="performance"
```

#### `debug`
**Constraints:** 3 (all extended windows)
- `handshake`: 100 cycles
- `stall`: 200 cycles
- `idle`: 50 cycles

**Use Case:** Debugging stuck streams

```python
preset_name="debug"
```

### Field Configuration

```python
from CocoTBFramework.tbclasses.wavedrom_user.axis import get_axis_field_config

# Simple stream
config = get_axis_field_config(
    data_width=64,
    include_tlast=True,
    include_tkeep=True
)

# Full stream with routing
config = get_axis_field_config(
    data_width=128,
    id_width=4,      # TID for stream routing
    dest_width=4,    # TDEST for destination
    user_width=8,    # TUSER sideband
    include_tkeep=True,
    include_tlast=True
)
```

---

## Comparison Table

| Feature | GAXI | APB | AXI4 | AXIL4 | AXIS |
|---------|------|-----|------|-------|------|
| **Channels** | 1 | 1 | 5 | 5 | 1 |
| **Handshake** | valid/ready | psel/penable/pready | valid/ready per channel | valid/ready per channel | tvalid/tready |
| **Addressing** | Optional | Yes | Yes | Yes | No (stream) |
| **Bursts** | No | No | Yes | No | Implicit |
| **Out-of-Order** | No | No | Yes (ID-based) | No | Optional (TID) |
| **Packet Boundary** | No | No | WLAST/RLAST | No | TLAST |
| **Complexity** | ⭐ Simple | ⭐⭐ Moderate | ⭐⭐⭐⭐⭐ Complex | ⭐⭐⭐ Moderate | ⭐⭐ Simple |
| **Template Class** | ✅ Yes | ✅ Yes | ❌ No | ❌ No | ❌ No |

---

## Creating Custom Presets

### Example: Custom GAXI Preset

```python
from CocoTBFramework.tbclasses.wavedrom_user.gaxi import (
    create_gaxi_handshake_constraint,
    create_gaxi_stall_constraint
)

# Create custom constraints
my_constraints = {
    'fast_handshake': create_gaxi_handshake_constraint(
        signal_prefix="cmd_",
        max_window=10,  # Expect fast response
        field_config=field_config
    ),
    'long_stall': create_gaxi_stall_constraint(
        signal_prefix="cmd_",
        max_window=500,  # Detect long stalls
        field_config=field_config
    )
}

# Add to solver
for name, constraint in my_constraints.items():
    wave_solver.add_constraint(constraint)
```

---

## Next Steps

- **Try it out**: [Quick Start Guide](wavedrom_quick_start.md)
- **Full example**: Wavedrom GAXI Example *(see TestTutorial)*
- **Troubleshooting**: Wavedrom Troubleshooting *(documentation planned)*
- **Auto-binding**: [Auto-Binding Guide](wavedrom_auto_binding.md)

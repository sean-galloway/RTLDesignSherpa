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

# Signal Naming Integration Guide

## Overview

The `signal_naming.py` module provides centralized, industry-standard signal naming for bridge generators.

**Industry Standard Naming Convention:**
- Master AXI4: `<port>_m_axi_<channel><signal>` (e.g., `cpu_m_axi_awid`)
- Slave AXI4: `<port>_s_axi_<channel><signal>` (e.g., `ddr_s_axi_rdata`)
- APB: `<port>_<signal>` (e.g., `apb0_psel`)

## Module API

### Core Functions

```python
from bridge_pkg.signal_naming import SignalNaming, Direction, AXI4Channel, Protocol

# AXI4 signal name generation
signal = SignalNaming.axi4_signal_name(
    port_name="cpu",           # Port name (e.g., "cpu", "ddr_controller")
    direction=Direction.MASTER,  # Direction.MASTER or Direction.SLAVE
    channel=AXI4Channel.AW,      # Channel: AW, W, B, AR, R
    signal="id"                  # Signal within channel: "id", "addr", "valid", etc.
)
# Returns: "cpu_m_axi_awid"

# APB signal name generation
signal = SignalNaming.apb_signal_name(
    port_name="apb0",    # Port name
    signal="psel"        # APB signal: "psel", "paddr", "pready", etc.
)
# Returns: "apb0_psel"

# Get all signals for AXI4 channels
signals = SignalNaming.get_all_axi4_signals(
    port_name="cpu",
    direction=Direction.MASTER,
    channels=[AXI4Channel.AW, AXI4Channel.W, AXI4Channel.B]  # For write-only
)
# Returns: {
#   AXI4Channel.AW: ['cpu_m_axi_awid', 'cpu_m_axi_awaddr', 'cpu_m_axi_awlen', ...],
#   AXI4Channel.W: ['cpu_m_axi_wdata', 'cpu_m_axi_wstrb', 'cpu_m_axi_wlast', ...],
#   AXI4Channel.B: ['cpu_m_axi_bid', 'cpu_m_axi_bresp', 'cpu_m_axi_bvalid', ...]
# }

# Convert channel type string to enum list
channels = SignalNaming.channels_from_type("wr")  # "rw", "wr", or "rd"
# Returns: [AXI4Channel.AW, AXI4Channel.W, AXI4Channel.B]
```

### Enums

```python
class Protocol(Enum):
    AXI4 = "axi4"
    APB = "apb"

class Direction(Enum):
    MASTER = "master"
    SLAVE = "slave"

class AXI4Channel(Enum):
    AW = "aw"  # Write Address
    W = "w"    # Write Data
    B = "b"    # Write Response
    AR = "ar"  # Read Address
    R = "r"    # Read Data
```

## Integration Examples

### Example 1: Generate AXI4 Master Ports

**Before (hardcoded strings):**
```python
def _generate_master_ports(self, master: MasterConfig) -> List[str]:
    lines = []
    prefix = master.prefix  # e.g., "cpu_m_axi_"

    lines.append(f"    input  logic [{id_width-1}:0]   {prefix}awid,")
    lines.append(f"    input  logic [{addr_width-1}:0]  {prefix}awaddr,")
    lines.append(f"    input  logic [7:0]   {prefix}awlen,")
    # ... more signals
    return lines
```

**After (using SignalNaming):**
```python
from bridge_pkg.signal_naming import SignalNaming, Direction, AXI4Channel

def _generate_master_ports(self, master: MasterConfig) -> List[str]:
    lines = []
    port_name = master.name  # e.g., "cpu"

    # Generate AW channel signals
    awid_sig = SignalNaming.axi4_signal_name(port_name, Direction.MASTER, AXI4Channel.AW, "id")
    awaddr_sig = SignalNaming.axi4_signal_name(port_name, Direction.MASTER, AXI4Channel.AW, "addr")
    awlen_sig = SignalNaming.axi4_signal_name(port_name, Direction.MASTER, AXI4Channel.AW, "len")

    lines.append(f"    input  logic [{id_width-1}:0]   {awid_sig},")
    lines.append(f"    input  logic [{addr_width-1}:0]  {awaddr_sig},")
    lines.append(f"    input  logic [7:0]   {awlen_sig},")
    # ... more signals
    return lines
```

### Example 2: Generate All Signals for a Channel

**Before (manual list):**
```python
def _generate_aw_channel(self, prefix: str) -> List[str]:
    lines = []
    lines.append(f"    input  logic [{id_width-1}:0]   {prefix}awid,")
    lines.append(f"    input  logic [{addr_width-1}:0]  {prefix}awaddr,")
    lines.append(f"    input  logic [7:0]   {prefix}awlen,")
    lines.append(f"    input  logic [2:0]   {prefix}awsize,")
    # ... 10+ more signals (easy to miss one!)
    return lines
```

**After (using get_all_axi4_signals):**
```python
def _generate_aw_channel(self, port_name: str, direction: Direction) -> List[str]:
    lines = []

    # Get all AW channel signals automatically
    all_signals = SignalNaming.get_all_axi4_signals(
        port_name=port_name,
        direction=direction,
        channels=[AXI4Channel.AW]
    )

    aw_signals = all_signals[AXI4Channel.AW]

    # Map signal names to widths
    signal_widths = {
        "id": id_width, "addr": addr_width, "len": 8, "size": 3,
        "burst": 2, "lock": 1, "cache": 4, "prot": 3,
        "qos": 4, "region": 4, "user": 1, "valid": 1, "ready": 1
    }

    for sig_name in aw_signals:
        # Extract signal type from full name (e.g., "cpu_m_axi_awid" → "id")
        sig_type = sig_name.split('_')[-1][2:]  # Remove "aw" prefix
        width = signal_widths.get(sig_type, 1)

        if width > 1:
            lines.append(f"    input  logic [{width-1}:0]   {sig_name},")
        else:
            lines.append(f"    input  logic         {sig_name},")

    return lines
```

### Example 3: Generate APB Signals

**Before (hardcoded APB signals):**
```python
def _generate_apb_ports(self, slave: SlaveInfo) -> List[str]:
    lines = []
    prefix = slave.name  # e.g., "apb0"

    lines.append(f"    output logic         {prefix}_psel,")
    lines.append(f"    output logic [31:0]  {prefix}_paddr,")
    lines.append(f"    output logic         {prefix}_penable,")
    # ... more signals
    return lines
```

**After (using SignalNaming):**
```python
def _generate_apb_ports(self, slave: SlaveInfo) -> List[str]:
    lines = []
    port_name = slave.name

    # Get all APB signal names automatically
    apb_signals = SignalNaming.get_all_apb_signals(port_name)

    # APB signal widths (known from spec)
    signal_widths = {
        "psel": 1, "paddr": 32, "penable": 1, "pwrite": 1, "pwdata": 32,
        "pstrb": 4, "pprot": 3, "prdata": 32, "pready": 1, "pslverr": 1
    }

    for sig_name in apb_signals:
        # Extract signal type from full name (e.g., "apb0_psel" → "psel")
        sig_type = sig_name.split('_')[-1]
        width = signal_widths[sig_type]

        if width > 1:
            lines.append(f"    output logic [{width-1}:0]  {sig_name},")
        else:
            lines.append(f"    output logic         {sig_name},")

    return lines
```

### Example 4: Channel-Specific Masters

**Before (manual channel checking):**
```python
def _generate_channels(self, master: MasterConfig) -> List[str]:
    lines = []
    prefix = master.prefix

    if master.channels in ["wr", "rw"]:
        lines.append(f"    input  logic  {prefix}awvalid,")
        lines.append(f"    output logic  {prefix}awready,")
        lines.append(f"    input  logic  {prefix}wvalid,")
        lines.append(f"    output logic  {prefix}wready,")
        lines.append(f"    output logic  {prefix}bvalid,")
        lines.append(f"    input  logic  {prefix}bready,")

    if master.channels in ["rd", "rw"]:
        lines.append(f"    input  logic  {prefix}arvalid,")
        lines.append(f"    output logic  {prefix}arready,")
        lines.append(f"    output logic  {prefix}rvalid,")
        lines.append(f"    input  logic  {prefix}rready,")

    return lines
```

**After (using channels_from_type):**
```python
def _generate_channels(self, master: MasterConfig) -> List[str]:
    lines = []
    port_name = master.name

    # Get channels for this master type
    channels = SignalNaming.channels_from_type(master.channels)

    # Get all signals for these channels
    all_signals = SignalNaming.get_all_axi4_signals(
        port_name=port_name,
        direction=Direction.MASTER,
        channels=channels
    )

    # Generate signal declarations
    for channel, signals in all_signals.items():
        for sig_name in signals:
            # Determine direction and width based on signal type
            # (implementation details omitted for brevity)
            lines.append(f"    input/output logic  {sig_name},")

    return lines
```

## Migration Strategy

### Phase 1: Add SignalNaming Import
```python
# At top of generator file
from bridge_pkg.signal_naming import SignalNaming, Direction, AXI4Channel, Protocol
```

### Phase 2: Replace Hardcoded Slave Prefixes
```python
# BEFORE:
prefix = f"{slave.name}_s_axi_"
signal = f"{prefix}awid"

# AFTER:
signal = SignalNaming.axi4_signal_name(slave.name, Direction.SLAVE, AXI4Channel.AW, "id")
```

### Phase 3: Replace Master Prefix Usage
```python
# BEFORE:
prefix = master.prefix  # Relies on config
signal = f"{prefix}awid"

# AFTER:
signal = SignalNaming.axi4_signal_name(master.name, Direction.MASTER, AXI4Channel.AW, "id")
```

### Phase 4: Use Bulk Signal Generation
```python
# For entire channel signal lists, use get_all_axi4_signals() or get_all_apb_signals()
```

## Benefits

1. **Single Source of Truth**: All signal naming logic in one module
2. **Protocol-Aware**: Handles AXI4, APB, and future protocols
3. **Consistent**: Same naming convention everywhere
4. **Easy to Customize**: Change naming convention in one place
5. **Type-Safe**: Uses enums instead of strings
6. **Self-Documenting**: Function names clearly indicate intent
7. **Prevents Typos**: No manual string concatenation errors

## Testing

### Test the signal_naming module directly:
```bash
cd projects/components/bridge/bin/bridge_pkg
python3 signal_naming.py
```

Example output shows complete signal declarations:
```
=== AXI4 Signal Information Database ===

AW Channel Signals (Master):
  output  logic [3:0]  cpu_m_axi_awid
  output  logic [31:0]  cpu_m_axi_awaddr
  output  logic [7:0]  cpu_m_axi_awlen
  output  logic [2:0]  cpu_m_axi_awsize
  output  logic [1:0]  cpu_m_axi_awburst
  output  logic         cpu_m_axi_awlock
  ... (13 total signals)

R Channel Signals (Slave):
  output  logic [7:0]  ddr_s_axi_rid
  output  logic [63:0]  ddr_s_axi_rdata
  output  logic [1:0]  ddr_s_axi_rresp
  output  logic         ddr_s_axi_rlast
  ... (6 total signals)

APB Signals (Master):
  output  logic         apb0_psel
  output  logic [31:0]  apb0_paddr
  output  logic         apb0_penable
  output  logic         apb0_pwrite
  output  logic [31:0]  apb0_pwdata
  output  logic [3:0]  apb0_pstrb
  ... (10 total signals)
```

### Test integration in bridge generator:
```bash
cd projects/components/bridge/bin
python3 -c "
from bridge_pkg.components.bridge_module_generator import BridgeModuleGenerator
from bridge_pkg.generators.adapter_generator import MasterConfig, SlaveInfo

# Test master port generation
master = MasterConfig('cpu', 'cpu_m_axi_', 64, 32, 4, 'wr', [0])
slave = SlaveInfo('ddr', 0x80000000, 0x80000000, 64, 64)

gen = BridgeModuleGenerator('test_bridge')
gen.add_master(master)
gen.add_slave(slave)

# Generate and display ports
for line in gen._generate_master_ports(master)[:5]:
    print(line)
"
```

This produces properly formatted SystemVerilog port declarations:
```systemverilog
    // Master: cpu (wr)
    output  logic [3:0]  cpu_m_axi_awid,
    output  logic [31:0]  cpu_m_axi_awaddr,
    output  logic [7:0]  cpu_m_axi_awlen,
    output  logic [2:0]  cpu_m_axi_awsize,
```

## Files to Update

### ✅ Completed

1. **bridge_pkg/components/bridge_module_generator.py**
   - ✅ `_generate_master_ports()` - Now uses SignalNaming for complete master signal generation
   - ✅ `_generate_slave_ports()` - Now uses SignalNaming for AXI4 and APB slave signals
   - ⏸️ `_generate_internal_signals()` - Deferred (uses struct-based approach)

### ✅ Phase 2 Complete

2. **bridge_pkg/generators/adapter_generator.py**
   - ✅ `_generate_external_ports()` - Now uses SignalNaming for master ports
   - ⏸️ `_generate_struct_ports()` - Deferred (uses struct-based adapter outputs)

3. **bridge_pkg/generators/crossbar_generator.py**
   - ✅ `_generate_slave_output_ports()` - Now uses SignalNaming for slave outputs
   - ⏸️ `_generate_write_channel_routing()` - Deferred (uses struct field access like `_aw.id`)
   - ⏸️ `_generate_read_channel_routing()` - Deferred (uses struct field access like `_ar.addr`)

**Note:** Internal signal generation currently uses struct-based approach (e.g., `axi4_aw_t`, `axi4_w_64b_t`) which is a valid alternative to individual signal declarations. SignalNaming integration for internal signals can be added later if individual signal approach is preferred.

## Future Enhancements

1. **Add optional underscore between channel and signal**:
   ```python
   # Option to generate: cpu_m_axi_aw_id instead of cpu_m_axi_awid
   SignalNaming.axi4_signal_name(..., separator="_")
   ```

2. **Add port name extraction from prefix**:
   ```python
   # Extract port name from existing prefix
   port_name = SignalNaming.extract_port_name("cpu_m_axi_")  # Returns "cpu"
   ```

3. **Add validation functions**:
   ```python
   # Validate signal name follows convention
   is_valid = SignalNaming.validate_signal_name("cpu_m_axi_awid")
   ```

4. **Add more protocols** (AXI4-Lite, AXI-Stream, etc.):
   ```python
   class Protocol(Enum):
       AXI4 = "axi4"
       AXI4_LITE = "axi4_lite"
       AXIS = "axis"
       APB = "apb"
   ```

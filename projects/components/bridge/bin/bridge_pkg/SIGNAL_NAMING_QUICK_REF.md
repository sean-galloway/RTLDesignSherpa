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

# Signal Naming Quick Reference Card

**Module:** `bridge_pkg.signal_naming`
**Purpose:** Single source of truth for AXI4 and APB signal properties

---

## Quick Import

```python
from bridge_pkg.signal_naming import SignalNaming, Direction, AXI4Channel, Protocol
```

---

## Basic Usage

### 1. Generate a Single Signal Name

```python
# AXI4 Master signal
sig_name = SignalNaming.axi4_signal_name(
    port_name="cpu",
    direction=Direction.MASTER,
    channel=AXI4Channel.AW,
    signal="id"
)
# Returns: "cpu_m_axi_awid"

# AXI4 Slave signal
sig_name = SignalNaming.axi4_signal_name(
    port_name="ddr",
    direction=Direction.SLAVE,
    channel=AXI4Channel.R,
    signal="data"
)
# Returns: "ddr_s_axi_rdata"

# APB signal
sig_name = SignalNaming.apb_signal_name(
    port_name="apb0",
    signal="psel"
)
# Returns: "apb0_psel"
```

---

## Advanced Usage

### 2. Get Complete Signal Information

```python
# Query signal properties
sig_info = SignalNaming.get_axi4_signal_info(
    direction=Direction.MASTER,
    channel=AXI4Channel.AW,
    signal="id"
)

# Access properties
print(sig_info.direction)      # PortDirection.OUTPUT
print(sig_info.width_expr)     # "ID_WIDTH"
print(sig_info.width_param)    # "ID_WIDTH"
print(sig_info.is_vector)      # True
print(sig_info.description)    # "Write transaction ID"
```

### 3. Generate SystemVerilog Declaration

```python
# Define width values
width_values = {
    'ID_WIDTH': 8,
    'ADDR_WIDTH': 32,
    'DATA_WIDTH': 64,
    'STRB_WIDTH': 8,
    'USER_WIDTH': 1
}

# Get signal name
sig_name = SignalNaming.axi4_signal_name("cpu", Direction.MASTER, AXI4Channel.AW, "id")

# Get signal info
sig_info = SignalNaming.get_axi4_signal_info(Direction.MASTER, AXI4Channel.AW, "id")

# Generate complete declaration
declaration = sig_info.get_declaration(sig_name, width_values)
# Returns: "output  logic [7:0]  cpu_m_axi_awid"
```

### 4. Get All Signals for Channels

```python
# Get all write channel signals for a master
channels = [AXI4Channel.AW, AXI4Channel.W, AXI4Channel.B]
all_signals = SignalNaming.get_all_axi4_signals(
    port_name="cpu",
    direction=Direction.MASTER,
    channels=channels
)

# Returns: Dict[AXI4Channel, List[Tuple[str, SignalInfo]]]
# {
#   AXI4Channel.AW: [
#     ("cpu_m_axi_awid", SignalInfo(...)),
#     ("cpu_m_axi_awaddr", SignalInfo(...)),
#     ...
#   ],
#   AXI4Channel.W: [...],
#   AXI4Channel.B: [...]
# }

# Generate declarations for all signals
width_values = {'ID_WIDTH': 8, 'ADDR_WIDTH': 32, ...}
for channel, channel_signals in all_signals.items():
    for sig_name, sig_info in channel_signals:
        declaration = sig_info.get_declaration(sig_name, width_values)
        print(declaration)
```

### 5. Channel-Specific Masters

```python
# Convert channel type string to enum list
wr_channels = SignalNaming.channels_from_type("wr")
# Returns: [AXI4Channel.AW, AXI4Channel.W, AXI4Channel.B]

rd_channels = SignalNaming.channels_from_type("rd")
# Returns: [AXI4Channel.AR, AXI4Channel.R]

rw_channels = SignalNaming.channels_from_type("rw")
# Returns: [AXI4Channel.AW, AXI4Channel.W, AXI4Channel.B,
#           AXI4Channel.AR, AXI4Channel.R]
```

### 6. APB Signals

```python
# Get all APB signals
apb_signals = SignalNaming.get_all_apb_signals(
    port_name="apb0",
    direction=Direction.MASTER
)

# Returns: List[Tuple[str, SignalInfo]]
# [
#   ("apb0_psel", SignalInfo(...)),
#   ("apb0_paddr", SignalInfo(...)),
#   ...
# ]

# Generate declarations
width_values = {'ADDR_WIDTH': 32, 'DATA_WIDTH': 32, 'STRB_WIDTH': 4}
for sig_name, sig_info in apb_signals:
    declaration = sig_info.get_declaration(sig_name, width_values)
    print(declaration)
```

---

## Enums Reference

```python
class Protocol(Enum):
    AXI4 = "axi4"
    APB = "apb"

class Direction(Enum):
    MASTER = "master"  # Bridge acts as slave (receives from master)
    SLAVE = "slave"    # Bridge acts as master (drives to slave)

class PortDirection(Enum):
    INPUT = "input"    # Signal is input to bridge
    OUTPUT = "output"  # Signal is output from bridge

class AXI4Channel(Enum):
    AW = "aw"  # Write Address
    W = "w"    # Write Data
    B = "b"    # Write Response
    AR = "ar"  # Read Address
    R = "r"    # Read Data
```

---

## Industry-Standard Naming Convention

### AXI4 Master (Bridge Slave Port)
```
<port>_m_axi_<channel><signal>
    │     │      │       │
    │     │      │       └─ Signal name (id, addr, valid, etc.)
    │     │      └───────── Channel (aw, w, b, ar, r)
    │     └──────────────── Master indicator
    └────────────────────── Port name

Examples:
  cpu_m_axi_awid      (Master write address ID)
  cpu_m_axi_wdata     (Master write data)
  cpu_m_axi_rvalid    (Master read data valid)
```

### AXI4 Slave (Bridge Master Port)
```
<port>_s_axi_<channel><signal>
    │     │      │       │
    │     │      │       └─ Signal name
    │     │      └───────── Channel
    │     └──────────────── Slave indicator
    └────────────────────── Port name

Examples:
  ddr_s_axi_awready   (Slave write address ready)
  ddr_s_axi_bid       (Slave write response ID)
  ddr_s_axi_rdata     (Slave read data)
```

### APB
```
<port>_<signal>
   │      │
   │      └─ Signal name (psel, paddr, etc.)
   └──────── Port name

Examples:
  apb0_psel           (APB slave select)
  apb0_paddr          (APB address)
  apb0_prdata         (APB read data)
```

---

## Direction Reference

### AXI4 Master (Bridge Slave Port)
```
Master → Bridge
  awvalid   OUTPUT (from master)  → INPUT (to bridge)   [Bridge receives]
  awready   INPUT (to master)     → OUTPUT (from bridge) [Bridge responds]
  wdata     OUTPUT (from master)  → INPUT (to bridge)   [Bridge receives]
  bid       INPUT (to master)     → OUTPUT (from bridge) [Bridge responds]
  rdata     INPUT (to master)     → OUTPUT (from bridge) [Bridge responds]
```

### AXI4 Slave (Bridge Master Port)
```
Bridge → Slave
  awvalid   OUTPUT (from bridge)  → INPUT (to slave)    [Slave receives]
  awready   INPUT (to bridge)     → OUTPUT (from slave)  [Slave responds]
  wdata     OUTPUT (from bridge)  → INPUT (to slave)    [Slave receives]
  bid       INPUT (to bridge)     → OUTPUT (from slave)  [Slave responds]
  rdata     INPUT (to bridge)     → OUTPUT (from slave)  [Slave responds]
```

### APB Master (Bridge to APB Slave)
```
Bridge → APB Slave
  psel      OUTPUT (from bridge)  → INPUT (to slave)
  paddr     OUTPUT (from bridge)  → INPUT (to slave)
  pwdata    OUTPUT (from bridge)  → INPUT (to slave)
  prdata    INPUT (to bridge)     → OUTPUT (from slave)
  pready    INPUT (to bridge)     → OUTPUT (from slave)
```

---

## Complete Example: Bridge Port Generation

```python
from bridge_pkg.signal_naming import SignalNaming, Direction, AXI4Channel

def generate_master_ports(master_name: str, channels_type: str, id_width: int,
                         addr_width: int, data_width: int) -> List[str]:
    """Generate AXI4 master port declarations for bridge."""
    lines = []

    # Width parameters
    width_values = {
        'ID_WIDTH': id_width,
        'ADDR_WIDTH': addr_width,
        'DATA_WIDTH': data_width,
        'STRB_WIDTH': data_width // 8,
        'USER_WIDTH': 1
    }

    # Determine channels
    channels = SignalNaming.channels_from_type(channels_type)

    # Get all signals
    all_signals = SignalNaming.get_all_axi4_signals(
        port_name=master_name,
        direction=Direction.MASTER,
        channels=channels
    )

    # Generate declarations
    for channel, channel_signals in all_signals.items():
        for sig_name, sig_info in channel_signals:
            declaration = sig_info.get_declaration(sig_name, width_values)
            lines.append(f"    {declaration},")

    # Remove trailing comma
    if lines:
        lines[-1] = lines[-1][:-1]

    return lines

# Usage
ports = generate_master_ports("cpu", "wr", 4, 32, 64)
for port in ports:
    print(port)

# Output:
#     output  logic [3:0]  cpu_m_axi_awid,
#     output  logic [31:0]  cpu_m_axi_awaddr,
#     output  logic [7:0]  cpu_m_axi_awlen,
#     ...
```

---

## Common Patterns

### Pattern 1: Port Generation Loop
```python
# For multiple masters
for master in masters:
    channels = SignalNaming.channels_from_type(master.channels)
    all_signals = SignalNaming.get_all_axi4_signals(
        master.name, Direction.MASTER, channels
    )
    # Generate ports...
```

### Pattern 2: Mixed AXI4 and APB
```python
# Check protocol type
if slave.protocol == 'apb':
    apb_signals = SignalNaming.get_all_apb_signals(slave.name, Direction.MASTER)
    # Generate APB ports...
else:
    channels = [AXI4Channel.AW, AXI4Channel.W, AXI4Channel.B,
                AXI4Channel.AR, AXI4Channel.R]
    all_signals = SignalNaming.get_all_axi4_signals(
        slave.name, Direction.SLAVE, channels
    )
    # Generate AXI4 ports...
```

### Pattern 3: Width Adaptation
```python
# Different width values for different ports
master_widths = {'ID_WIDTH': 4, 'DATA_WIDTH': 64, ...}
slave_widths = {'ID_WIDTH': 8, 'DATA_WIDTH': 512, ...}

# Generate with appropriate widths
master_decl = sig_info.get_declaration(master_sig, master_widths)
slave_decl = sig_info.get_declaration(slave_sig, slave_widths)
```

---

## Testing

```bash
# Test module directly
cd projects/components/bridge/bin/bridge_pkg
python3 signal_naming.py

# Test integration
python3 -c "
from bridge_pkg.signal_naming import SignalNaming, Direction, AXI4Channel

# Test single signal
print(SignalNaming.axi4_signal_name('cpu', Direction.MASTER, AXI4Channel.AW, 'id'))

# Test signal info
sig_info = SignalNaming.get_axi4_signal_info(Direction.MASTER, AXI4Channel.AW, 'id')
print(sig_info.get_declaration('cpu_m_axi_awid', {'ID_WIDTH': 8}))

# Test APB
apb_sig = SignalNaming.apb_signal_name('apb0', 'psel')
print(apb_sig)
"
```

---

## See Also

- `SIGNAL_NAMING_INTEGRATION.md` - Detailed integration guide
- `SIGNAL_NAMING_STATUS.md` - Implementation status
- `signal_naming.py` - Source code with full documentation

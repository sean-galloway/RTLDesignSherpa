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

# AXISFieldConfigs

The `AXISFieldConfigs` class provides factory methods for creating field configurations for AXI4-Stream protocol implementations. It offers standardized configurations for different AXIS parameter combinations, ensuring consistency between hardware modules and verification components.

## Class Overview

```python
class AXISFieldConfigs:
    """
    Factory class for creating AXIS field configurations.

    AXI4-Stream protocol uses a single T channel containing:
    - TDATA: Data payload
    - TSTRB: Byte enables (strobe)
    - TLAST: End of packet/frame indicator
    - TID: Stream identifier
    - TDEST: Destination routing
    - TUSER: User-defined sideband data
    - TVALID/TREADY: Handshake signals
    """
```

## Factory Methods

### Core Configuration Method

#### `create_t_field_config(data_width=32, id_width=8, dest_width=4, user_width=1)`

Create comprehensive field configuration for AXIS T channel with all optional fields.

**Parameters:**
- **`data_width`** (int) - Width of TDATA field (8, 16, 32, 64, 128, 256, 512, 1024)
- **`id_width`** (int) - Width of TID field (1-16 bits, 0 to disable)
- **`dest_width`** (int) - Width of TDEST field (1-16 bits, 0 to disable)
- **`user_width`** (int) - Width of TUSER field (1-32 bits, 0 to disable)

**Returns:** `FieldConfig` - Complete field configuration for T channel

**Example:**
```python
# Create full-featured AXIS configuration
config = AXISFieldConfigs.create_t_field_config(
    data_width=64,
    id_width=16,
    dest_width=8,
    user_width=16
)

# Create configuration with minimal sideband signals
config = AXISFieldConfigs.create_t_field_config(
    data_width=32,
    id_width=4,
    dest_width=0,  # No destination routing
    user_width=0   # No user data
)
```

### Predefined Configurations

#### `create_default_axis_config(data_width=32)`

Create default AXIS configuration with typical parameters suitable for most applications.

**Parameters:**
- **`data_width`** (int) - Width of data field

**Returns:** `FieldConfig` - Standard configuration (8-bit ID, 4-bit DEST, 1-bit USER)

**Example:**
```python
# Create standard 32-bit AXIS configuration
config = AXISFieldConfigs.create_default_axis_config(data_width=32)
# Results in: data=32b, id=8b, dest=4b, user=1b, strb=4b

# Create standard 64-bit AXIS configuration
config = AXISFieldConfigs.create_default_axis_config(data_width=64)
# Results in: data=64b, id=8b, dest=4b, user=1b, strb=8b
```

#### `create_simple_axis_config(data_width=32)`

Create simple AXIS configuration with minimal sideband signals for basic streaming.

**Parameters:**
- **`data_width`** (int) - Width of data field

**Returns:** `FieldConfig` - Minimal configuration (no ID, DEST, or USER signals)

**Example:**
```python
# Create simple streaming configuration
config = AXISFieldConfigs.create_simple_axis_config(data_width=32)
# Results in: data=32b, strb=4b, last=1b only

# Create simple wide configuration
config = AXISFieldConfigs.create_simple_axis_config(data_width=512)
# Results in: data=512b, strb=64b, last=1b only
```

#### `create_axis_config_from_hw_params(data_width, id_width, dest_width, user_width)`

Create AXIS configuration matching hardware module parameters exactly.

**Parameters:**
- **`data_width`** (int) - AXIS_DATA_WIDTH hardware parameter
- **`id_width`** (int) - AXIS_ID_WIDTH hardware parameter
- **`dest_width`** (int) - AXIS_DEST_WIDTH hardware parameter
- **`user_width`** (int) - AXIS_USER_WIDTH hardware parameter

**Returns:** `FieldConfig` - Configuration matching hardware exactly

**Example:**
```python
# Match hardware module parameters
config = AXISFieldConfigs.create_axis_config_from_hw_params(
    data_width=128,
    id_width=12,
    dest_width=6,
    user_width=8
)

# Zero-width parameter handling (hardware with TID_WIDTH=0)
config = AXISFieldConfigs.create_axis_config_from_hw_params(
    data_width=32,
    id_width=0,     # No ID signal
    dest_width=0,   # No DEST signal
    user_width=4    # 4-bit USER signal
)
```

## Field Definitions

Each configuration includes the following field definitions:

### Core Fields (Always Present)

#### `data` Field
- **Width**: Configurable (8-1024 bits)
- **Format**: Hexadecimal
- **Default**: 0
- **Description**: Stream data payload

#### `strb` Field
- **Width**: data_width / 8 bits
- **Format**: Binary
- **Default**: All bits set (all bytes enabled)
- **Description**: Byte enables indicating valid data bytes

#### `last` Field
- **Width**: 1 bit
- **Format**: Binary
- **Default**: 0 (not last)
- **Description**: End of packet/frame indicator
- **Encoding**: {0: "Not Last", 1: "Last"}

### Optional Fields (Conditionally Present)

#### `id` Field (if id_width > 0)
- **Width**: Configurable (1-16 bits)
- **Format**: Hexadecimal
- **Default**: 0
- **Description**: Stream identifier for routing

#### `dest` Field (if dest_width > 0)
- **Width**: Configurable (1-16 bits)
- **Format**: Hexadecimal
- **Default**: 0
- **Description**: Destination routing identifier

#### `user` Field (if user_width > 0)
- **Width**: Configurable (1-32 bits)
- **Format**: Binary
- **Default**: 0
- **Description**: User-defined sideband data

## Usage Examples

### Basic Configuration Setup

```python
# Create configuration for different data widths
configs = {}

# 32-bit standard configuration
configs['axis32'] = AXISFieldConfigs.create_default_axis_config(32)

# 64-bit high-performance configuration
configs['axis64'] = AXISFieldConfigs.create_t_field_config(
    data_width=64,
    id_width=16,
    dest_width=8,
    user_width=32
)

# 512-bit simple streaming configuration
configs['axis512'] = AXISFieldConfigs.create_simple_axis_config(512)

# Use with components
master = AXISMaster(dut, "Master", "m_axis_", clk, field_config=configs['axis32'])
```

### Hardware Matching Configuration

```python
# Match SystemVerilog module parameters
# module axis_master #(
#     parameter AXIS_DATA_WIDTH = 128,
#     parameter AXIS_ID_WIDTH = 8,
#     parameter AXIS_DEST_WIDTH = 4,
#     parameter AXIS_USER_WIDTH = 16
# )

hw_config = AXISFieldConfigs.create_axis_config_from_hw_params(
    data_width=128,
    id_width=8,
    dest_width=4,
    user_width=16
)

# Create components with matching configuration
master = AXISMaster(dut, "HW_Master", "m_axis_", clk, field_config=hw_config)
slave = AXISSlave(dut, "HW_Slave", "s_axis_", clk, field_config=hw_config)
```

### Dynamic Configuration Selection

```python
def get_axis_config(stream_type, data_width):
    """Select appropriate AXIS configuration based on requirements."""

    if stream_type == "simple":
        return AXISFieldConfigs.create_simple_axis_config(data_width)

    elif stream_type == "routing":
        return AXISFieldConfigs.create_t_field_config(
            data_width=data_width,
            id_width=8,
            dest_width=8,
            user_width=0
        )

    elif stream_type == "full_featured":
        return AXISFieldConfigs.create_t_field_config(
            data_width=data_width,
            id_width=16,
            dest_width=16,
            user_width=32
        )

    else:
        return AXISFieldConfigs.create_default_axis_config(data_width)

# Use in test scenarios
test_config = get_axis_config("routing", 64)
master = AXISMaster(dut, "RoutingMaster", "m_axis_", clk, field_config=test_config)
```

### Configuration Analysis and Validation

```python
def analyze_axis_config(config):
    """Analyze AXIS field configuration."""
    analysis = {
        'total_fields': len(config.fields),
        'data_width': config.get_field('data').bits,
        'strb_width': config.get_field('strb').bits,
        'has_id': 'id' in config.fields,
        'has_dest': 'dest' in config.fields,
        'has_user': 'user' in config.fields
    }

    # Calculate total bus width
    total_bits = sum(field.bits for field in config.fields.values())
    analysis['total_signal_bits'] = total_bits

    # Add optional field widths
    if analysis['has_id']:
        analysis['id_width'] = config.get_field('id').bits
    if analysis['has_dest']:
        analysis['dest_width'] = config.get_field('dest').bits
    if analysis['has_user']:
        analysis['user_width'] = config.get_field('user').bits

    return analysis

# Analyze different configurations
configs_to_test = [
    AXISFieldConfigs.create_simple_axis_config(32),
    AXISFieldConfigs.create_default_axis_config(32),
    AXISFieldConfigs.create_t_field_config(64, 16, 8, 32)
]

for i, config in enumerate(configs_to_test):
    analysis = analyze_axis_config(config)
    print(f"Config {i}: {analysis}")
```

### Zero-Width Signal Handling

```python
# Handle configurations with zero-width optional signals
def create_flexible_axis_config(data_width, **optional_widths):
    """Create AXIS config with flexible optional signal widths."""

    return AXISFieldConfigs.create_t_field_config(
        data_width=data_width,
        id_width=optional_widths.get('id_width', 0),
        dest_width=optional_widths.get('dest_width', 0),
        user_width=optional_widths.get('user_width', 0)
    )

# Various zero-width combinations
configs = {
    'data_only': create_flexible_axis_config(32),
    'with_id': create_flexible_axis_config(32, id_width=8),
    'with_routing': create_flexible_axis_config(32, id_width=4, dest_width=4),
    'full_custom': create_flexible_axis_config(32, id_width=12, dest_width=6, user_width=8)
}

# Verify field presence
for name, config in configs.items():
    fields = list(config.fields.keys())
    print(f"{name}: {fields}")
```

## Integration with Components

### Component Configuration

```python
# Configure master and slave with matching configurations
config = AXISFieldConfigs.create_default_axis_config(64)

master = AXISMaster(
    dut=dut,
    title="ConfiguredMaster",
    prefix="m_axis_",
    clock=clk,
    field_config=config
)

slave = AXISSlave(
    dut=dut,
    title="ConfiguredSlave",
    prefix="s_axis_",
    clock=clk,
    field_config=config
)

# Configuration ensures field compatibility
```

### Packet Creation with Configuration

```python
# Create packets using configuration
config = AXISFieldConfigs.create_t_field_config(32, 8, 4, 16)

packet = AXISPacket(field_config=config)
packet.data = 0x12345678
packet.strb = 0xF
packet.last = 1
packet.id = 5
packet.dest = 2
packet.user = 0xABCD

# All fields properly sized according to configuration
```

The AXISFieldConfigs class provides a comprehensive and flexible system for creating standardized AXIS field configurations, ensuring compatibility between hardware implementations and verification components while supporting the full range of AXI4-Stream protocol variations.
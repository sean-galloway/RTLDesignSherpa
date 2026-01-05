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

# apbgaxiconfig.py Usage Guide

APB-GAXI Configuration Module providing configurable APB-GAXI interface configurations using the FieldConfig framework. This module supports parameterized field configurations and signal mappings for APB-GAXI bridge interfaces.

## Why Use APB GAXI Config

The `apbgaxiconfig.py` module is essential for APB-GAXI bridge verification because it provides:

- **Parameterized configuration generation** for different bus widths and interface variants
- **FieldConfig integration** that ensures consistent field definitions across components
- **Standardized interface definitions** for APB-GAXI command and response interfaces
- **Configurable bus widths** supporting different design requirements
- **Systematic field management** that reduces configuration errors and inconsistencies

## Core Class

### APBGAXIConfig

**Purpose**: Factory class that creates standard APB-GAXI configurations with customizable parameters like address width, data width, and strobe width.

**When to Use**:
- Creating field configurations for APB-GAXI bridge components
- Setting up testbenches with different bus width requirements
- Ensuring consistent field definitions across command and response interfaces
- Supporting multiple design variants with different width configurations

## Class Architecture

### Configuration Parameters

The APBGAXIConfig class manages three primary parameters:

- **addr_width**: Address bus width in bits (default: 32)
- **data_width**: Data bus width in bits (default: 32) 
- **strb_width**: Strobe width in bits (default: data_width // 8)

### Constructor

```python
APBGAXIConfig(addr_width=32, data_width=32, strb_width=None)
```

**Parameters:**
- `addr_width`: Address bus width in bits (default: 32)
- `data_width`: Data bus width in bits (default: 32)
- `strb_width`: Strobe width in bits (defaults to data_width // 8 if None)

**Basic Creation**:
```python
from CocoTBFramework.tbclasses.apb.apbgaxiconfig import APBGAXIConfig

# Default 32-bit configuration
config = APBGAXIConfig()

# Custom 64-bit data bus configuration
wide_config = APBGAXIConfig(
    addr_width=32,
    data_width=64,
    strb_width=8
)

# Custom address and data widths
custom_config = APBGAXIConfig(
    addr_width=24,
    data_width=32,
    strb_width=4
)
```

## Configuration Generation Methods

### Command Interface Configuration

```python
def create_cmd_field_config() -> FieldConfig
```

**Purpose**: Creates field configuration for APB-GAXI command interface.

**Returns**: FieldConfig object with command interface field definitions

**Usage**:
```python
config = APBGAXIConfig(addr_width=32, data_width=32)

# Generate command interface field configuration
cmd_config = config.create_cmd_field_config()

# Use with GAXI master or command components
gaxi_master = GAXIMaster(
    entity=dut,
    title="APB_GAXI_Master",
    prefix="cmd_",
    clock=dut.clk,
    field_config=cmd_config
)
```

### Response Interface Configuration

```python
def create_rsp_field_config() -> FieldConfig
```

**Purpose**: Creates field configuration for APB-GAXI response interface.

**Returns**: FieldConfig object with response interface field definitions

**Usage**:
```python
config = APBGAXIConfig(addr_width=32, data_width=32)

# Generate response interface field configuration
rsp_config = config.create_rsp_field_config()

# Use with GAXI slave or response components
gaxi_slave = GAXISlave(
    entity=dut,
    title="APB_GAXI_Slave",
    prefix="rsp_",
    clock=dut.clk,
    field_config=rsp_config
)
```

## Field Configuration Details

### Command Interface Fields

The command interface configuration typically includes:

- **Address Field**: Configurable width based on addr_width parameter
- **Write Enable**: Single bit for read/write indication
- **Write Data**: Configurable width based on data_width parameter
- **Write Strobes**: Configurable width based on strb_width parameter
- **Valid/Ready**: Handshaking signals for command interface

### Response Interface Fields

The response interface configuration typically includes:

- **Read Data**: Configurable width based on data_width parameter
- **Error Response**: Error indication fields
- **Valid/Ready**: Handshaking signals for response interface
- **Response Status**: Additional status fields as needed

## Usage Patterns

### Basic Configuration Setup

```python
from CocoTBFramework.tbclasses.apb.apbgaxiconfig import APBGAXIConfig

@cocotb.test()
async def basic_apb_gaxi_test(dut):
    # Create configuration for standard 32-bit interface
    config = APBGAXIConfig(
        addr_width=32,
        data_width=32,
        strb_width=4
    )
    
    # Generate field configurations
    cmd_field_config = config.create_cmd_field_config()
    rsp_field_config = config.create_rsp_field_config()
    
    # Create components with generated configurations
    from CocoTBFramework.components.gaxi import GAXIMaster, GAXISlave
    
    master = GAXIMaster(
        entity=dut,
        title="APB_Master",
        prefix="cmd_",
        clock=dut.clk,
        field_config=cmd_field_config
    )
    
    slave = GAXISlave(
        entity=dut,
        title="APB_Slave", 
        prefix="rsp_",
        clock=dut.clk,
        field_config=rsp_field_config
    )
    
    # Use components for testing
    # ...
```

### Multi-Width Configuration Testing

```python
@cocotb.test()
async def multi_width_config_test(dut):
    # Test different bus width configurations
    
    # 32-bit configuration
    config_32 = APBGAXIConfig(addr_width=32, data_width=32)
    cmd_config_32 = config_32.create_cmd_field_config()
    rsp_config_32 = config_32.create_rsp_field_config()
    
    # 64-bit configuration
    config_64 = APBGAXIConfig(addr_width=32, data_width=64)
    cmd_config_64 = config_64.create_cmd_field_config()
    rsp_config_64 = config_64.create_rsp_field_config()
    
    # 16-bit configuration for smaller interfaces
    config_16 = APBGAXIConfig(addr_width=16, data_width=16)
    cmd_config_16 = config_16.create_cmd_field_config()
    rsp_config_16 = config_16.create_rsp_field_config()
    
    # Create components for each configuration
    # Test compatibility and behavior across different widths
    
    # Verify field widths match expectations
    assert cmd_config_32.get_field_width('addr') == 32
    assert cmd_config_64.get_field_width('data') == 64
    assert cmd_config_16.get_field_width('strb') == 2  # 16/8 = 2
```

### APB-GAXI Bridge Configuration

```python
async def setup_apb_gaxi_bridge(dut, addr_width, data_width):
    """Setup APB-GAXI bridge with specific configuration"""
    
    # Create configuration for bridge
    bridge_config = APBGAXIConfig(
        addr_width=addr_width,
        data_width=data_width,
        strb_width=data_width // 8
    )
    
    # Generate field configurations for both sides
    apb_cmd_config = bridge_config.create_cmd_field_config()
    gaxi_rsp_config = bridge_config.create_rsp_field_config()
    
    # Create APB side components
    apb_master = APBMaster(
        entity=dut,
        title="APB_Bridge_Master",
        prefix="apb_",
        clock=dut.clk,
        bus_width=data_width,
        addr_width=addr_width
    )
    
    # Create GAXI side components with field configurations
    gaxi_master = GAXIMaster(
        entity=dut,
        title="GAXI_Bridge_Master",
        prefix="gaxi_cmd_",
        clock=dut.clk,
        field_config=apb_cmd_config
    )
    
    gaxi_slave = GAXISlave(
        entity=dut,
        title="GAXI_Bridge_Slave",
        prefix="gaxi_rsp_",
        clock=dut.clk,
        field_config=gaxi_rsp_config
    )
    
    return {
        'config': bridge_config,
        'apb_master': apb_master,
        'gaxi_master': gaxi_master,
        'gaxi_slave': gaxi_slave
    }

@cocotb.test()
async def apb_gaxi_bridge_test(dut):
    # Setup bridge for 32-bit operation
    bridge_32 = await setup_apb_gaxi_bridge(dut, 32, 32)
    
    # Setup bridge for 64-bit operation
    bridge_64 = await setup_apb_gaxi_bridge(dut, 32, 64)
    
    # Test both configurations
    # ...
```

### Configuration-Driven Component Creation

```python
def create_apb_gaxi_system(dut, clock, config_params):
    """Create complete APB-GAXI system from configuration parameters"""
    
    # Create configuration from parameters
    config = APBGAXIConfig(**config_params)
    
    # Generate field configurations
    cmd_config = config.create_cmd_field_config()
    rsp_config = config.create_rsp_field_config()
    
    # Create all components with consistent configuration
    components = {
        'config': config,
        'cmd_field_config': cmd_config,
        'rsp_field_config': rsp_config,
        'master': GAXIMaster(dut, "Master", "cmd_", clock, cmd_config),
        'slave': GAXISlave(dut, "Slave", "rsp_", clock, rsp_config),
        'monitor': GAXIMonitor(dut, "Monitor", "mon_", clock, cmd_config)
    }
    
    return components

@cocotb.test()
async def configuration_driven_test(dut):
    # Define different test configurations
    test_configs = [
        {'addr_width': 32, 'data_width': 32, 'strb_width': 4},
        {'addr_width': 32, 'data_width': 64, 'strb_width': 8},
        {'addr_width': 24, 'data_width': 32, 'strb_width': 4},
        {'addr_width': 16, 'data_width': 16, 'strb_width': 2}
    ]
    
    # Test each configuration
    for i, config_params in enumerate(test_configs):
        logger.info(f"Testing configuration {i+1}: {config_params}")
        
        # Create system with current configuration
        system = create_apb_gaxi_system(dut, dut.clk, config_params)
        
        # Run test with this configuration
        await run_system_test(system, f"config_{i+1}")
        
        logger.info(f"Configuration {i+1} test completed")
```

### Field Width Validation

```python
def validate_configuration(config, expected_widths):
    """Validate that configuration produces expected field widths"""
    
    cmd_config = config.create_cmd_field_config()
    rsp_config = config.create_rsp_field_config()
    
    # Validate command interface fields
    for field_name, expected_width in expected_widths['cmd'].items():
        actual_width = cmd_config.get_field_width(field_name)
        assert actual_width == expected_width, \
            f"Command field {field_name}: expected {expected_width}, got {actual_width}"
    
    # Validate response interface fields
    for field_name, expected_width in expected_widths['rsp'].items():
        actual_width = rsp_config.get_field_width(field_name)
        assert actual_width == expected_width, \
            f"Response field {field_name}: expected {expected_width}, got {actual_width}"

@cocotb.test()
async def field_width_validation_test(dut):
    # Test 32-bit configuration
    config_32 = APBGAXIConfig(addr_width=32, data_width=32, strb_width=4)
    
    expected_widths_32 = {
        'cmd': {
            'addr': 32,
            'data': 32,
            'strb': 4,
            'write': 1
        },
        'rsp': {
            'data': 32,
            'error': 1
        }
    }
    
    validate_configuration(config_32, expected_widths_32)
    
    # Test 64-bit configuration
    config_64 = APBGAXIConfig(addr_width=32, data_width=64, strb_width=8)
    
    expected_widths_64 = {
        'cmd': {
            'addr': 32,
            'data': 64,
            'strb': 8,
            'write': 1
        },
        'rsp': {
            'data': 64,
            'error': 1
        }
    }
    
    validate_configuration(config_64, expected_widths_64)
    
    logger.info("All field width validations passed")
```

## Integration with Other Components

### With GAXI Components

```python
# Configurations work seamlessly with GAXI components
config = APBGAXIConfig(addr_width=32, data_width=32)

gaxi_master = GAXIMaster(
    dut, "Master", "cmd_", dut.clk, 
    field_config=config.create_cmd_field_config()
)

gaxi_slave = GAXISlave(
    dut, "Slave", "rsp_", dut.clk,
    field_config=config.create_rsp_field_config()
)
```

### With APB Components

```python
# Configurations support APB component requirements
config = APBGAXIConfig(addr_width=24, data_width=32)

# APB components can use the same width parameters
apb_master = APBMaster(
    dut, "APB_Master", "apb_", dut.clk,
    bus_width=config.data_width,
    addr_width=config.addr_width
)
```

### With Scoreboards

```python
# Field configurations integrate with scoreboards
config = APBGAXIConfig(addr_width=32, data_width=32)
cmd_config = config.create_cmd_field_config()

scoreboard = APBGAXIScoreboard(
    name="Bridge_SB",
    field_config=cmd_config,
    log=logger
)
```

## Best Practices

### 1. **Consistent Configuration Usage**
```python
# Use same configuration for related components
config = APBGAXIConfig(addr_width=32, data_width=64)

# Apply to all related components
cmd_config = config.create_cmd_field_config()
rsp_config = config.create_rsp_field_config()

master = GAXIMaster(dut, "Master", "cmd_", clk, cmd_config)
slave = GAXISlave(dut, "Slave", "rsp_", clk, rsp_config)
```

### 2. **Parameter Validation**
```python
# Validate parameters before use
def create_validated_config(addr_width, data_width, strb_width=None):
    assert addr_width > 0, "Address width must be positive"
    assert data_width > 0, "Data width must be positive"
    assert data_width % 8 == 0, "Data width must be multiple of 8"
    
    if strb_width is None:
        strb_width = data_width // 8
    else:
        assert strb_width == data_width // 8, "Strobe width must match data width"
    
    return APBGAXIConfig(addr_width, data_width, strb_width)
```

### 3. **Configuration Documentation**
```python
# Document configuration choices
def create_system_config(system_type):
    """Create configuration for specific system type"""
    
    if system_type == "high_performance":
        # 64-bit data for high throughput
        return APBGAXIConfig(addr_width=32, data_width=64, strb_width=8)
    elif system_type == "low_power":
        # 16-bit data for reduced power
        return APBGAXIConfig(addr_width=24, data_width=16, strb_width=2)
    elif system_type == "standard":
        # Standard 32-bit configuration
        return APBGAXIConfig(addr_width=32, data_width=32, strb_width=4)
    else:
        raise ValueError(f"Unknown system type: {system_type}")
```

### 4. **Reusable Configuration Patterns**
```python
# Create reusable configuration patterns
class ConfigPatterns:
    @staticmethod
    def embedded_system():
        return APBGAXIConfig(addr_width=24, data_width=32, strb_width=4)
    
    @staticmethod
    def server_system():
        return APBGAXIConfig(addr_width=32, data_width=64, strb_width=8)
    
    @staticmethod
    def iot_device():
        return APBGAXIConfig(addr_width=16, data_width=16, strb_width=2)

# Usage
config = ConfigPatterns.embedded_system()
```

The APB GAXI Config module provides essential configuration management for APB-GAXI bridge verification, ensuring consistent field definitions and supporting multiple design variants through parameterized configuration generation.
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

# APB Testbench Classes Index

This directory contains APB testbench classes for the CocoTBFramework. These classes provide high-level testbench functionality for APB protocol verification including command handling, configuration management, and register map testing.

## Directory Structure

```
CocoTBFramework/tbclasses/apb/
├── apb_command_handler.py
├── apbgaxiconfig.py
└── register_map.py
```

## Overview
- [**Overview**](tbclasses_apb_overview.md) - Complete overview of the APB testbench classes directory

## Core Components

### Command and Control
- [**apb_command_handler.py**](tbclasses_apb_apb_command_handler_guide.md) - APB slave command/response interface handler
- [**apbgaxiconfig.py**](tbclasses_apb_apbgaxiconfig_guide.md) - APB-GAXI configuration factory with field configurations

### Register Management
- [**register_map.py**](tbclasses_apb_register_map_guide.md) - Register information handling and transaction generation

## Quick Start

### Basic Command Handler Setup
```python
from CocoTBFramework.tbclasses.apb.apb_command_handler import APBCommandHandler

# Create command handler for APB slave
handler = APBCommandHandler(
    dut=dut,
    memory_model=memory_model,
    log=logger
)

# Start processing commands
await handler.start()
```

### Configuration Management
```python
from CocoTBFramework.tbclasses.apb.apbgaxiconfig import APBGAXIConfig

# Create configuration with custom widths
config = APBGAXIConfig(addr_width=32, data_width=64)

# Generate field configurations
cmd_config = config.create_cmd_field_config()
rsp_config = config.create_rsp_field_config()
```

### Register Map Testing
```python
from CocoTBFramework.tbclasses.apb.register_map import RegisterMap

# Load register map from file
reg_map = RegisterMap(
    filename="registers.py",
    apb_data_width=32,
    apb_addr_width=24,
    start_address=0x1000000,
    log=logger
)

# Generate test transactions
read_transactions = reg_map.generate_read_transactions()
write_transactions = reg_map.generate_write_even_transactions()
```

## Navigation
- [**Back to tbclasses**](../tbclasses_index.md) - Return to tbclasses index
- [**Back to CocoTBFramework**](../../index.md) - Return to main framework index
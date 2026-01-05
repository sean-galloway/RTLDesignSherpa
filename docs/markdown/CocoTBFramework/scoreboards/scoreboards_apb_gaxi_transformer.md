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

# apb_gaxi_transformer.py

APB to GAXI protocol transformer implementation providing bidirectional conversion between APB and GAXI protocols. This module enables cross-protocol verification through transaction transformation and adapter classes for seamless protocol bridge testing.

## Overview

The APB-GAXI transformer system provides:
- **Bidirectional Transformation**: Complete APB ↔ GAXI protocol conversion
- **Field Mapping**: Configurable mapping between APB and GAXI protocol fields
- **Timing Preservation**: Maintains transaction timing information across transformations
- **Adapter Framework**: High-level adapters for integration with master components
- **Performance Tracking**: Transaction statistics and latency analysis

## Classes

### APBtoGAXITransformer

Core transformer providing bidirectional APB-GAXI protocol conversion.

```python
class APBtoGAXITransformer:
    def __init__(self, gaxi_field_config, gaxi_packet_class=GAXIPacket, log=None)
```

**Parameters:**
- `gaxi_field_config`: GAXI field configuration for packet creation
- `gaxi_packet_class`: GAXI packet class for creating instances (default: GAXIPacket)
- `log`: Logger instance for transformation debugging

**Key Features:**
- Field mapping between APB and GAXI formats
- Direction-aware data handling
- Timing information preservation
- Error handling and logging

## Core Transformation Methods

### APB to GAXI Conversion

#### `apb_to_gaxi(apb_transaction)`
Convert APB transaction to GAXI packet format.

**Parameters:**
- `apb_transaction`: APB transaction to convert

**Returns:**
- `GAXIPacket`: Converted GAXI packet

**Field Mapping:**
- `apb.paddr` → `gaxi.addr`: Address field mapping
- `apb.pwdata/prdata` → `gaxi.data`: Data field (direction-dependent)
- `apb.pstrb` → `gaxi.strb`: Write strobe mapping (write transactions only)
- `apb.direction` → `gaxi.cmd`: Command type (1=write, 0=read)

```python
# APB write transaction transformation
apb_write = APBPacket()
apb_write.direction = 'WRITE'
apb_write.paddr = 0x1000
apb_write.pwdata = 0xDEADBEEF
apb_write.pstrb = 0xF

gaxi_packet = transformer.apb_to_gaxi(apb_write)
# Result: gaxi_packet.addr=0x1000, gaxi_packet.data=0xDEADBEEF, gaxi_packet.cmd=1
```

### GAXI to APB Conversion

#### `gaxi_to_apb(gaxi_packet, apb_transaction_class)`
Convert GAXI packet to APB transaction format.

**Parameters:**
- `gaxi_packet`: GAXI packet to convert
- `apb_transaction_class`: APB transaction class for creating instances

**Returns:**
- `APBTransaction`: Converted APB transaction

**Field Mapping:**
- `gaxi.addr` → `apb.paddr`: Address field mapping
- `gaxi.data` → `apb.pwdata/prdata`: Data field (command-dependent)
- `gaxi.strb` → `apb.pstrb`: Write strobe mapping (if available)
- `gaxi.cmd` → `apb.direction`: Direction field (1=WRITE, 0=READ)

```python
# GAXI packet transformation
gaxi_read = GAXIPacket(field_config)
gaxi_read.addr = 0x2000
gaxi_read.data = 0x12345678
gaxi_read.cmd = 0  # Read

apb_transaction = transformer.gaxi_to_apb(gaxi_read, APBPacket)
# Result: apb_transaction.direction='READ', apb_transaction.paddr=0x2000, apb_transaction.prdata=0x12345678
```

## Adapter Framework

### APBGAXIAdapterBase

Base class providing common functionality for protocol adapters.

```python
class APBGAXIAdapterBase:
    def __init__(self, transformer, field_config=None, log=None)
```

**
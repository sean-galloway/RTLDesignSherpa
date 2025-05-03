# AMBA Fabric Components

This section contains documentation for various AMBA (Advanced Microcontroller Bus Architecture) fabric components designed for system-on-chip (SoC) implementations. These components enable communication between different IP blocks within a complex SoC design.

## [↩ Return to AMBA Index](../index.md)

## Available Components

### APB Crossbars

* [**apb_xbar**](apb_xbar.md) - A full-featured APB crossbar implementation that connects multiple APB masters to multiple APB slaves with:
  * Configurable number of masters (default: 3) and slaves (default: 6)
  * Intermediate command/response buffer architecture 
  * FIFO buffering for commands and responses
  * Weighted round-robin arbitration for both master and slave sides
  * Address-based routing with configurable slave address ranges

* [**apb_xbar_thin**](apb_xbar_thin.md) - A lightweight APB crossbar implementation with:
  * Reduced resource usage compared to full apb_xbar
  * Direct connection between masters and slaves without intermediate buffering
  * Configurable number of masters (default: 2) and slaves (default: 4)
  * Weighted round-robin arbitration
  * Address-based routing with configurable slave address ranges

### Protocol Converters

* [**axi2apb_convert**](axi2apb_convert.md) - A protocol converter that bridges between AXI and APB interfaces:
  * Translates AXI transactions into APB transactions
  * Handles data width adaptation when AXI data width is larger than APB data width
  * Supports AXI burst transactions by breaking them into individual APB transfers
  * Transaction tracking for proper response correlation
  * Preserves AXI transaction ordering semantics

* [**axi2apb_shim**](axi2apb_shim.md) - A complete AXI to APB bridge with clock domain crossing:
  * Built upon axi2apb_convert with added clock domain crossing capabilities
  * Supports independent AXI and APB clock domains
  * Four-phase handshake for robust clock domain crossing
  * Configurable buffer depths for performance tuning
  * Complete AXI slave and APB master interfaces

## Integration Considerations

When designing a system using these components, consider the following:

1. **Clock Domains**: For designs with multiple clock domains, use axi2apb_shim which includes CDC capability.
   
2. **Data Width**: Match the data width parameters to your specific requirements, ensuring AXI_DATA_WIDTH is a multiple of APB_DATA_WIDTH for optimal performance.

3. **Buffer Sizing**: Adjust buffer depths based on expected traffic patterns and performance requirements.

4. **Address Mapping**: Configure slave address ranges properly to ensure correct routing of transactions.

5. **Resource Usage**: Choose between full and thin implementations based on your resource constraints and performance needs.

## [↩ Return to AMBA Index](../index.md)

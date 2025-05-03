# AMBA Utilities

[Return to AMBA Index](../index.md)

This section contains documentation for various AMBA (Advanced Microcontroller Bus Architecture) utility modules that facilitate efficient implementation of AMBA-based designs. These utilities provide essential functionality for clock management, error monitoring, address generation, and data transfer across clock domains.

## Clock Management

* [amba_clock_gate_ctrl](amba_clock_gate_ctrl.md) - Clock gating controller for AMBA interfaces that monitors activity and gates the clock during idle periods to reduce power consumption.

## Address Generation and Management

* [axi_gen_addr](axi_gen_addr.md) - Module for generating the next address for AXI transactions based on current address, transfer size, burst type, and length.

## Error Monitoring

* [axi_errmon_base](axi_errmon_base.md) - Comprehensive error monitoring system for AXI and AXI-Lite interfaces that detects protocol violations and timeout conditions.

## Clock Domain Crossing (CDC)

* [cdc_handshake](cdc_handshake_doc.md) - Specialized synchronization circuit for safely transferring data between different clock domains using request-acknowledge handshaking.

## FIFO and Buffer Components

* [gaxi_fifo_sync](gaxi_fifo_sync_doc.md) - Synchronous FIFO buffer operating in a single clock domain, designed for buffering and flow control in AXI interfaces.
* [gaxi_fifo_async](gaxi_fifo_async_doc.md) - Asynchronous FIFO buffer for safely crossing clock domains in AXI interfaces with Gray code-based pointer synchronization.
* [gaxi_skid_buffer](gaxi_skid_buffer_doc.md) - Specialized FIFO that improves timing closure and throughput in pipelined designs by providing buffering with flow control.
* [gaxi_skid_buffer_async](gaxi_skid_buffer_async.md) - Asynchronous skid buffer combining buffering, flow control, and clock domain crossing capabilities for AXI interfaces.

[Return to AMBA Index](../index.md)

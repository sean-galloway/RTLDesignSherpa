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

## RAPIDS System Overview

The Memory Input/Output Processor (RAPIDS) is a high-performance data streaming engine operating at 2.5 GHz, designed to provide reliable, low-latency data transfer between external DRAM and processing cores through the Network network. The architecture features dual independent data paths with sophisticated multi-channel support for up to 32 concurrent streams, implementing pure pipeline architectures that eliminate traditional FSM overhead to achieve sustained throughput exceeding 1.2 Tbps per path.

![RAPIDS/Network/MSAP](../assets/mermaid/miop_blocks.png)

### Scheduler Group

The Scheduler Group provides complete integrated channel processing through an innovative dual-FSM architecture that combines descriptor execution with parallel address alignment optimization. The main scheduler FSM manages descriptor lifecycle, credit operations, and program sequencing, while the address alignment FSM runs concurrently to pre-calculate optimal transfer parameters including burst lengths and chunk enable patterns. This approach eliminates alignment calculation overhead from critical AXI timing paths, enabling sustained high-performance operation while maintaining comprehensive control over stream boundaries and error handling.

### Descriptor Engine

The Descriptor Engine implements a sophisticated six-state finite state machine that orchestrates descriptor fetching and processing operations with dual-path support for both APB programming interface requests and RDA packet interface operations. The FSM manages the complete descriptor lifecycle from initial request validation through AXI read transactions, descriptor parsing, and final output generation. RDA packets receive priority processing over APB requests, ensuring optimal network responsiveness, while comprehensive stream boundary support includes complete EOS/EOL/EOD field extraction and propagation through a 4-deep descriptor FIFO.

### Program Engine

The Program Engine implements a streamlined four-state finite state machine that manages post-processing write operations for each virtual channel after descriptor completion. The FSM handles program address writes with configurable data values to support notification, control, and cleanup operations with comprehensive timeout mechanisms and robust error handling. Conditional programming through graceful null address handling enables descriptor-driven execution, while shared AXI interface operations use ID-based response routing for proper multi-channel coordination and runtime reconfiguration support.

### Source Data Path Group

The Source Data Path implements a complete data transmission pipeline from scheduler requests through Network packet delivery, featuring a revolutionary pure pipeline architecture with zero-FSM overhead for optimal performance. The path integrates a sophisticated AXI read engine with multi-channel arbitration, preallocation-based deadlock prevention, and chunk-aware burst optimization to achieve maximum memory bandwidth utilization. Integrated SRAM control provides multi-channel buffering with stream-aware flow control, while the Network master implements a four-stage pipeline with credit-based flow control and mathematically proven zero packet loss guarantees.

### Sink Data Path Group

The Sink Data Path provides comprehensive data reception and processing from Network packet arrival through final AXI memory writes, implementing sophisticated buffer management and multi-channel arbitration for optimal throughput. The Network slave features bulletproof ACK generation with dual FIFO queues, comprehensive validation, and intelligent packet routing based on packet classification. Sink SRAM control manages multi-channel buffering with sophisticated flow control and EOS completion signaling, while the AXI write engine implements pure pipeline architecture with zero-cycle arbitration, transfer strategy optimization, and chunk-aware write strobes for precise memory utilization.

### Monitor Bus AXI4-Lite Group

The Monitor Bus AXI4-Lite Group provides unified system monitoring and event aggregation across all RAPIDS subsystems, implementing a comprehensive filtering and routing architecture for optimal system visibility. The group aggregates monitor streams from source and sink data paths through round-robin arbitration, applying configurable protocol-specific filtering for AXI, Network, and CORE events. The architecture supports both interrupt generation through error/interrupt FIFOs for critical events and external logging through configurable master write operations, providing complete event coverage across 544 defined event codes spanning all protocols and packet types for comprehensive system debugging and performance analysis.
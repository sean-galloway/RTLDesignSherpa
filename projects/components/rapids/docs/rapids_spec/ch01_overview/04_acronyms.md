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

# Chapter 1.4: Acronyms and Abbreviations

## A

**APB** - Advanced Peripheral Bus (AMBA 3 specification for low-bandwidth control interfaces)

**AR** - Address Read (AXI4 read address channel)

**AMBA** - Advanced Microcontroller Bus Architecture (ARM interconnect standard)

**AW** - Address Write (AXI4 write address channel)

**AXI4** - Advanced eXtensible Interface version 4 (high-performance memory-mapped protocol)

**AXI4-Lite (AXIL)** - Subset of AXI4 for simple control/status register access

**AXIS** - AXI4-Stream (packet-oriented streaming protocol)

**ASIC** - Application-Specific Integrated Circuit

## B

**BFM** - Bus Functional Model (testbench component)

**B Channel** - AXI4 write response channel

## C

**CDA** - Compute Direct Access (packet type for descriptor injection from HIVE-C to RAPIDS)

**CDC** - Clock Domain Crossing (asynchronous interface between different clock domains)

**Comparator** - Timer comparison value in HPET peripheral

## D

**DDR** - Double Data Rate (SDRAM memory technology: DDR2, DDR3, DDR4)

**DDR2/DDR3/DDR4** - Generations of DDR memory (DDR2: 400-800 MT/s, DDR3: 800-1600 MT/s, DDR4: 1600-3200 MT/s)

**Delta Network** - 4×4 mesh Network-on-Chip for compute fabric interconnection

**Descriptor** - Data structure containing DMA transfer parameters (source, destination, length, control)

**DMA** - Direct Memory Access (hardware-managed memory transfers without CPU intervention)

**DRAM** - Dynamic Random Access Memory

**DUT** - Device Under Test (module being verified in testbench)

## F

**FIFO** - First In First Out (queue buffer structure)

**FPGA** - Field-Programmable Gate Array

**FSM** - Finite State Machine (sequential logic with discrete states)

## H

**HIVE-C** - High-performance Integrated VexRiscv Engine for Control (RISC-V master controller)

**HPET** - High Precision Event Timer (multi-timer peripheral)

## I

**ID** - Transaction identifier (AXI4 signal for out-of-order response routing)

**INCR** - Incrementing burst type (AXI4 burst mode)

## M

**Mesh** - Network topology with regular grid structure (4×4 for Delta Network)

**MM2S** - Memory-to-Stream (read from DDR memory, transmit to Delta Network)

**MonBus** - Monitor Bus (standardized 64-bit monitoring protocol)

## N

**Network Slave** - RAPIDS interface receiving packets from Delta Network

**Network Master** - RAPIDS interface transmitting packets to Delta Network

**NoC** - Network-on-Chip (on-chip interconnect fabric)

## P

**Packet** - Unit of data transmission on AXIS/Delta Network interfaces

**PKT_CONFIG** - Packet type for configuration (TUSER = 2'b10)

**PKT_DATA** - Packet type for compute data (TUSER = 2'b00)

**PKT_STATUS** - Packet type for monitoring/status (TUSER = 2'b11)

**Priority** - Descriptor scheduling weight (0=highest, 15=lowest in RAPIDS)

## R

**R Channel** - AXI4 read data channel

**RAPIDS** - Rapid AXI Programmable In-band Descriptor System (DMA engine)

**RISC-V** - Open-standard instruction set architecture (used in HIVE-C)

**Router** - Delta Network component for packet routing between tiles

## S

**S2MM** - Stream-to-Memory (receive from Delta Network, write to DDR memory)

**Scatter-Gather** - DMA technique using linked descriptor chains for non-contiguous transfers

**SERV** - System Event Reporting and Verification (monitoring subsystem)

**SRAM** - Static Random Access Memory (on-chip buffer)

## T

**TDEST** - Transaction Destination (AXIS signal indicating target tile/destination)

**TID** - Transaction ID (AXIS signal for source identification or priority)

**Tile** - Compute element in Delta Network mesh (physical: 0-15, virtual: 16-17)

**TLAST** - Transaction Last (AXIS signal indicating final beat of packet)

**TREADY** - Transaction Ready (AXIS backpressure signal)

**TUSER** - Transaction User (AXIS signal encoding packet type)

**TVALID** - Transaction Valid (AXIS signal indicating valid data)

## V

**VexRiscv** - RISC-V softcore CPU implementation (used in HIVE-C)

**Virtual Tile** - Non-physical network endpoint (RAPIDS=16, HIVE-C=17)

**VC** - Virtual Channel (independent flow control paths in router)

## W

**W Channel** - AXI4 write data channel

**W1C** - Write-1-to-Clear (register bit cleared by writing 1, not 0)

**WRAP** - Wrapping burst type (AXI4 burst mode for circular addressing)

---

## System-Specific Terms

**Compute Tile** - Processing element in Delta Network (tiles 0-15)

**Descriptor Chain** - Linked list of descriptors for scatter-gather DMA

**Descriptor FIFO** - Queue storing pending DMA descriptors (minimum 8 entries)

**Inband Descriptor** - Descriptor injected via CDA packets (no memory polling)

**Virtual Tile 16** - RAPIDS DMA engine network address

**Virtual Tile 17** - HIVE-C control processor network address

**XY Routing** - Dimension-ordered routing (X-dimension first, then Y-dimension)

---

## Packet Type Summary

| Acronym | TUSER | Full Name | Source | Destination | Purpose |
|---------|-------|-----------|--------|-------------|---------|
| **PKT_DATA** | 2'b00 | Data Packet | RAPIDS/Tiles | RAPIDS/Tiles | Compute data transfers |
| **CDA** | 2'b01 | Compute Direct Access | HIVE-C | RAPIDS | Descriptor injection |
| **PKT_CONFIG** | 2'b10 | Configuration Packet | HIVE-C/SERV | Routers/Tiles | Configuration |
| **PKT_STATUS** | 2'b11 | Status Packet | SERV | HIVE-C | Monitoring/status |

---

**Next:** [References](05_references.md)

**Previous:** [Clocks and Reset](03_clocks_and_reset.md)

**Back to:** [Index](../rapids_index.md)

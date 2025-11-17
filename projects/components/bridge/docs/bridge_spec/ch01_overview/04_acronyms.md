# 1.4 Acronyms and Abbreviations

This section provides definitions for acronyms and abbreviations used throughout the Bridge documentation.

## A

**AHB**  
Advanced High-performance Bus - AMBA bus protocol for high-performance systems

**APB**  
Advanced Peripheral Bus - AMBA bus protocol for low-power peripheral interfaces

**AMBA**  
Advanced Microcontroller Bus Architecture - ARM's on-chip communication standard

**ARADDR**  
AXI Read Address - Address field in AXI read address channel

**ARBURST**  
AXI Read Burst Type - Burst type indicator for read transactions

**ARCACHE**  
AXI Read Cache - Cache attributes for read transactions

**ARID**  
AXI Read ID - Transaction identifier for read address channel

**ARLEN**  
AXI Read Length - Number of data transfers in read burst

**ARLOCK**  
AXI Read Lock - Lock type for atomic read operations

**ARPROT**  
AXI Read Protection - Protection attributes for read transactions

**ARQOS**  
AXI Read Quality of Service - QoS identifier for read transactions

**ARREADY**  
AXI Read Address Ready - Slave indicates readiness to accept read address

**ARSIZE**  
AXI Read Size - Size of each transfer in read burst

**ARVALID**  
AXI Read Address Valid - Master indicates valid read address/control

**AWADDR**  
AXI Write Address - Address field in AXI write address channel

**AWBURST**  
AXI Write Burst Type - Burst type indicator for write transactions

**AWCACHE**  
AXI Write Cache - Cache attributes for write transactions

**AWID**  
AXI Write ID - Transaction identifier for write address channel

**AWLEN**  
AXI Write Length - Number of data transfers in write burst

**AWLOCK**  
AXI Write Lock - Lock type for atomic write operations

**AWPROT**  
AXI Write Protection - Protection attributes for write transactions

**AWQOS**  
AXI Write Quality of Service - QoS identifier for write transactions

**AWREADY**  
AXI Write Address Ready - Slave indicates readiness to accept write address

**AWSIZE**  
AXI Write Size - Size of each transfer in write burst

**AWVALID**  
AXI Write Address Valid - Master indicates valid write address/control

**AXI**  
Advanced eXtensible Interface - High-performance protocol in AMBA family

**AXI4**  
Advanced eXtensible Interface version 4 - Latest full AXI specification

**AXI4-Lite**  
Simplified subset of AXI4 for control/status registers

**AXI4-Stream**  
AXI4 variant optimized for streaming data flows

## B

**BID**  
AXI Write Response ID - Transaction identifier for write response channel

**BREADY**  
AXI Write Response Ready - Master indicates readiness to accept write response

**BRESP**  
AXI Write Response - Response status for write transaction

**BVALID**  
AXI Write Response Valid - Slave indicates valid write response

## C

**CAM**  
Content Addressable Memory - Associative memory used for ID tracking

**CDC**  
Clock Domain Crossing - Circuitry for signals crossing clock boundaries

**CLOG2**  
Ceiling Log Base 2 - Function to calculate minimum bit width

**CSV**  
Comma-Separated Values - Configuration file format option

## D

**DMA**  
Direct Memory Access - Hardware subsystem for autonomous data transfers

**DRC**  
Design Rule Check - Automated verification of design constraints

**DUT**  
Device Under Test - Component being verified in testbench

## E

**ECC**  
Error Correction Code - Algorithm for detecting/correcting bit errors

## F

**FIFO**  
First-In-First-Out - Queue data structure for buffering

**FSM**  
Finite State Machine - Sequential logic controller

## G

**GUI**  
Graphical User Interface - Visual tool for configuration management

## H

**HPET**  
High Precision Event Timer - Reference specification for documentation format

## I

**ID**  
Identifier - Unique tag for tracking transactions

**ILA**  
Integrated Logic Analyzer - FPGA debugging tool

**IP**  
Intellectual Property - Reusable design component

## J

**JSON**  
JavaScript Object Notation - Data interchange format

## L

**LFSR**  
Linear Feedback Shift Register - Pseudo-random sequence generator

**LSB**  
Least Significant Bit - Rightmost bit in binary representation

**LUT**  
Look-Up Table - FPGA logic element

## M

**MAS**  
Micro-Architecture Specification - Detailed design documentation format

**MSB**  
Most Significant Bit - Leftmost bit in binary representation

**MUX**  
Multiplexer - Circuit selecting one of multiple inputs

## N

**NOP**  
No Operation - Idle state or null transaction

## O

**OOO**  
Out-Of-Order - Transactions completing in different order than issued

**OOR**  
Out-Of-Range - Address outside valid address space

## P

**PDF**  
Portable Document Format - Document file format for distribution

**PRDATA**  
APB Read Data - Data field in APB read transaction

**PRD**  
Product Requirements Document - High-level specification document

**PREADY**  
APB Ready - Slave indicates completion of transfer

**PSEL**  
APB Select - Slave selection signal

**PSLVERR**  
APB Slave Error - Error response signal

**PWDATA**  
APB Write Data - Data field in APB write transaction

## Q

**QoS**  
Quality of Service - Priority or performance level indicator

## R

**RDATA**  
AXI Read Data - Data field in AXI read data channel

**RID**  
AXI Read Response ID - Transaction identifier for read data channel

**RLAST**  
AXI Read Last - Indicates final transfer in read burst

**RREADY**  
AXI Read Data Ready - Master indicates readiness to accept read data

**RRESP**  
AXI Read Response - Response status for read data transfer

**RTL**  
Register Transfer Level - Hardware description abstraction level

**RVALID**  
AXI Read Data Valid - Slave indicates valid read data

## S

**SDC**  
Synopsys Design Constraints - Timing constraint file format

**SoC**  
System-on-Chip - Integrated circuit containing complete system

**STA**  
Static Timing Analysis - Method for verifying timing requirements

**SV**  
SystemVerilog - Hardware description and verification language

## T

**TCAM**  
Ternary Content Addressable Memory - CAM with don't-care states

**TOML**  
Tom's Obvious Minimal Language - Configuration file format

## U

**UVM**  
Universal Verification Methodology - SystemVerilog verification framework

## V

**VCD**  
Value Change Dump - Waveform file format

**VIP**  
Verification IP - Reusable verification component

## W

**WDATA**  
AXI Write Data - Data field in AXI write data channel

**WLAST**  
AXI Write Last - Indicates final transfer in write burst

**WREADY**  
AXI Write Data Ready - Slave indicates readiness to accept write data

**WSTRB**  
AXI Write Strobe - Byte-lane write enable signals

**WVALID**  
AXI Write Data Valid - Master indicates valid write data

## X

**XBAR**  
Crossbar - Interconnect allowing any master to access any slave

**XDC**  
Xilinx Design Constraints - Xilinx timing constraint file format

---

## Bridge-Specific Terms

**Bridge ID (BID_WIDTH)**  
Internal identifier added to transactions for routing responses back to originating master

**Channel-Specific Master**  
Master port specialized for read-only, write-only, or read-write operations

**Master Adapter**  
Per-master module providing timing isolation and protocol conversion

**Round-Robin Arbitration**  
Fair scheduling algorithm cycling through requesters

**Skid Buffer**  
Pipeline register allowing single-cycle backpressure response

**Slave Router**  
Module decoding addresses and routing requests to slaves

**Width Conversion**  
Logic adapting between different data bus widths

---

**Note**: Signal names from the AXI4 specification (AR*, AW*, W*, B*, R*) are shown in uppercase as they typically appear in RTL. However, when used in SystemVerilog code they may appear in lowercase or with prefixes/suffixes depending on naming conventions.

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

# CDC Handshake

**Module:** `cdc_handshake.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The CDC Handshake module provides robust clock domain crossing (CDC) with valid/ready flow control protocol. It implements a dual FSM architecture with 3-stage synchronizers to safely transfer data between asynchronous clock domains while maintaining AXI-style handshaking semantics.

### Key Features

- Safe asynchronous clock domain crossing with metastability protection
- AXI-compatible valid/ready handshake protocol
- 3-stage synchronizer chains for REQ/ACK signals
- Dual FSM architecture (source and destination domains)
- Parameterizable data width
- Independent reset for each clock domain
- Proven REQ/ACK protocol for glitch-free operation

---

## Module Purpose

Modern SoC designs frequently require data transfer between asynchronous clock domains. Direct signal crossing risks metastability, data corruption, and protocol violations. The CDC Handshake module solves these challenges by:

1. **Metastability Protection:** Multi-stage synchronizers for control signals
2. **Data Integrity:** Stable data capture with proper handshaking
3. **Flow Control:** Backpressure support via ready signals
4. **Protocol Correctness:** AXI-compatible valid/ready semantics

**Use Cases:**
- AXI interface clock domain crossing (monitor packets, control signals)
- Data transfer between processor cores and peripherals
- Multi-clock SoC interconnect boundaries
- Configuration register updates across clock domains

**Key Guarantee:** Data transferred without corruption or loss, with proper flow control.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| DATA_WIDTH | int | 8 | Width of the data bus (1 to 1024+ bits typical) |

**Typical Values:**
- Control signals: 8-32 bits
- AXI monitor packets: 64 bits
- Configuration registers: 32-64 bits
- Custom data structures: Application-specific

---

## Port Groups

### Source Clock Domain Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| clk_src | input | 1 | Source domain clock (can be asynchronous to clk_dst) |
| rst_src_n | input | 1 | Source domain active-low asynchronous reset |
| src_valid | input | 1 | Source indicates data valid (AXI-style valid) |
| src_ready | output | 1 | Handshake ready back to source (asserted when transfer complete) |
| src_data | input | DATA_WIDTH | Data from source domain (captured when valid asserted) |

### Destination Clock Domain Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| clk_dst | input | 1 | Destination domain clock (can be asynchronous to clk_src) |
| rst_dst_n | input | 1 | Destination domain active-low asynchronous reset |
| dst_valid | output | 1 | Destination indicates data valid to receiver (AXI-style valid) |
| dst_ready | input | 1 | Receiver ready in destination domain (AXI-style ready) |
| dst_data | output | DATA_WIDTH | Data transferred to destination domain (stable when valid) |

---

## Functional Description

### CDC Protocol Overview

The module implements a four-phase handshake protocol:

1. **Request Phase:** Source asserts REQ, latches data
2. **Synchronization Phase:** REQ crosses to destination domain (3 stages)
3. **Acknowledge Phase:** Destination asserts ACK after accepting data
4. **Synchronization Phase:** ACK crosses back to source domain (3 stages)
5. **Completion Phase:** Both sides deassert signals, ready for next transfer

**Critical Property:** Data stable throughout handshake (captured at REQ assertion, held until ACK completion).

### Source Domain FSM

**State Diagram:**
```
S_IDLE → S_WAIT_ACK → S_WAIT_ACK_CLR → S_IDLE
```

**State Descriptions:**

**S_IDLE:**
- Awaits src_valid assertion
- src_ready = 1 (ready for new data)
- r_req_src = 0 (request inactive)

**S_WAIT_ACK:**
- Transfer in progress
- src_ready = 0 (busy)
- r_req_src = 1 (request asserted)
- Data latched in r_async_data
- Awaits synchronized ACK from destination

**S_WAIT_ACK_CLR:**
- ACK received, completing handshake
- src_ready = 0 (still busy)
- r_req_src = 0 (request deasserted)
- Awaits ACK to clear (return to 0)

**State Transitions:**

```systemverilog
S_IDLE:
    if (src_valid):
        r_async_data <= src_data       // Capture data
        r_req_src <= 1                 // Assert request
        src_ready <= 0
        → S_WAIT_ACK

S_WAIT_ACK:
    if (w_ack_sync):                   // ACK received
        r_req_src <= 0                 // Deassert request
        → S_WAIT_ACK_CLR
    else:
        remain in S_WAIT_ACK

S_WAIT_ACK_CLR:
    if (!w_ack_sync):                  // ACK cleared
        src_ready <= 1                 // Ready for next transfer
        → S_IDLE
    else:
        remain in S_WAIT_ACK_CLR
```

### Destination Domain FSM

**State Diagram:**
```
D_IDLE → D_WAIT_READY → D_WAIT_REQ_CLR → D_IDLE
```

**State Descriptions:**

**D_IDLE:**
- Awaits synchronized REQ from source
- dst_valid = 0 (no data available)
- r_ack_dst = 0 (acknowledge inactive)

**D_WAIT_READY:**
- REQ detected, data available
- dst_valid = 1 (presenting data to receiver)
- r_ack_dst = 0 (waiting for receiver acceptance)
- Awaits dst_ready assertion

**D_WAIT_REQ_CLR:**
- Data accepted, handshake completing
- dst_valid = 0 (transfer complete)
- r_ack_dst = 1 (acknowledge asserted)
- Awaits REQ to clear (return to 0)

**State Transitions:**

```systemverilog
D_IDLE:
    if (w_req_sync):                   // REQ received
        r_dst_data <= r_async_data     // Latch data
        dst_valid <= 1                 // Present to receiver
        → D_WAIT_READY

D_WAIT_READY:
    if (dst_ready):                    // Receiver accepts data
        r_ack_dst <= 1                 // Assert acknowledge
        dst_valid <= 0                 // Clear valid
        → D_WAIT_REQ_CLR
    else if (!w_req_sync):             // REQ withdrawn (error case)
        dst_valid <= 0
        → D_IDLE

D_WAIT_REQ_CLR:
    if (!w_req_sync):                  // REQ cleared
        r_ack_dst <= 0                 // Deassert acknowledge
        → D_IDLE
    else:
        remain in D_WAIT_REQ_CLR
```

### Synchronizer Architecture

**3-Stage Synchronizers for Metastability Protection:**

**REQ Synchronizer (Source → Destination):**
```systemverilog
always_ff @(posedge clk_dst or negedge rst_dst_n) begin
    if (!rst_dst_n)
        r_req_sync <= 3'b000;
    else
        r_req_sync <= {r_req_sync[1:0], r_req_src};
end

assign w_req_sync = r_req_sync[2];  // Use final stage
```

**ACK Synchronizer (Destination → Source):**
```systemverilog
always_ff @(posedge clk_src or negedge rst_src_n) begin
    if (!rst_src_n)
        r_ack_sync <= 3'b000;
    else
        r_ack_sync <= {r_ack_sync[1:0], r_ack_dst};
end

assign w_ack_sync = r_ack_sync[2];  // Use final stage
```

**Why 3 Stages?**
- Stage 1: May go metastable (timing violation from async input)
- Stage 2: Metastability resolves (high probability)
- Stage 3: Clean synchronized signal (used by FSM)

**MTBF Calculation:**
```
MTBF = e^(Tr/τ) / (f_clk × f_data × τ)

Where:
- Tr: Resolution time (2 clock periods for 2-stage sync)
- τ: Metastability time constant (technology-dependent, ~100ps)
- f_clk: Destination clock frequency
- f_data: Data change frequency

3-stage sync provides astronomical MTBF (years to millennia)
```

### Data Stability Guarantee

**Critical Timing:**

1. **Data Capture (Source Domain):**
   - Data captured when src_valid asserted in S_IDLE
   - Stored in r_async_data register
   - Held stable until handshake completes

2. **Data Transfer (Asynchronous):**
   - r_async_data crosses clock domains (static signal)
   - No timing violations (data stable throughout)

3. **Data Latch (Destination Domain):**
   - Data latched into r_dst_data when REQ synchronized
   - Held stable until dst_ready asserted

**Key Property:** Data never changes while crossing domains (setup/hold violations impossible).

---

## Usage Example

### Basic CDC for Monitor Packets (64-bit)

```systemverilog
// Monitor packets generated in monitor clock domain
// Must cross to system clock domain for processing

cdc_handshake #(
    .DATA_WIDTH         (64)  // AXI monitor packet width
) u_packet_cdc (
    // Source: Monitor clock domain
    .clk_src            (mon_clk),
    .rst_src_n          (mon_rst_n),
    .src_valid          (mon_pkt_valid),
    .src_ready          (mon_pkt_ready),
    .src_data           (mon_pkt_data),

    // Destination: System clock domain
    .clk_dst            (sys_clk),
    .rst_dst_n          (sys_rst_n),
    .dst_valid          (sys_pkt_valid),
    .dst_ready          (sys_pkt_ready),
    .dst_data           (sys_pkt_data)
);

// Source domain: Monitor packet generation
always_ff @(posedge mon_clk or negedge mon_rst_n) begin
    if (!mon_rst_n) begin
        mon_pkt_valid <= 1'b0;
    end else begin
        if (packet_generated && mon_pkt_ready) begin
            mon_pkt_valid <= 1'b1;
            mon_pkt_data <= new_packet;
        end else if (mon_pkt_ready) begin
            mon_pkt_valid <= 1'b0;
        end
    end
end

// Destination domain: Packet processing
always_ff @(posedge sys_clk or negedge sys_rst_n) begin
    if (!sys_rst_n) begin
        sys_pkt_ready <= 1'b0;
    end else begin
        if (sys_pkt_valid && processing_ready) begin
            sys_pkt_ready <= 1'b1;
            process_packet(sys_pkt_data);
        end else begin
            sys_pkt_ready <= 1'b0;
        end
    end
end
```

### Configuration Register Update Across Domains

```systemverilog
// CPU writes config register in AHB clock domain
// Design uses config in AXI clock domain

cdc_handshake #(
    .DATA_WIDTH         (32)  // Configuration register width
) u_config_cdc (
    // Source: CPU/AHB clock domain
    .clk_src            (ahb_clk),
    .rst_src_n          (ahb_rst_n),
    .src_valid          (cfg_write_valid),
    .src_ready          (cfg_write_ready),
    .src_data           (cfg_write_data),

    // Destination: AXI logic clock domain
    .clk_dst            (axi_clk),
    .rst_dst_n          (axi_rst_n),
    .dst_valid          (cfg_update_valid),
    .dst_ready          (cfg_update_ready),
    .dst_data           (cfg_update_data)
);

// Source: AHB write decoder
always_ff @(posedge ahb_clk) begin
    if (ahb_write && addr_match && cfg_write_ready) begin
        cfg_write_valid <= 1'b1;
        cfg_write_data <= ahb_wdata;
    end else if (cfg_write_ready) begin
        cfg_write_valid <= 1'b0;
    end
end

// Destination: Configuration register update
always_ff @(posedge axi_clk or negedge axi_rst_n) begin
    if (!axi_rst_n) begin
        config_reg <= 32'h0;
        cfg_update_ready <= 1'b0;
    end else begin
        if (cfg_update_valid) begin
            config_reg <= cfg_update_data;
            cfg_update_ready <= 1'b1;
        end else begin
            cfg_update_ready <= 1'b0;
        end
    end
end
```

### Burst Transfer with Backpressure

```systemverilog
// Transfer burst of data with flow control

cdc_handshake #(
    .DATA_WIDTH         (128)  // Large data path
) u_burst_cdc (
    .clk_src            (src_clk),
    .rst_src_n          (src_rst_n),
    .src_valid          (burst_valid),
    .src_ready          (burst_ready),
    .src_data           (burst_data),

    .clk_dst            (dst_clk),
    .rst_dst_n          (dst_rst_n),
    .dst_valid          (fifo_wr_valid),
    .dst_ready          (fifo_wr_ready),
    .dst_data           (fifo_wr_data)
);

// Source: Burst generator
logic [7:0] burst_count;

always_ff @(posedge src_clk or negedge src_rst_n) begin
    if (!src_rst_n) begin
        burst_count <= 8'd0;
        burst_valid <= 1'b0;
    end else begin
        if (start_burst) begin
            burst_count <= burst_length;
            burst_valid <= 1'b1;
            burst_data <= first_data;
        end else if (burst_valid && burst_ready) begin
            if (burst_count > 1) begin
                burst_count <= burst_count - 1;
                burst_data <= next_data;
                burst_valid <= 1'b1;
            end else begin
                burst_valid <= 1'b0;
            end
        end
    end
end

// Destination: FIFO with backpressure
assign fifo_wr_ready = !fifo_full;
```

---

## Design Notes

### Handshake Protocol Timing

**Latency Characteristics:**

**Minimum Transfer Latency (Fast Case):**
1. Source asserts REQ (clk_src cycle N)
2. REQ synchronization: 3 clk_dst cycles
3. Destination asserts dst_valid (clk_dst cycle N+3)
4. Destination samples dst_ready (clk_dst cycle N+3 or later)
5. Destination asserts ACK (clk_dst cycle N+4)
6. ACK synchronization: 3 clk_src cycles
7. Source sees ACK (clk_src cycle N+7)
8. Source ready for next transfer (clk_src cycle N+8)

**Total: 6-8 cycles in fast clock + 3-4 cycles in slow clock**

**Maximum Transfer Latency (Slow Case):**
- Add dst_ready assertion delay (unbounded, depends on receiver)
- Add clock frequency ratio effects

**Throughput:**
- Limited by handshake round-trip latency
- Not suitable for high-throughput streaming (use async FIFO instead)
- Optimal for control signals, configuration, low-rate data

### Reset Considerations

**Independent Domain Resets:**
- Each FSM has domain-specific reset
- Resets can be asynchronous to each other
- Design handles reset in one domain while other operates

**Reset Recovery:**
1. Source domain reset: FSM returns to S_IDLE, REQ=0
2. Destination domain reset: FSM returns to D_IDLE, ACK=0
3. Any in-flight handshake abandoned (safe by design)
4. Synchronizers clear to 3'b000 (deasserted state)

**Recommendation:** Assert both resets together during system initialization for clean startup.

### Data Width Considerations

**Wide Data Buses (64+ bits):**
- Large fanout from r_async_data register
- Consider pipelining if timing closure issues
- Area cost: DATA_WIDTH × 2 flip-flops (r_async_data + r_dst_data)

**Narrow Data Buses (1-8 bits):**
- Minimal area overhead
- Still requires full handshake protocol (latency same as wide buses)

**Alternative for Streaming:** If high-throughput needed, use async FIFO instead.

### Metastability Protection Validation

**Synchronizer Verification:**

**Static Timing Analysis:**
- Ensure no timing paths between asynchronous domains (except through synchronizers)
- Verify synchronizer stages have no combinational logic
- Check recovery/removal timing on first stage (expect violations, safe by design)

**Formal Verification:**
```systemverilog
// CDC assertion: REQ/ACK only change in respective domains
assert property (@(posedge clk_src)
    !$rose(r_ack_dst) && !$fell(r_ack_dst));  // ACK only changes in dst domain

assert property (@(posedge clk_dst)
    !$rose(r_req_src) && !$fell(r_req_src));  // REQ only changes in src domain
```

**Simulation:**
- Use formal CDC checkers (Synopsys SpyGlass, Cadence JasperGold)
- Verify no X-propagation in synchronizer stages

### Performance Optimization

**When to Use CDC Handshake:**
- Control signals (low rate, <1% of clock frequency)
- Configuration registers (infrequent updates)
- Status synchronization (occasional transfers)

**When to Use Async FIFO Instead:**
- High-throughput data streaming
- Continuous data flow
- Burst transfers with sustained rate

**Hybrid Approach:**
```systemverilog
// Use async FIFO for data, CDC handshake for control
async_fifo #(.WIDTH(64), .DEPTH(16)) u_data_fifo (...);
cdc_handshake #(.WIDTH(8)) u_ctrl_cdc (...);
```

---

## Related Modules

### Used By
- AXI monitor bus aggregation (packet crossing between monitor and system clocks)
- Configuration register synchronization
- Status/control signal crossing in multi-clock systems
- Peripheral interface adapters with asynchronous clocks

### Dependencies
- **reset_defs.svh** - Standard reset macro definitions

### See Also
- **async_fifo** - High-throughput async FIFO for streaming data
- **reset_sync.sv** - Reset synchronizer for single-bit reset crossing

---

## References

### Source Code
- RTL: `rtl/amba/shared/cdc_handshake.sv`
- Tests: `val/common/test_cdc_handshake.py` (if available)

### Documentation
- Architecture: `docs/markdown/RTLAmba/shared/README.md`
- CDC Best Practices: Clifford E. Cummings, "Clock Domain Crossing (CDC) Design & Verification Techniques"
- Design Guide: `rtl/amba/PRD.md`

### Industry Standards
- IEEE 1364/1800 - Synchronizer modeling
- AMBA specifications - CDC requirements for multi-clock systems

---

**Last Updated:** 2025-10-24

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../index.md)

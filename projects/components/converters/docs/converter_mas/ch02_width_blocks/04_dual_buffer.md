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

# 2.4 Dual-Buffer Architecture

The dual-buffer mode for **axi_data_dnsize** achieves 100% throughput by using ping-pong buffering to eliminate the gap cycle between wide beat loads.

## 2.4.1 Problem Statement

### Single-Buffer Limitation

In single-buffer mode, there is an unavoidable gap cycle between completing output of one wide beat and starting output of the next:

```
Cycle N:   Output last narrow beat of wide beat A
Cycle N+1: Load wide beat B (gap - no output)
Cycle N+2: Output first narrow beat of wide beat B
```

This gap cycle reduces throughput to N/(N+1), or approximately 80-90% depending on the width ratio.

### High-Performance Requirements

Some applications require continuous 100% throughput:
- DDR memory controllers with sustained bandwidth
- DMA engines with continuous data flows
- Real-time video/audio processing

## 2.4.2 Solution: Ping-Pong Buffering

### Concept

Use two buffers that alternate between loading and outputting:

```
Time:     0   1   2   3   4   5   6   7   8   9  10  11
Buffer A: LD  O0  O1  O2  O3  O4  O5  O6  O7  LD  O0  O1
Buffer B:     LD  --  --  --  --  --  --  --  LD  --  --
Output:   --  A0  A1  A2  A3  A4  A5  A6  A7  B0  B1  B2

LD = Loading, On = Outputting beat n
```

While buffer A outputs its 8 narrow beats, buffer B loads the next wide beat. When buffer A completes, buffer B immediately starts outputting while buffer A loads.

### Figure 2.5: Dual-Buffer Ping-Pong Operation

![Dual-Buffer Operation](../assets/mermaid/dual_buffer_operation.png)

## 2.4.3 Implementation

### Buffer State Machine

Each buffer has three states:

```systemverilog
typedef enum logic [1:0] {
    BUF_IDLE      = 2'b00,  // Empty, ready to load
    BUF_LOADED    = 2'b01,  // Full, waiting to output
    BUF_OUTPUTTING = 2'b10  // Active output
} buf_state_t;

buf_state_t r_buf_a_state, r_buf_b_state;
```

### Output Arbiter

```systemverilog
// Select which buffer outputs
logic w_output_sel;  // 0 = buffer A, 1 = buffer B

always_comb begin
    if (r_buf_a_state == BUF_OUTPUTTING)
        w_output_sel = 1'b0;
    else if (r_buf_b_state == BUF_OUTPUTTING)
        w_output_sel = 1'b1;
    else if (r_buf_a_state == BUF_LOADED)
        w_output_sel = 1'b0;  // A ready first
    else if (r_buf_b_state == BUF_LOADED)
        w_output_sel = 1'b1;  // B ready
    else
        w_output_sel = 1'b0;  // Default
end
```

### Load Controller

```systemverilog
// Determine which buffer can accept new data
logic w_load_sel;  // 0 = buffer A, 1 = buffer B

always_comb begin
    if (r_buf_a_state == BUF_IDLE)
        w_load_sel = 1'b0;
    else if (r_buf_b_state == BUF_IDLE)
        w_load_sel = 1'b1;
    else
        w_load_sel = 1'b0;  // No buffer available
end

assign s_ready = (r_buf_a_state == BUF_IDLE) || (r_buf_b_state == BUF_IDLE);
```

### Buffer State Transitions

```systemverilog
// Buffer A state machine
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_buf_a_state <= BUF_IDLE;
    end else begin
        case (r_buf_a_state)
            BUF_IDLE: begin
                if (s_valid && s_ready && !w_load_sel) begin
                    r_buf_a_data <= s_data;
                    r_buf_a_state <= BUF_LOADED;
                end
            end

            BUF_LOADED: begin
                if (!w_output_sel || r_buf_b_state != BUF_OUTPUTTING)
                    r_buf_a_state <= BUF_OUTPUTTING;
            end

            BUF_OUTPUTTING: begin
                if (m_ready && r_buf_a_count == RATIO - 1)
                    r_buf_a_state <= BUF_IDLE;
            end
        endcase
    end
end

// Buffer B follows same pattern with opposite selection
```

## 2.4.4 Timing Analysis

### Continuous Operation

With dual buffering, the output is continuous:

| Cycle | Buffer A | Buffer B | Output |
|-------|----------|----------|--------|
| 0 | Load W0 | Idle | - |
| 1 | Output W0[0] | Load W1 | W0[0] |
| 2 | Output W0[1] | Wait | W0[1] |
| ... | ... | ... | ... |
| 8 | Output W0[7] | Wait | W0[7] |
| 9 | Load W2 | Output W1[0] | W1[0] |
| 10 | Wait | Output W1[1] | W1[1] |

: Table 2.10: Dual-Buffer Cycle Timing

### Latency

| Metric | Value |
|--------|-------|
| First beat latency | 1 cycle (load) |
| Sustained throughput | 100% |
| Buffer switch latency | 0 cycles |

: Table 2.11: Dual-Buffer Latency

## 2.4.5 Edge Cases

### Empty Pipeline Start

When starting from empty state:
1. First wide beat loads into buffer A
2. Buffer A starts outputting
3. Buffer B loads next wide beat
4. Continuous operation begins

### Pipeline Drain

When input stops (last beat processed):
1. Currently outputting buffer completes
2. Other buffer (if loaded) takes over
3. Pipeline drains to empty

### Backpressure Handling

If `m_ready` goes low:
1. Output stalls on current beat
2. Loading continues if buffer available
3. If both buffers full, `s_ready` goes low
4. Resumes when `m_ready` returns high

## 2.4.6 Resource Comparison

### Resource Breakdown

| Component | Single Buffer | Dual Buffer |
|-----------|---------------|-------------|
| Data registers | 512 bits | 1024 bits |
| Sideband registers | 64 bits | 128 bits |
| Beat counters | 3 bits | 6 bits |
| State machines | 1 | 2 + arbiter |
| Control logic | ~40 LEs | ~90 LEs |

: Table 2.12: Resource Breakdown

### Trade-off Summary

| Mode | Area | Throughput | Use Case |
|------|------|------------|----------|
| Single | 1x | 80-90% | Area-constrained, bursty traffic |
| Dual | 2x | 100% | Performance-critical, sustained traffic |

: Table 2.13: Mode Trade-offs

## 2.4.7 Configuration Guidelines

### When to Use Dual Buffer

**Recommended:**
- DDR/HBM memory interfaces
- DMA engines with sustained transfers
- Video/audio streaming paths
- Any path where 10-20% throughput loss is unacceptable

**Not Recommended:**
- Area-constrained designs
- Bursty traffic with gaps
- Control paths (low bandwidth)
- When latency is more critical than throughput

### Integration Example

```systemverilog
// High-performance read path for DDR controller
axi_data_dnsize #(
    .WIDE_WIDTH(512),
    .NARROW_WIDTH(64),
    .DUAL_BUFFER(1),          // Enable dual buffer
    .USE_BURST_TRACKER(1),
    .SB_BROADCAST(1)
) u_rdata_dnsize (
    // ... connections
);

// Low-bandwidth control path (save area)
axi_data_dnsize #(
    .WIDE_WIDTH(128),
    .NARROW_WIDTH(32),
    .DUAL_BUFFER(0),          // Single buffer OK
    .USE_BURST_TRACKER(0),
    .SB_BROADCAST(1)
) u_ctrl_dnsize (
    // ... connections
);
```

---

**Next:** [axi4_dwidth_converter_wr](05_dwidth_converter_wr.md)

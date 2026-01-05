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

# 4.3 Burst Decomposition

This section describes how converters decompose AXI4 bursts into smaller transactions.

## 4.3.1 Width Converter Burst Handling

### Burst Length Adjustment

When converting widths, burst length changes inversely with data width:

```
M_AWLEN = (S_AWLEN + 1) / RATIO - 1

Example (64-bit to 512-bit, RATIO=8):
  S_AWLEN = 7 (8 beats × 64 bits = 512 bits)
  M_AWLEN = (7 + 1) / 8 - 1 = 0 (1 beat × 512 bits)

  S_AWLEN = 15 (16 beats × 64 bits = 1024 bits)
  M_AWLEN = (15 + 1) / 8 - 1 = 1 (2 beats × 512 bits)
```

### Figure 4.5: Width Burst Conversion

![Width Burst Conversion](../assets/mermaid/width_burst_conversion.png)

### Non-Aligned Bursts

When burst length is not a multiple of ratio:

```
S_AWLEN = 5 (6 beats), RATIO = 8
M_AWLEN = (5 + 1) / 8 - 1 = -1 → 0 (1 beat)

The 6 narrow beats pack into 1 wide beat.
Last 2 positions have WSTRB = 0 (no write).
```

## 4.3.2 Protocol Converter Burst Handling

### AXI4 to AXI4-Lite Decomposition

AXI4-Lite only supports single-beat transactions, so all bursts must be decomposed:

```
AXI4 Burst:
  ARADDR = 0x1000
  ARLEN = 3 (4 beats)
  ARSIZE = 2 (4 bytes)

AXIL4 Sequence:
  Transaction 0: ARADDR = 0x1000
  Transaction 1: ARADDR = 0x1004
  Transaction 2: ARADDR = 0x1008
  Transaction 3: ARADDR = 0x100C
```

### Address Increment Calculation

```systemverilog
// Calculate address increment based on burst type and size
function automatic [ADDR_WIDTH-1:0] next_address(
    input [ADDR_WIDTH-1:0] current_addr,
    input [2:0] size,
    input [1:0] burst,
    input [7:0] len,
    input [7:0] beat
);
    logic [ADDR_WIDTH-1:0] increment;
    logic [ADDR_WIDTH-1:0] wrap_mask;

    increment = 1 << size;

    case (burst)
        2'b00: // FIXED
            return current_addr;  // No increment

        2'b01: // INCR
            return current_addr + increment;

        2'b10: // WRAP
            wrap_mask = ((len + 1) << size) - 1;
            return (current_addr & ~wrap_mask) |
                   ((current_addr + increment) & wrap_mask);

        default:
            return current_addr + increment;
    endcase
endfunction
```

## 4.3.3 Response Aggregation

### Read Response Aggregation

For burst reads decomposed into multiple single reads:

```systemverilog
// Track responses as they arrive
logic [7:0] r_response_count;
logic [1:0] r_worst_rresp;

always_ff @(posedge clk) begin
    if (start_new_burst) begin
        r_response_count <= '0;
        r_worst_rresp <= 2'b00;  // OKAY
    end else if (m_rvalid && m_rready) begin
        r_response_count <= r_response_count + 1;
        // Keep worst response
        if (m_rresp > r_worst_rresp)
            r_worst_rresp <= m_rresp;
    end
end

// Generate RLAST on final beat
assign s_rlast = (r_response_count == r_original_arlen);

// Forward individual responses or aggregate
assign s_rresp = m_rresp;  // Forward each response
// Or: assign s_rresp = r_worst_rresp; // Aggregate
```

### Write Response Aggregation

For burst writes:

```systemverilog
// Track worst response across burst
logic [1:0] r_worst_bresp;
logic r_all_beats_done;

always_ff @(posedge clk) begin
    if (start_new_burst)
        r_worst_bresp <= 2'b00;
    else if (m_bvalid && m_bready)
        r_worst_bresp <= (m_bresp > r_worst_bresp) ? m_bresp : r_worst_bresp;
end

// Send single aggregated B response
assign s_bvalid = r_all_beats_done;
assign s_bresp = r_worst_bresp;
```

## 4.3.4 Burst Tracking Registers

### Required State

```systemverilog
// Burst tracking registers
logic [ADDR_WIDTH-1:0] r_base_addr;
logic [ADDR_WIDTH-1:0] r_current_addr;
logic [7:0]            r_original_len;
logic [7:0]            r_remaining_beats;
logic [2:0]            r_size;
logic [1:0]            r_burst;
logic [ID_WIDTH-1:0]   r_id;
logic                  r_is_write;
```

### Initialization

```systemverilog
always_ff @(posedge clk) begin
    if (accept_new_transaction) begin
        r_base_addr <= s_axaddr;
        r_current_addr <= s_axaddr;
        r_original_len <= s_axlen;
        r_remaining_beats <= s_axlen;
        r_size <= s_axsize;
        r_burst <= s_axburst;
        r_id <= s_axid;
        r_is_write <= is_write_transaction;
    end else if (beat_complete) begin
        r_current_addr <= next_address(...);
        r_remaining_beats <= r_remaining_beats - 1;
    end
end
```

## 4.3.5 Timing Impact

### Decomposition Overhead

| Transaction Type | Overhead |
|------------------|----------|
| Single-beat | 0 cycles (passthrough) |
| 2-beat burst | 2 cycles (sequential) |
| N-beat burst | 2N cycles (2 per beat) |

: Table 4.6: Decomposition Overhead

### Pipeline Considerations

Decomposition is inherently sequential:
- Cannot issue next AR until previous R received (AXIL4)
- Cannot issue next AW/W until previous B received (AXIL4)

**Optimization:** Use response pipelining when downstream supports it.

---

**Next:** [Chapter 5: Verification](../ch05_verification/01_test_strategy.md)

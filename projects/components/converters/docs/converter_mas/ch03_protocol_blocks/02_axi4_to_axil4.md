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

# 3.2 AXI4 to AXI4-Lite Converter

The **axi4_to_axil4** converter family decomposes AXI4 burst transactions into sequential AXI4-Lite single-beat transactions.

## 3.2.1 Module Organization

```
axi4_to_axil4.sv          # Full bidirectional wrapper
├── axi4_to_axil4_rd.sv   # Read path converter
└── axi4_to_axil4_wr.sv   # Write path converter
```

### Design Philosophy

Separate read and write paths enable:
- Independent optimization
- Selective instantiation (read-only, write-only, or both)
- Simpler verification (test paths independently)

## 3.2.2 Read Path (axi4_to_axil4_rd)

### Block Diagram

### Figure 3.2: AXI4 to AXI4-Lite Read Path

![AXI4 to AXIL4 Read](../assets/mermaid/axi4_to_axil4_rd.png)

### Operation

**Single-Beat (ARLEN=0):**
```
Cycle 0: AR accepted (passthrough)
Cycle 1: R returned (passthrough)
Total: 0 extra cycles (pure passthrough)
```

**Multi-Beat (ARLEN=N-1):**
```
Cycle 0:   AR[0] issued to AXIL4
Cycle 1:   R[0] received, AR[1] issued
Cycle 2:   R[1] received, AR[2] issued
...
Cycle 2N-1: R[N-1] received (RLAST)
Total: 2N cycles (1 cycle per AR + 1 cycle per R)
```

### State Machine

```systemverilog
typedef enum logic [1:0] {
    IDLE       = 2'b00,  // Wait for AR
    DECOMPOSE  = 2'b01,  // Issuing single beats
    WAIT_R     = 2'b10   // Wait for last R
} rd_state_t;
```

### Implementation

```systemverilog
// Beat counter and address tracking
logic [7:0] r_beat_count;
logic [7:0] r_arlen_saved;
logic [ADDR_WIDTH-1:0] r_current_addr;

// State machine
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_state <= IDLE;
        r_beat_count <= '0;
    end else begin
        case (r_state)
            IDLE: begin
                if (s_arvalid && s_arready) begin
                    r_arlen_saved <= s_arlen;
                    r_current_addr <= s_araddr;
                    if (s_arlen == 0) begin
                        // Single beat - passthrough
                        r_state <= WAIT_R;
                    end else begin
                        r_state <= DECOMPOSE;
                        r_beat_count <= 8'd1;
                    end
                end
            end

            DECOMPOSE: begin
                if (m_arvalid && m_arready) begin
                    r_current_addr <= r_current_addr + (1 << s_arsize);
                    r_beat_count <= r_beat_count + 1;
                    if (r_beat_count == r_arlen_saved) begin
                        r_state <= WAIT_R;
                    end
                end
            end

            WAIT_R: begin
                if (s_rvalid && s_rready && s_rlast) begin
                    r_state <= IDLE;
                end
            end
        endcase
    end
end

// AXIL4 AR generation
assign m_arvalid = (r_state == DECOMPOSE) || (r_state == IDLE && s_arvalid);
assign m_araddr = r_current_addr;

// R aggregation
assign s_rlast = (r_beat_count == r_arlen_saved) || (r_arlen_saved == 0);
```

## 3.2.3 Write Path (axi4_to_axil4_wr)

### Block Diagram

### Figure 3.3: AXI4 to AXI4-Lite Write Path

![AXI4 to AXIL4 Write](../assets/mermaid/axi4_to_axil4_wr.png)

### Operation

**Single-Beat (AWLEN=0):**
```
Cycle 0: AW+W accepted (passthrough)
Cycle 1: B returned (passthrough)
Total: 0 extra cycles
```

**Multi-Beat (AWLEN=N-1):**
```
Cycle 0:   AW[0] + W[0] issued
Cycle 1:   B[0] received, AW[1] + W[1] issued
...
Cycle 2N-1: B[N-1] received
Total: 2N cycles
```

### AW/W Synchronization Challenge

AXI4 allows AW and W to arrive in any order:
- AW before W
- W before AW
- Interleaved

### Solution: Dual Accept Logic

```systemverilog
// Track AW and W arrival independently
logic r_aw_accepted;
logic r_w_accepted;

// Accept both when ready to issue
always_ff @(posedge clk) begin
    if (w_issue_axil4) begin
        r_aw_accepted <= 1'b0;
        r_w_accepted <= 1'b0;
    end else begin
        if (s_awvalid && s_awready)
            r_aw_accepted <= 1'b1;
        if (s_wvalid && s_wready)
            r_w_accepted <= 1'b1;
    end
end

// Issue AXIL4 when both available
assign w_issue_axil4 = (r_aw_accepted || s_awvalid) &&
                       (r_w_accepted || s_wvalid) &&
                       m_ready;
```

### Response Aggregation

```systemverilog
// Track worst response in burst
logic [1:0] r_worst_bresp;

always_ff @(posedge clk) begin
    if (r_state == IDLE)
        r_worst_bresp <= 2'b00;  // OKAY
    else if (m_bvalid && m_bready)
        r_worst_bresp <= (m_bresp > r_worst_bresp) ? m_bresp : r_worst_bresp;
end

// Return worst response on final beat
assign s_bresp = (r_beat_count == r_awlen_saved) ?
                 ((m_bresp > r_worst_bresp) ? m_bresp : r_worst_bresp) :
                 r_worst_bresp;
```

## 3.2.4 Bidirectional Wrapper (axi4_to_axil4)

### Composition Pattern

```systemverilog
module axi4_to_axil4 #(
    parameter int DATA_WIDTH = 32,
    parameter int ADDR_WIDTH = 32,
    parameter int ID_WIDTH   = 4
) (
    // ... ports
);

    // Instantiate read path
    axi4_to_axil4_rd #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .ID_WIDTH(ID_WIDTH)
    ) u_rd (
        // ... read channel connections
    );

    // Instantiate write path
    axi4_to_axil4_wr #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .ID_WIDTH(ID_WIDTH)
    ) u_wr (
        // ... write channel connections
    );

endmodule
```

## 3.2.5 Resource Utilization

| Module | Registers | LUTs | BRAM |
|--------|-----------|------|------|
| axi4_to_axil4_rd | ~120 | ~180 | 0 |
| axi4_to_axil4_wr | ~150 | ~220 | 0 |
| axi4_to_axil4 (combined) | ~270 | ~400 | 0 |

: Table 3.6: AXI4 to AXIL4 Resources

## 3.2.6 Performance Analysis

### Throughput

| Transaction Type | Throughput |
|------------------|------------|
| Single-beat | 100% (passthrough) |
| 2-beat burst | 50% |
| 4-beat burst | 50% |
| N-beat burst | ~50% |

: Table 3.7: AXI4 to AXIL4 Throughput

### Latency

| Transaction Type | Latency |
|------------------|---------|
| Single-beat | 0 extra cycles |
| N-beat burst | 2N - 1 cycles |

: Table 3.8: AXI4 to AXIL4 Latency

## 3.2.7 Test Coverage

**Test Suite:** 42 tests passing

| Test Category | Tests | Status |
|---------------|-------|--------|
| Single-beat read | 4 | Pass |
| Multi-beat read | 6 | Pass |
| Single-beat write | 4 | Pass |
| Multi-beat write | 6 | Pass |
| Mixed traffic | 8 | Pass |
| Error injection | 6 | Pass |
| Edge cases | 8 | Pass |

: Table 3.9: Test Coverage Summary

---

**Next:** [AXI4-Lite to AXI4](03_axil4_to_axi4.md)

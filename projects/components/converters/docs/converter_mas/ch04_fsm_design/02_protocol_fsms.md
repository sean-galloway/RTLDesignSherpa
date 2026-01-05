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

# 4.2 Protocol Converter FSMs

This section describes the state machines used in protocol converter modules.

## 4.2.1 AXI4 to AXI4-Lite Read FSM

### Figure 4.3: AXI4 to AXIL4 Read FSM

![AXI4 to AXIL4 Read FSM](../assets/mermaid/axi4_to_axil4_rd_fsm.png)

### States

| State | Description |
|-------|-------------|
| IDLE | Waiting for AR transaction |
| SINGLE | Single-beat passthrough |
| DECOMPOSE | Issuing burst as single beats |
| WAIT_R | Waiting for final R response |

: Table 4.3: AXI4 to AXIL4 Read FSM States

### Transitions

```
IDLE:
  - s_arvalid && s_arlen == 0 → SINGLE (passthrough)
  - s_arvalid && s_arlen > 0 → DECOMPOSE

SINGLE:
  - m_arready → forward AR, wait for R
  - m_rvalid && m_rready → IDLE

DECOMPOSE:
  - m_arready → issue single AR
  - increment address, decrement remaining
  - remaining == 0 → WAIT_R

WAIT_R:
  - s_rvalid && s_rready && s_rlast → IDLE
```

### Implementation

```systemverilog
typedef enum logic [1:0] {
    IDLE      = 2'b00,
    SINGLE    = 2'b01,
    DECOMPOSE = 2'b10,
    WAIT_R    = 2'b11
} rd_state_t;

rd_state_t r_state;
logic [7:0] r_beats_remaining;
logic [ADDR_WIDTH-1:0] r_current_addr;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_state <= IDLE;
    end else begin
        case (r_state)
            IDLE: begin
                if (s_arvalid && s_arready) begin
                    r_current_addr <= s_araddr;
                    r_beats_remaining <= s_arlen;
                    r_state <= (s_arlen == 0) ? SINGLE : DECOMPOSE;
                end
            end

            SINGLE: begin
                if (m_rvalid && s_rready)
                    r_state <= IDLE;
            end

            DECOMPOSE: begin
                if (m_arvalid && m_arready) begin
                    r_current_addr <= r_current_addr + (1 << r_arsize);
                    if (r_beats_remaining == 0)
                        r_state <= WAIT_R;
                    else
                        r_beats_remaining <= r_beats_remaining - 1;
                end
            end

            WAIT_R: begin
                if (s_rvalid && s_rready && s_rlast)
                    r_state <= IDLE;
            end
        endcase
    end
end
```

## 4.2.2 AXI4 to AXI4-Lite Write FSM

### States

| State | Description |
|-------|-------------|
| IDLE | Waiting for AW/W transactions |
| SYNC_AW_W | Synchronizing AW and W channels |
| DECOMPOSE | Issuing burst as single beats |
| WAIT_B | Waiting for all B responses |
| SEND_B | Sending aggregated B response |

: Table 4.4: AXI4 to AXIL4 Write FSM States

### AW/W Synchronization

```systemverilog
// Track which channels have been accepted
logic r_aw_pending, r_w_pending;

always_ff @(posedge clk) begin
    // Accept AW
    if (s_awvalid && s_awready && !r_aw_pending)
        r_aw_pending <= 1'b1;

    // Accept W
    if (s_wvalid && s_wready && !r_w_pending)
        r_w_pending <= 1'b1;

    // Issue AXIL4 when both ready
    if (w_issue_axil4) begin
        r_aw_pending <= 1'b0;
        r_w_pending <= 1'b0;
    end
end

assign w_issue_axil4 = (r_aw_pending || s_awvalid) &&
                       (r_w_pending || s_wvalid) &&
                       m_awready && m_wready;
```

## 4.2.3 AXI4 to APB FSM

### Figure 4.4: AXI4 to APB FSM

![AXI4 to APB FSM](../assets/mermaid/axi4_to_apb_fsm.png)

### States

| State | Description |
|-------|-------------|
| IDLE | Waiting for AXI4 transaction |
| APB_SETUP | APB setup phase (PSEL=1, PENABLE=0) |
| APB_ACCESS | APB access phase (PSEL=1, PENABLE=1) |
| AXI_RESP | Sending AXI4 response |
| BURST_NEXT | Preparing next beat in burst |

: Table 4.5: AXI4 to APB FSM States

### APB Protocol Phases

```
Setup Phase:
  - PSEL = 1
  - PENABLE = 0
  - PADDR, PWDATA, PWRITE stable
  - Duration: 1 cycle

Access Phase:
  - PSEL = 1
  - PENABLE = 1
  - Wait for PREADY
  - Sample PRDATA (read) or complete write
  - Duration: 1+ cycles (depends on PREADY)
```

### Implementation

```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_state <= IDLE;
        psel <= 1'b0;
        penable <= 1'b0;
    end else begin
        case (r_state)
            IDLE: begin
                psel <= 1'b0;
                penable <= 1'b0;
                if (s_awvalid || s_arvalid) begin
                    r_state <= APB_SETUP;
                    psel <= 1'b1;
                end
            end

            APB_SETUP: begin
                r_state <= APB_ACCESS;
                penable <= 1'b1;
            end

            APB_ACCESS: begin
                if (pready) begin
                    psel <= 1'b0;
                    penable <= 1'b0;
                    r_state <= AXI_RESP;
                end
            end

            AXI_RESP: begin
                if ((r_is_write && s_bready) ||
                    (!r_is_write && s_rready)) begin
                    if (r_beat_count == r_burst_len)
                        r_state <= IDLE;
                    else
                        r_state <= BURST_NEXT;
                end
            end

            BURST_NEXT: begin
                r_beat_count <= r_beat_count + 1;
                r_current_addr <= r_current_addr + (1 << r_size);
                r_state <= APB_SETUP;
                psel <= 1'b1;
            end
        endcase
    end
end
```

## 4.2.4 Timing Analysis

### AXI4 to AXIL4 Timing

**Single-beat transaction:**
```
Cycle 0: AR accepted
Cycle 1: AR forwarded to AXIL4
Cycle 2: R received from AXIL4
Cycle 3: R forwarded to AXI4
Total: ~2 cycles overhead (can be pipelined)
```

**N-beat burst:**
```
Cycle 0: AR accepted
Cycles 1-2N: Decomposed transactions
Total: 2N cycles
```

### AXI4 to APB Timing

**Single transfer:**
```
Cycle 0: AXI4 AR/AW accepted
Cycle 1: APB setup phase
Cycle 2+: APB access phase (wait PREADY)
Cycle N: APB complete, AXI4 response
Total: 3+ cycles (minimum)
```

---

**Next:** [Burst Decomposition](03_burst_decomposition.md)

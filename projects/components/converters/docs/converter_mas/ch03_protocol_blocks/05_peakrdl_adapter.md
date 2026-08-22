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

# 3.5 PeakRDL Adapter

The **peakrdl_to_cmdrsp** module drives a PeakRDL-generated register block from a command/response stream. Data flows cmd/rsp -> PeakRDL: `cmd_*` are inputs and `regblk_*` request signals are outputs, with the register block's acks and read data coming back in. The name reads in the opposite order to the dataflow; the ports below are authoritative.

## 3.5.1 Purpose

PeakRDL generates register blocks with an APB-style interface. This adapter sits behind that interface and:

1. Decouples the register interface from the implementation
2. Provides a clean handshake protocol
3. Enables pipelined register access
4. Supports custom control logic integration

## 3.5.2 Block Diagram

### Figure 3.8: PeakRDL Adapter

![PeakRDL Adapter](../assets/mermaid/peakrdl_adapter.png)

## 3.5.3 Interface Specification

### Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| ADDR_WIDTH | int | 32 | Address width |
| DATA_WIDTH | int | 32 | Data width |

: Table 3.20: PeakRDL Adapter Parameters

### Ports

```systemverilog
module peakrdl_to_cmdrsp #(
    parameter int ADDR_WIDTH = 12,  // Address width for cmd/rsp interface
    parameter int DATA_WIDTH = 32   // Must match PeakRDL generation (typically 32)
) (
    // Clock and Reset
    input  logic                    aclk,
    input  logic                    aresetn,

    // =========================================================================
    // CMD/RSP Interface (rtldesignsherpa standard)
    // =========================================================================
    // Command Channel
    input  logic                    cmd_valid,
    output logic                    cmd_ready,
    input  logic                    cmd_pwrite,         // 1=write, 0=read
    input  logic [ADDR_WIDTH-1:0]   cmd_paddr,          // Byte address
    input  logic [DATA_WIDTH-1:0]   cmd_pwdata,         // Write data
    input  logic [DATA_WIDTH/8-1:0] cmd_pstrb,          // Byte strobes

    // Response Channel
    output logic                    rsp_valid,
    input  logic                    rsp_ready,
    output logic [DATA_WIDTH-1:0]   rsp_prdata,         // Read data
    output logic                    rsp_pslverr,        // Error flag

    // =========================================================================
    // PeakRDL Passthrough Interface
    // =========================================================================
    output logic                    regblk_req,         // Request strobe
    output logic                    regblk_req_is_wr,   // Write flag
    output logic [ADDR_WIDTH-1:0]   regblk_addr,        // Address
    output logic [DATA_WIDTH-1:0]   regblk_wr_data,     // Write data
    output logic [DATA_WIDTH-1:0]   regblk_wr_biten,    // Write bit enables
    input  logic                    regblk_req_stall_wr, // Write stall
    input  logic                    regblk_req_stall_rd, // Read stall
    input  logic                    regblk_rd_ack,      // Read acknowledge
    input  logic                    regblk_rd_err,      // Read error
    input  logic [DATA_WIDTH-1:0]   regblk_rd_data,     // Read data
    input  logic                    regblk_wr_ack,      // Write acknowledge
    input  logic                    regblk_wr_err       // Write error
);
```

## 3.5.4 Operation

### Write Transaction

```
Cycle 0: reg_write asserted
         cmd_valid = 1, cmd_write = 1
Cycle 1: cmd_ready = 1 (downstream accepts)
         Wait for response
Cycle N: rsp_valid = 1
         reg_ack = 1
Cycle N+1: Transaction complete
```

### Read Transaction

```
Cycle 0: reg_read asserted
         cmd_valid = 1, cmd_write = 0
Cycle 1: cmd_ready = 1 (downstream accepts)
         Wait for response
Cycle N: rsp_valid = 1
         reg_rdata = rsp_rdata
         reg_ack = 1
Cycle N+1: Transaction complete
```

## 3.5.5 Implementation

```systemverilog
// State machine
typedef enum logic [1:0] {
    IDLE    = 2'b00,
    CMD     = 2'b01,
    RSP     = 2'b10
} state_t;

state_t r_state;
logic r_is_write;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_state <= IDLE;
    end else begin
        case (r_state)
            IDLE: begin
                if (reg_write || reg_read) begin
                    r_state <= CMD;
                    r_is_write <= reg_write;
                end
            end

            CMD: begin
                if (cmd_ready) begin
                    r_state <= RSP;
                end
            end

            RSP: begin
                if (rsp_valid) begin
                    r_state <= IDLE;
                end
            end
        endcase
    end
end

// Command interface
assign cmd_valid = (r_state == CMD);
assign cmd_addr = reg_addr;
assign cmd_wdata = reg_wdata;
assign cmd_write = r_is_write;

// Response interface
assign rsp_ready = (r_state == RSP);

// Register interface
assign reg_rdata = rsp_rdata;
assign reg_error = rsp_error;
assign reg_ack = (r_state == RSP) && rsp_valid;
```

## 3.5.6 Resource Utilization

```
State machine:  ~20 LUTs, ~10 regs
Data paths:     ~10 LUTs, ~40 regs
Control:        ~20 LUTs, ~5 regs

Total: ~50 LUTs, ~55 regs
```

## 3.5.7 Use Cases

### 1. PeakRDL to Custom Control

```
PeakRDL Registers → Adapter → Custom State Machine
                            → Hardware Accelerator
                            → Debug Controller
```

### 2. Register Access Logging

```
PeakRDL Registers → Adapter → Logger → Registers
                            ↓
                         Log Buffer
```

### 3. Pipeline Insertion

```
PeakRDL Registers → Adapter → Pipeline → Slow Registers
                             (for timing)
```

## 3.5.8 Integration Example

```systemverilog
// Instantiate PeakRDL-generated register block
my_regs u_regs (
    .clk        (clk),
    .rst_n      (rst_n),

    // APB-style interface from CPU
    .s_apb_psel    (apb_psel),
    .s_apb_penable (apb_penable),
    // ... other APB signals

    // Register interface to adapter
    .reg_addr   (reg_addr),
    .reg_wdata  (reg_wdata),
    .reg_write  (reg_write),
    .reg_read   (reg_read),
    .reg_rdata  (reg_rdata),
    .reg_error  (reg_error),
    .reg_ack    (reg_ack)
);

// Adapter to custom protocol
peakrdl_to_cmdrsp #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32)
) u_adapter (
    .clk        (clk),
    .rst_n      (rst_n),

    // From PeakRDL registers
    .reg_addr   (reg_addr),
    .reg_wdata  (reg_wdata),
    .reg_write  (reg_write),
    .reg_read   (reg_read),
    .reg_rdata  (reg_rdata),
    .reg_error  (reg_error),
    .reg_ack    (reg_ack),

    // To custom control logic
    .cmd_valid  (ctrl_cmd_valid),
    .cmd_ready  (ctrl_cmd_ready),
    .cmd_addr   (ctrl_cmd_addr),
    .cmd_wdata  (ctrl_cmd_wdata),
    .cmd_write  (ctrl_cmd_write),

    .rsp_valid  (ctrl_rsp_valid),
    .rsp_ready  (ctrl_rsp_ready),
    .rsp_rdata  (ctrl_rsp_rdata),
    .rsp_error  (ctrl_rsp_error)
);
```

---

**Next:** [Chapter 4: FSM Design](../ch04_fsm_design/01_width_fsms.md)

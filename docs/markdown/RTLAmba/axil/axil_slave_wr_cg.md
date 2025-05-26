# axil_slave_wr_cg

This SystemVerilog module implements an AXI-Lite slave write path with clock gating functionality. It handles the AW (address write), W (write data), and B (write response) channels of the AXI4-Lite interface with power-saving capabilities, error monitoring, buffering, and proper handshaking for AXI-Lite write transactions.

## Module Parameters

### AXI-Lite Parameters
- `AXIL_ADDR_WIDTH`: Width of the AXI-Lite address bus (default: 32).
- `AXIL_DATA_WIDTH`: Width of the AXI-Lite data bus (default: 32).
- `AXI_ID_WIDTH`: Width of the AXI ID field (default: 8) - used for error reporting.
- `AXIL_PROT_WIDTH`: Width of the AXI-Lite protection field (fixed at 3 for AXI-Lite).

### Skid Buffer Depths
- `SKID_DEPTH_AW`: Depth of the AW channel skid buffer (default: 2).
- `SKID_DEPTH_W`: Depth of the W channel skid buffer (default: 4).
- `SKID_DEPTH_B`: Depth of the B channel skid buffer (default: 2).

### FIFO Parameters
- `ERROR_FIFO_DEPTH`: Depth of the error reporting FIFO (default: 2).

### Timeout Parameters (in clock cycles)
- `TIMEOUT_AW`: Write address channel timeout (default: 1000).
- `TIMEOUT_W`: Write data channel timeout (default: 1000).
- `TIMEOUT_B`: Write response channel timeout (default: 1000).

### Clock Gating Parameters
- `CG_IDLE_COUNT_WIDTH`: Width of the idle counter (default: 4) - determines how many idle cycles before clock gating activates.

### Derived Parameters
- `AW`: Alias for AXIL_ADDR_WIDTH.
- `DW`: Alias for AXIL_DATA_WIDTH.
- `IW`: Alias for AXI_ID_WIDTH.
- `PW`: Alias for AXIL_PROT_WIDTH.

## Ports

### Global Signals
- `aclk`: System clock.
- `aresetn`: Active-low reset signal.

### Clock Gating Configuration
- `i_cfg_cg_enable`: Enable signal for clock gating functionality.
- `i_cfg_cg_idle_count [CG_IDLE_COUNT_WIDTH-1:0]`: Number of idle cycles before clock gating activates.

### Master AXI-Lite Interface (Input Side)

#### Write Address Channel (AW)
- `fub_awaddr [AXIL_ADDR_WIDTH-1:0]`: Address for the write transaction (output).
- `fub_awprot [AXIL_PROT_WIDTH-1:0]`: Protection type for the write transaction (output).
- Handshake signals: `fub_awvalid` (output), `fub_awready` (input).

#### Write Data Channel (W)
- `fub_wdata [AXIL_DATA_WIDTH-1:0]`: Write data (output).
- `fub_wstrb [AXIL_DATA_WIDTH/8-1:0]`: Write strobes (output).
- Handshake signals: `fub_wvalid` (output), `fub_wready` (input).

#### Write Response Channel (B)
- `fub_bresp [1:0]`: Write response (input).
- Handshake signals: `fub_bvalid` (input), `fub_bready` (output).

### Slave AXI-Lite Interface (Output Side to memory or backend)

#### Write Address Channel (AW)
- `s_axil_awaddr [AXIL_ADDR_WIDTH-1:0]`: Address for the write transaction (input).
- `s_axil_awprot [AXIL_PROT_WIDTH-1:0]`: Protection type for the write transaction (input).
- Handshake signals: `s_axil_awvalid` (input), `s_axil_awready` (output).

#### Write Data Channel (W)
- `s_axil_wdata [AXIL_DATA_WIDTH-1:0]`: Write data (input).
- `s_axil_wstrb [AXIL_DATA_WIDTH/8-1:0]`: Write strobes (input).
- Handshake signals: `s_axil_wvalid` (input), `s_axil_wready` (output).

#### Write Response Channel (B)
- `s_axil_bresp [1:0]`: Write response (output).
- Handshake signals: `s_axil_bvalid` (output), `s_axil_bready` (input).

### Error FIFO Interface
- `fub_error_type [3:0]`: Type of error detected.
- `fub_error_addr [AXIL_ADDR_WIDTH-1:0]`: Address associated with the error.
- `fub_error_id [AXI_ID_WIDTH-1:0]`: ID associated with the error.
- Handshake signals: `fub_error_valid`, `fub_error_ready`.

### Clock Gating Status
- `o_cg_gating`: Active gating indicator - shows when clock gating is active.
- `o_cg_idle`: All buffers empty indicator - shows when the module is in an idle state.

## Functionality

The module provides an AXI4-Lite slave write path with clock gating capability:

### Data Transfer Direction

The `axil_slave_wr_cg` module transfers data in the following directions:

1. **Write Address**: From slave-side input (`s_axil_aw*`) to master-side output (`fub_aw*`).
2. **Write Data**: From slave-side input (`s_axil_w*`) to master-side output (`fub_w*`).
3. **Write Response**: From master-side input (`fub_b*`) to slave-side output (`s_axil_b*`).

This reflects the typical flow in a slave interface where addresses and data come from the requester (slave side) and responses go back to the requester.

### Clock Gating

The module implements intelligent clock gating to reduce power consumption:

1. **Idle Detection**: Monitors activity on all channels to determine when the module is idle.
2. **Configurable Idle Threshold**: Uses the idle counter to determine when to activate clock gating.
3. **Status
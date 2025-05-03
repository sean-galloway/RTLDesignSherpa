# axi2apb_shim

This SystemVerilog module implements a complete AXI to APB bridge with clock domain crossing capabilities. It converts AXI transactions into equivalent APB transactions while providing robust crossing between the AXI and APB clock domains. This enables integration of APB peripherals into AXI-based systems with different clock domains.

## Module Parameters

### AXI Interface Parameters
- `DEPTH_AW`: Depth of the AW channel skid buffer (default: 2).
- `DEPTH_W`: Depth of the W channel skid buffer (default: 4).
- `DEPTH_B`: Depth of the B channel skid buffer (default: 2).
- `DEPTH_AR`: Depth of the AR channel skid buffer (default: 2).
- `DEPTH_R`: Depth of the R channel skid buffer (default: 4).

### Bridge Parameters
- `SIDE_DEPTH`: Depth of the side queue for transaction tracking (default: 4).
- `APB_CMD_DEPTH`: Depth of the APB command FIFO (default: 4).
- `APB_RSP_DEPTH`: Depth of the APB response FIFO (default: 4).

### Interface Width Parameters
- `AXI_ID_WIDTH`: Width of the AXI ID field (default: 8).
- `AXI_ADDR_WIDTH`: Width of the AXI address bus (default: 32).
- `AXI_DATA_WIDTH`: Width of the AXI data bus (default: 32).
- `AXI_USER_WIDTH`: Width of the AXI user field (default: 1).
- `APB_ADDR_WIDTH`: Width of the APB address bus (default: 32).
- `APB_DATA_WIDTH`: Width of the APB data bus (default: 32).

### Derived Parameters
- Various shorthands (AW, DW, IW, UW, etc.) for more concise references.
- `AXI2APBRATIO`: Ratio of AXI data width to APB data width.
- Various packet widths for AXI and APB formats.

## Ports

### Clock and Reset
- `aclk`: AXI domain clock.
- `aresetn`: AXI domain active-low reset.
- `pclk`: APB domain clock.
- `presetn`: APB domain active-low reset.

### AXI Slave Interface

#### Write Address Channel (AW)
- Complete set of AW channel signals including ID, address, burst information, protection, QoS, etc.
- Handshake signals: `s_axi_awvalid`, `s_axi_awready`.

#### Write Data Channel (W)
- Complete set of W channel signals including data, strobe, last indicator, etc.
- Handshake signals: `s_axi_wvalid`, `s_axi_wready`.

#### Write Response Channel (B)
- Complete set of B channel signals including ID, response, etc.
- Handshake signals: `s_axi_bvalid`, `s_axi_bready`.

#### Read Address Channel (AR)
- Complete set of AR channel signals including ID, address, burst information, protection, QoS, etc.
- Handshake signals: `s_axi_arvalid`, `s_axi_arready`.

#### Read Data Channel (R)
- Complete set of R channel signals including ID, data, response, last indicator, etc.
- Handshake signals: `s_axi_rvalid`, `s_axi_rready`.

### APB Master Interface

- `m_apb_PSEL`: Peripheral select signal.
- `m_apb_PADDR [APB_ADDR_WIDTH-1:0]`: Address signal.
- `m_apb_PENABLE`: Enable signal for APB transfer.
- `m_apb_PWRITE`: Write direction signal.
- `m_apb_PWDATA [APB_DATA_WIDTH-1:0]`: Write data signal.
- `m_apb_PSTRB [APB_DATA_WIDTH/8-1:0]`: Write strobe signal.
- `m_apb_PPROT [2:0]`: Protection type signal.
- `m_apb_PRDATA [APB_DATA_WIDTH-1:0]`: Read data signal.
- `m_apb_PREADY`: Ready signal from peripheral.
- `m_apb_PSLVERR`: Error response signal.

## Functionality

### Protocol Translation

The module converts between AXI and APB protocols by:

1. **AXI Interface Handling**:
   - Uses `axi_slave_stub` to provide the AXI slave interface.
   - Converts AXI transactions to internal packet formats for further processing.

2. **Protocol Conversion**:
   - Uses `axi2apb_convert` to translate AXI transactions to APB format.
   - Handles differences in transaction models, data widths, and handshaking.

3. **Clock Domain Crossing**:
   - Uses `cdc_handshake` instances for safe crossing of command and response packets.
   - Implements four-phase handshake for robust clock domain crossing.

4. **APB Master Interface**:
   - Uses `apb_master_stub` to generate APB protocol signals.
   - Implements proper APB protocol timing and handshaking.

### Data Path Flow

The data flow through the module follows this path:

1. AXI transactions are received by the AXI slave interface.
2. The AXI transactions are converted to packed data formats.
3. The packed AXI data is translated to APB command packets.
4. The APB command packets cross the clock domain from AXI to APB.
5. The APB master interface executes the commands.
6. APB responses cross back from the APB clock domain to the AXI clock domain.
7. The responses are translated back to AXI format and returned to the AXI master.

## Implementation Details

### Top-Level Structure

The module uses a hierarchical design approach with four major components:

1. **AXI Slave Stub**: Handles the AXI interface and converts transactions to internal packet formats.
2. **AXI to APB Converter**: Translates AXI transactions to APB format.
3. **Clock Domain Crossing**: Provides safe crossing between AXI and APB clock domains.
4. **APB Master Stub**: Generates APB protocol signals for interfacing with peripherals.

### Clock Domain Crossing

The module implements robust clock domain crossing through:

1. **Command CDC**:
   - APB command packets cross from AXI to APB domain.
   - Uses four-phase handshake for reliable transfer.

2. **Response CDC**:
   - APB response packets cross from APB to AXI domain.
   - Also uses four-phase handshake for reliability.

3. **Reset Synchronization**:
   - Each domain operates with its own reset (aresetn and presetn).
   - CDC components handle reset properly in both domains.

### Packet Formats

The module uses packed formats for internal data representation:

1. **AXI Packet Formats**:
   - AW, W, B, AR, and R channels each have their own packet format.
   - Combines all relevant signals for each channel into a single packet.

2. **APB Command Packet Format**:
   - Includes address, data, strobes, control flags, etc.
   - Used for crossing from AXI to APB domain.

3. **APB Response Packet Format**:
   - Includes read data, error status, and control flags.
   - Used for crossing from APB to AXI domain.

## Usage Considerations

1. **Clock Domain Relationship**:
   - The module supports independent AXI and APB clock domains.
   - No specific frequency relationship is required between the domains.
   - Synchronous operation is also supported (same clock for both domains).

2. **Data Width Ratio**:
   - For optimal performance, AXI_DATA_WIDTH should be a multiple of APB_DATA_WIDTH.
   - Common configurations: 32-bit APB with 32/64/128-bit AXI.

3. **Buffer Sizing**:
   - Buffer depths affect performance and resource usage.
   - Deeper buffers improve performance but consume more resources.

4. **APB Peripheral Timing**:
   - APB peripherals must adhere to standard APB timing requirements.
   - The module handles all necessary protocol translation and timing requirements.

## Integration Example

```systemverilog
axi2apb_shim #(
    .AXI_DATA_WIDTH(64),           // 64-bit AXI data bus
    .APB_DATA_WIDTH(32),           // 32-bit APB data bus
    .APB_CMD_DEPTH(8),             // Deeper command FIFO
    .APB_RSP_DEPTH(8)              // Deeper response FIFO
) i_axi2apb_shim (
    // AXI clock domain
    .aclk(axi_clock),
    .aresetn(axi_reset_n),
    
    // APB clock domain
    .pclk(peripheral_clock),
    .presetn(peripheral_reset_n),
    
    // Connect AXI slave interface
    // ... (connection of all AXI signals) ...
    
    // Connect APB master interface
    .m_apb_PSEL(apb_psel),
    .m_apb_PADDR(apb_paddr),
    .m_apb_PENABLE(apb_penable),
    .m_apb_PWRITE(apb_pwrite),
    .m_apb_PWDATA(apb_pwdata),
    .m_apb_PSTRB(apb_pstrb),
    .m_apb_PPROT(apb_pprot),
    .m_apb_PRDATA(apb_prdata),
    .m_apb_PREADY(apb_pready),
    .m_apb_PSLVERR(apb_pslverr)
);
```

## Design Considerations

1. **Throughput Optimization**:
   - The module is optimized for efficient throughput despite the clock domain crossing.
   - Buffer depths can be tuned to balance performance and resource usage.

2. **CDC Robustness**:
   - The four-phase handshake ensures reliable data transfer between domains.
   - Metastability protection is implemented for all signals crossing domains.

3. **Reset Handling**:
   - Each domain has its own reset signal.
   - The module handles asynchronous resets properly to ensure clean startup.

4. **Error Propagation**:
   - APB errors (PSLVERR) are properly propagated back to the AXI domain.
   - AXI responses include appropriate error codes for failed transactions.

---

[Return to Index](index.md)

---
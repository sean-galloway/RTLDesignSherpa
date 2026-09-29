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

# AMBA Interface Adapters

Generic, reusable protocol adapters for AMBA and register interfaces.

## peakrdl_to_cmdrsp

> Full module reference — parameters, ports, both state machines, strobe
> conversion and stall handling — is in
> [`peakrdl_to_cmdrsp.md`](peakrdl_to_cmdrsp.md), moved here from the AMBA
> book on 2026-09-01 so it sits with the module it documents. This page is
> the shorter integration note.


**Purpose**: Bridges PeakRDL-generated register blocks (passthrough cpuif) to rtldesignsherpa's cmd/rsp valid/ready interface.

**Features**:
- Generic, works with ANY PeakRDL-generated register block using passthrough cpuif
- Handles valid/ready protocol conversion
- Manages backpressure from register block stalls
- Converts byte strobes to bit enables
- Parameterizable address and data widths
- Includes assertions for protocol checking

### Usage Example

```systemverilog
// Instantiate the generic adapter
peakrdl_to_cmdrsp #(
    .ADDR_WIDTH(12),    // Match your address space
    .DATA_WIDTH(32)     // Must match PeakRDL generation
) u_peakrdl_to_cmdrsp (
    .aclk                  (aclk),
    .aresetn               (aresetn),
    .cmd_valid             (cmd_valid),
    .cmd_ready             (cmd_ready),
    .cmd_pwrite            (cmd_pwrite),
    .cmd_paddr             (cmd_paddr),
    .cmd_pwdata            (cmd_pwdata),
    .cmd_pstrb             (cmd_pstrb),
    .rsp_valid             (rsp_valid),
    .rsp_ready             (rsp_ready),
    .rsp_prdata            (rsp_prdata),
    .rsp_pslverr           (rsp_pslverr),
    .regblk_req            (regblk_req),
    .regblk_req_is_wr      (regblk_req_is_wr),
    .regblk_addr           (regblk_addr),
    .regblk_wr_data        (regblk_wr_data),
    .regblk_wr_biten       (regblk_wr_biten),
    .regblk_req_stall_wr   (regblk_req_stall_wr),
    .regblk_req_stall_rd   (regblk_req_stall_rd),
    .regblk_rd_ack         (regblk_rd_ack),
    .regblk_rd_err         (regblk_rd_err),
    .regblk_rd_data        (regblk_rd_data),
    .regblk_wr_ack         (regblk_wr_ack),
    .regblk_wr_err         (regblk_wr_err)
);
```

### Protocol Details

**CMD/RSP Interface (rtldesignsherpa standard)**:
- **Command Channel**: `cmd_valid`, `cmd_ready`, `cmd_pwrite`, `cmd_paddr`, `cmd_pwdata`, `cmd_pstrb`
  - Valid/ready handshake
  - Command held stable until ready asserted
  - `cmd_pwrite`: 1=write, 0=read
  - `cmd_pstrb`: Byte strobes (one bit per byte)

- **Response Channel**: `rsp_valid`, `rsp_ready`, `rsp_prdata`, `rsp_pslverr`
  - Valid/ready handshake
  - Response held stable until ready asserted
  - `rsp_pslverr`: Error flag (1=error, 0=success)

**PeakRDL Passthrough Interface**:
- **Request**: `regblk_req` (single-cycle strobe), `regblk_req_is_wr`, `regblk_addr`, `regblk_wr_data`, `regblk_wr_biten`
- **Stall**: `regblk_req_stall_wr`, `regblk_req_stall_rd` (backpressure)
- **Response**: `regblk_rd_ack`, `regblk_wr_ack` (single-cycle strobes), `regblk_rd_data`, `regblk_rd_err`, `regblk_wr_err`

### Integration Notes

1. **Address Width**: The adapter's `ADDR_WIDTH` should match your full address space. The PeakRDL-generated module will use fewer bits (calculated from register map size).

2. **Reset Polarity**: Note that PeakRDL uses **active-high reset** while rtldesignsherpa uses **active-low reset**. The adapter handles active-low; you need to invert for PeakRDL (see example).

3. **No Wrapper Needed**: This is a **generic adapter** - instantiate it alongside your PeakRDL register block at the top level. No wrapper module required!

4. **Reusability**: Same adapter works for all PeakRDL-generated register blocks in your project. Just parameterize appropriately.

### See Also

- **Example**: `projects/components/retro_legacy_blocks/rtl/hpet/apb4_hpet.sv` (shows full integration of PeakRDL-generated registers; the old `hpet_regs_wrapper.sv` was superseded)
- **PeakRDL docs**: https://peakrdl-regblock.readthedocs.io/
- **SystemRDL spec**: https://www.accellera.org/downloads/standards/systemrdl

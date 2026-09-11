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

# wb4_master_retry

## Overview

`wb4_master_retry` is [wb4_retry](wb4_retry.md) in front of
[wb4_master](wb4_master.md): the master's command/response queue contract
and Wishbone B4 ports, with `RTY` terminations retried up to
`cfg_max_retries` times, `cfg_retry_delay` clocks apart, before the FUB
sees one. Drop it in where `wb4_master` would go when the slave is known
to retry.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| ADDR_WIDTH | int | 32 | Wishbone address width |
| DATA_WIDTH | int | 32 | Wishbone data width |
| CMD_DEPTH | int | 4 | Master command queue depth |
| RSP_DEPTH | int | 4 | Master response queue depth; bounds the transfers on the bus |
| CLASSIC | int | 0 | 0 = B4 pipelined, 1 = B4 standard (classic) mode |
| INFLIGHT | int | 1 | Retry block completion-buffer depth. 1 = strict program order (see wb4_retry) |
| USE_BURST_HINTS | int | 0 | 0 = `m_wb_CTI`/`m_wb_BTE` read CLASSIC/LINEAR and `cmd_cti`/`cmd_bte` are ignored; 1 = the hints are carried, and they ride **in the retry buffer** so a re-issued transfer carries its own hint |

With `INFLIGHT = 1` the bus carries one transfer at a time regardless of
`RSP_DEPTH`; set `INFLIGHT` up to `RSP_DEPTH` for pipelined traffic that
tolerates a retried transfer completing behind later ones.

## Ports

`wb4_master`'s ports (`clk`, `aresetn`, `m_wb_*` including `m_wb_CTI [2:0]`
and `m_wb_BTE [1:0]`, `cmd_*` including `cmd_cti [2:0]` and `cmd_bte [1:0]`,
`rsp_*`) plus
`cfg_max_retries [7:0]`, `cfg_retry_delay [15:0]`, `retry_count [31:0]` and
`active_count [7:0]` from the retry block.

## Usage Example

```systemverilog
wb4_master_retry #(
    .ADDR_WIDTH (32),
    .DATA_WIDTH (32),
    .CMD_DEPTH  (4),
    .RSP_DEPTH  (4),
    .INFLIGHT   (1)
) u_wb_master (
    .clk (clk), .aresetn (rst_n),
    .cfg_max_retries (8'd3),
    .cfg_retry_delay (16'd16),
    .m_wb_CYC (wb_cyc), .m_wb_STB (wb_stb), .m_wb_WE (wb_we), .m_wb_ADR (wb_adr),
    .m_wb_DAT_W (wb_dat_w), .m_wb_SEL (wb_sel),
    .m_wb_STALL (wb_stall), .m_wb_ACK (wb_ack), .m_wb_ERR (wb_err), .m_wb_RTY (wb_rty),
    .m_wb_DAT_R (wb_dat_r),
    .cmd_valid (cmd_valid), .cmd_ready (cmd_ready), .cmd_we (cmd_we), .cmd_adr (cmd_adr),
    .cmd_dat (cmd_dat), .cmd_sel (cmd_sel),
    .rsp_valid (rsp_valid), .rsp_ready (rsp_ready), .rsp_status (rsp_status), .rsp_dat (rsp_dat),
    .retry_count (), .active_count ()
);
```

## Related

- [wb4_retry](wb4_retry.md), [wb4_master](wb4_master.md)

## Test

`val/amba/test_wb4_master_retry.py`; see [wb4_retry](wb4_retry.md).

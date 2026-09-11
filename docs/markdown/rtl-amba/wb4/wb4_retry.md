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

# wb4_retry

## Overview

`wb4_retry` sits on the FUB side of `wb4_master` and turns a Wishbone
`RTY` into a retry. Every command the FUB issues is held in an in-order
completion buffer until its answer has been handed back. `ACK` and `ERR`
complete the entry as they arrive. `RTY` puts the entry back on the issue
path after `cfg_retry_delay` clocks, until `cfg_max_retries` re-issues
have been spent; only then does the FUB see the `RTY`. Responses reach
the FUB in command order whatever happened on the bus, and re-issues
always take priority over new commands.

`cfg_max_retries = 0` makes the block a pass-through. `wb4_master_retry`
is the block and the master together, with the master's ports.

**Order on the bus.** A retried command re-appears on the bus behind the
commands issued after it, which with `INFLIGHT > 1` may already have
terminated. The FUB still gets its responses in order, but a read issued
behind a write that was retried can observe memory from before that
write. `INFLIGHT = 1`, the default, keeps program order exactly: one
command on the bus at a time, retries included. Use `INFLIGHT > 1` only
for traffic with no ordering dependence across transfers.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| ADDR_WIDTH | int | 32 | Wishbone address width |
| DATA_WIDTH | int | 32 | Wishbone data width |
| INFLIGHT | int | 1 | Completion-buffer entries: commands accepted from the FUB and not yet answered. 1 = strict program order |

## Ports

```systemverilog
module wb4_retry
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int INFLIGHT   = 1,
    // Short Parameters
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = DW/8,
    parameter int STW = WB4_STATUS_WIDTH,
    parameter int CTW = WB4_CTI_WIDTH,
    parameter int BTW = WB4_BTE_WIDTH
)
(
    input  logic              clk,
    input  logic              aresetn,

    input  logic [7:0]        cfg_max_retries,   // 0 = pass RTY through
    input  logic [15:0]       cfg_retry_delay,   // clocks from RTY to re-issue

    // FUB side: the same contract wb4_master offers
    input  logic              cmd_valid,
    output logic              cmd_ready,
    input  logic              cmd_we,
    input  logic [AW-1:0]     cmd_adr,
    input  logic [DW-1:0]     cmd_dat,
    input  logic [SW-1:0]     cmd_sel,
    input  logic [CTW-1:0]    cmd_cti,           // burst hint, stored with its transfer
    input  logic [BTW-1:0]    cmd_bte,
    output logic              rsp_valid,
    input  logic              rsp_ready,
    output logic [1:0]        rsp_status,        // WB4_RSP_ACK / ERR / RTY
    output logic [DW-1:0]     rsp_dat,

    // wb4_master side
    output logic              mst_cmd_valid,
    input  logic              mst_cmd_ready,
    output logic              mst_cmd_we,
    output logic [AW-1:0]     mst_cmd_adr,
    output logic [DW-1:0]     mst_cmd_dat,
    output logic [SW-1:0]     mst_cmd_sel,
    output logic [CTW-1:0]    mst_cmd_cti,
    output logic [BTW-1:0]    mst_cmd_bte,
    input  logic              mst_rsp_valid,
    output logic              mst_rsp_ready,
    input  logic [1:0]        mst_rsp_status,
    input  logic [DW-1:0]     mst_rsp_dat,

    output logic [31:0]       retry_count,       // re-issues since reset
    output logic [7:0]        active_count       // entries in the buffer
);
```

### Configuration

`cfg_max_retries` is the number of re-issues allowed per command, not the
number of attempts: with 3, a command is presented to the bus at most
four times. `cfg_retry_delay` is the number of clocks between the `RTY`
and the re-issue; 0 re-issues on the next clock the master can take a
command. Both are sampled when used, so they can change between
transfers.

### Status

`retry_count` counts every re-issue since reset. `active_count` is the
number of commands accepted from the FUB and not yet answered, at most
`INFLIGHT`.

## Functional Description

Each entry of the completion buffer holds the command (`we`, `adr`,
`dat`, `sel`), a retry count, a delay timer and, once answered, the
status and read data. Entries are allocated at the tail when a command is
accepted and released at the head when the FUB takes the response, so the
FUB order is the buffer order. A separate issue log records which entry
each command handed to the master belongs to, in the order the master
received them; Wishbone terminates in that order, so the log head is
always the entry a termination belongs to.

| Event | Effect |
|---|---|
| `cmd_valid && cmd_ready` | Entry allocated at the tail and forwarded to `mst_cmd_*` in the same clock |
| `mst_rsp_*` handshake, `ACK` or `ERR` | Log-head entry marked done with the status and data |
| `mst_rsp_*` handshake, `RTY`, retries left | Entry marked waiting, retry count +1, timer loaded with `cfg_retry_delay`, `retry_count` +1 |
| `mst_rsp_*` handshake, `RTY`, budget spent | Entry marked done with `RTY` |
| Waiting entry with timer at 0 | Re-issued on `mst_cmd_*` before any new command (oldest first) |
| Head entry done | `rsp_valid`; released on the handshake |

`cmd_ready` is low while a retry is pending issue, while the buffer is
full, and while the master cannot take a command — so a FUB never has a
command accepted that would be reordered behind a retry. `mst_rsp_ready`
is high whenever a command is on the bus: the termination's entry is
waiting for it, so the master is never back-pressured on a response.

## Timing

- A new command reaches `mst_cmd_*` combinationally in the clock it is
  accepted; the master's own skid buffer registers it.
- A termination is recorded in the clock it arrives; `rsp_valid` for the
  head follows one clock later (registered state).
- With `INFLIGHT = 1` the bus carries one transfer at a time, so the
  sustained rate is one transfer per round trip. With `INFLIGHT = N` and
  a master `RSP_DEPTH >= N`, up to N transfers are open.

## Design Notes

- Under `ifdef FORMAL` the block asserts the occupancy bounds of both the
  buffer and the issue log, that everything on the bus is an allocated
  entry, that a retry is never issued in the clock a new command is
  accepted, and that the FUB only ever sees the head once it is done.
  `formal/amba/wb4_retry/` adds the port-level contract (payload equality
  of every re-issue, `1 + retries` issues per command, the budget and the
  delay, `RTY` to the FUB only once the budget is spent) at `INFLIGHT =
  1` and the bounds at `INFLIGHT = 2`.
- The block does not know why the slave retried. Back-off is a fixed
  delay; a slave that needs a longer or growing gap needs a larger
  `cfg_retry_delay` from the controlling software.

## Related Modules

- [wb4_master_retry](wb4_master_retry.md) — this block with `wb4_master`
  behind it
- [wb4_master](wb4_master.md) — what it drives
- [axil4_to_wb4](../../../../projects/components/converters/docs/converter_mas/ch03_protocol_blocks/10_axil4_to_wb4.md) — a bridge that maps `RTY` to an AXI error; put this block between it and the master to retry instead

## Testing

`val/amba/test_wb4_master_retry.py`, through the wrapper: the framework
Wishbone slave answers with address windows that retry a bounded number
of times, retry forever, or error, so every FUB response, the number of
re-issues (`retry_count`, the monitor's transfer count, the slave's `RTY`
count) and the read data follow from the model. Formal:
`formal/amba/wb4_retry/`.

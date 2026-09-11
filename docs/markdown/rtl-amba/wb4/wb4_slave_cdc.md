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

# wb4_slave_cdc

## Overview

[wb4_slave](wb4_slave.md) with its command and response queues carried
across a clock-domain boundary. The Wishbone bus lives in `wb_clk`; the
FUB's `cmd_*`/`rsp_*` queues live in `aclk`. Two `gaxi_fifo_async`
instances do the crossing (commands `wb_clk -> aclk`, responses `aclk ->
wb_clk`), the same structure as
[apb4_slave_cdc](../apb4/apb4_slave_cdc.md). In-order termination is
preserved because both crossings are FIFOs.

## Parameters

In addition to all `wb4_slave` parameters:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| CDC_DEPTH | int | 4 | Async FIFO depth, floored at 4; power of two preferred (Gray pointers) |
| USE_JOHNSON | int | 0 | 0 = Gray pointers (power-of-two depth), 1 = Johnson pointers (any depth) |

## Ports

`wb4_slave`'s ports, with the clock and reset split by domain:

| Port | Domain | Description |
|---|---|---|
| `wb_clk`, `wb_resetn` | Wishbone | the `s_wb_*` bus |
| `aclk`, `aresetn` | FUB | the `cmd_*` / `rsp_*` queues |
| `wb_busy` (output) | Wishbone | high while this block has anything in flight on the Wishbone side. Built from `wb_clk` signals ONLY, so a clock gate in that domain can use it directly; `wb4_slave_cdc_cg` is its one consumer |

## Functional Description

### Clock Domains

The slave itself, its skid buffers, the `STALL` logic and the registered
terminations are all in `wb_clk`. `MAX_OUTSTANDING` bounds the requests
accepted while responses are pending, so the response FIFO can never
overflow the slave's response queue whatever the clock ratio.

### CDC Structure

```
 s_wb_* (wb_clk) --> wb4_slave --> cmd FIFO (wb_clk -> aclk) --> cmd_* (aclk)
                              <-- rsp FIFO (aclk -> wb_clk) <-- rsp_* (aclk)
```

Each FIFO is a `gaxi_fifo_async` with two-flop pointer synchronisers
(`N_FLOP_CROSS = 2`). Throughput is one transfer per clock of the slower
side once the pointers have crossed; latency is a few clocks of each
domain per direction.

### Reset Behavior

Each FIFO resets its own side's pointers from that side's reset. While a
reset is asserted the resetting side is self-consistent, but a
**one-sided reset with transfers in the FIFOs is not safe**: a write-side
reset alone lets the read side see phantom occupancy (it fabricates
entries), and a read-side reset alone replays consumed entries. Quiesce
the bus before resetting one side. The full analysis is in
[apb4_slave_cdc](../apb4/apb4_slave_cdc.md), Reset Behavior, and applies
here unchanged.

## Related Modules

- [wb4_slave](wb4_slave.md), [wb4_slave_cg](wb4_slave_cg.md)
- [gaxi_fifo_async](../../rtl-cdc/gaxi_fifo_async.md) — the crossing

## Testing

`val/amba/test_wb4_slave_cdc.py` runs the `wb4_slave` phases with the
Wishbone BFMs on `wb_clk` and the queue BFMs on `aclk` at several clock
ratios in both directions (bus faster, bus slower). Formal:
`formal/amba/wb4_slave_cdc/`, single-clock model (both domains on one
clock) for the port-level contract, as the APB CDC harness does.

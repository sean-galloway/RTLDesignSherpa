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

# By-ID Response Routing

## Overview

A slave adapter that has to route by ID reads the issuing master straight
off the response's ID. This covers an AXI3/AXI4/AXI5 slave of a bridge
with more than one master, or any slave with `enable_ooo = true`
(`SlaveAdapterGenerator.track_by_id`). Inside the fabric every ID is
`{BRIDGE_ID, id}` (bridge TASK-005), and an AXI slave returns the ID it
was given, so the top `BRIDGE_ID_WIDTH` bits of BID / RID are the master
index. No table is kept to route a response. Each direction has one
counter, which bounds the transactions in flight. Single-master bridges,
protocol-shim slaves and the internal subtractive slave use an in-order
FIFO instead (see [ID Tracking](02_id_tracking.md)).

> Until 2026-10-18 these adapters looked the returning ID up in a per-ID
> CAM (`bridge_cam`, `u_wr_cam` / `u_rd_cam`) to recover the master index
> the ID already carries. That lookup sat in series with the crossbar's
> response arbitration and was the fabric's critical path on the Artix-7
> (bridge W12; HAS 5.1). `bridge_cam.sv`, its unit test and its formal
> proof are in the bridge's `deprecated/` directory, out of every
> regression; no generated bridge instantiates it.

## Functional Description

### Routing

```systemverilog
// <slave>_adapter.sv, bridge_2x2_rw (ID_WIDTH 5, BRIDGE_ID_WIDTH 1)
assign bid_bridge_id = xbar_ddr_axi_bid[ID_WIDTH-1 -: BRIDGE_ID_WIDTH];
assign bid_valid     = 1'b1;
assign rid_bridge_id = xbar_ddr_axi_rid[ID_WIDTH-1 -: BRIDGE_ID_WIDTH];
assign rid_valid     = 1'b1;
```

The crossbar steers the B / R beat by that index, as it did by the CAM's
returned index before. The slave may complete different IDs in any order,
and one master may have the same ID outstanding several times: AXI
requires the slave to return same-ID responses in order, and each of them
carries the same master index.

The prefix is always there. The config validator rejects an AXI3/AXI4/AXI5
slave whose `id_width` is narrower than `XBAR_ID_WIDTH`, so no slave can
drop the master index. A slave that returned an ID it was never sent would
be routed to whichever master its top bits name. Under the CAM, that beat
went nowhere and its handshake hung, so neither form recovers from a
non-compliant slave.

### Outstanding Limit

```systemverilog
logic [4:0] wr_out_cnt;  // in flight, 0..16 (max_outstanding)
wr_out_cnt <= wr_out_cnt + 5'(xbar_ddr_axi_awvalid && xbar_ddr_axi_awready)
                         - 5'(xbar_ddr_axi_bvalid  && xbar_ddr_axi_bready);
assign wr_trk_full = (wr_out_cnt == 5'(16));
assign xbar_ddr_axi_awready = w_sub_awready && !wr_trk_full;
```

The read counter counts AR handshakes up and the R beat with RLAST down.
Each counter is `max_outstanding` (default 16, power of two 2..64, bridge
GitHub #119 L5). When full, it holds the adapter's AWREADY / ARREADY
toward the crossbar low (bridge BUG-009, was BRIDGE-011). The address
phase waits for a B or a last R. Nothing is dropped and no error response
is generated. The full flag compares the registered count, so it is never
in series with the crossbar's grant.

### Read-Return Atomics

An AXI5 slave that takes read-return atomics answers them on R with the
AW's ID. That ID carries the master index like any other, so the beat
routes by ID too. The atomic return tracker (`u_atom_rd`) stays only to
keep those beats out of the read counter, since they were counted on AW
and not on AR.

### What It Cost Before

Measured out of context on the Artix-7 -1 at 10 ns (2026-10-18), at
`max_outstanding` 16:

| Bridge | Per-ID CAM: WNS | LUTs | By ID: WNS | LUTs |
|---|---:|---:|---:|---:|
| `bridge_2x2_axi3_slaves` | -1.006 ns | 10,636 | +0.001 ns | 8,824 |
| `bridge_mix_e` | -2.686 ns | 17,158 | -0.669 ns | 15,055 |

: Slave-adapter response routing, CAM against ID bits

Halving the CAM to 8 entries recovered 0.8-0.9 ns and still missed on
both. The paths that then remained in `bridge_mix_e` were in the AXI3
slave converter and the APB slave's arbiter; with those fixed (HAS 5.1, W13
and W14) it meets 10 ns at +0.174 ns.

## Related Modules

- [ID Tracking](02_id_tracking.md) - which slaves route by ID and which use the in-order FIFO
- [Response Routing](../ch02_blocks/08_response_routing.md) - how the crossbar uses the returned master index

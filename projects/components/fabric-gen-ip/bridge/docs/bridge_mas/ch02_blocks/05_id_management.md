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

# 2.5 ID Management

ID Management is how the bridge remembers which master sent each outstanding transaction, so the response can find its way back.

## Overview

Before anything else in this chapter, read this — it colors everything below:

> **What the generated bridge actually does** (measured against
> `rtl/generated/`). Two mechanisms, both in Figure 2.5:
>
> * **The ID is widened.** The master adapter sends `{BRIDGE_ID, id}` into the
>   fabric (bridge TASK-005), so IDs are unique across masters: in
>   `bridge_2x2_rw`, `cpu_m_axi_awid` is 4 bits and `ddr_s_axi_awid` is 5. The
>   response muxes return the low bits to the master.
> * **Each slave adapter names the originating master.** An AXI3 / AXI4 /
>   AXI5 slave of a multi-master bridge (or any slave with `enable_ooo`)
>   routes by ID. The master index is the top `BRIDGE_ID_WIDTH` bits of the
>   returned BID / RID, so the slave may complete different IDs in any
>   order. A single-master bridge, the protocol shims and the catch-all
>   instead store the granted master's index (`xbar_bridge_id_aw` / `_ar`) in
>   an in-order `bridge_id` FIFO. That requires the slave to answer in
>   request order, and bridge BUG-008's simulation-only check flags a
>   violation.
>
> Either tracker holds `max_outstanding` (default 16), and the address
> handshake is gated on it being not full (bridge BUG-009).
>
> Until 2026-10-18 the by-ID slaves looked the ID up in a per-ID CAM
> (`bridge_cam`) for the master index it already carries; that lookup was
> the fabric's critical path (bridge W12, MAS 4.1).

The ID management system does four things:

1. **Transaction Tracking**: each slave adapter records which master issued each outstanding request
2. **Response Routing**: the crossbar steers B / R by the recorded master index (`bid_bridge_id` / `rid_bridge_id`)
3. **Out-of-Order Support**: a by-ID slave may return different IDs in any order
4. **ID Space Isolation**: the `{BRIDGE_ID, id}` prefix keeps two masters' IDs distinct at every slave

### Figure 2.5: ID Management Architecture

![ID Management Architecture](../assets/graphviz/id_management.png)

The request takes the center column, widened to `{BRIDGE_ID, id}` in the master adapter and granted with its `bridge_id` in the crossbar. The response climbs the right side: the slave adapter's tracker (the ID's prefix bits or the FIFO head, dashed because each slave builds exactly one) names the master, and the crossbar and master adapter return B / R with the master's own id bits.

## Parameters

There is no `[bridge.id_management]` table and no `enable_cam`, `cam_type`
or `cam_depth` key; `config_validator` rejects unknown keys. What decides
ID handling:

```toml
[[bridge.masters]]
name = "cpu"
id_width = 4                    # master-side ID width

[[bridge.slaves]]
name = "ddr"
id_width = 5                    # must be >= widest master id_width + $clog2(num_masters)
enable_ooo = false              # true forces by-ID routing on this slave even with one master
```

Derived, not configured (emitted into `<bridge>_pkg.sv`):

| Constant | Value | `bridge_2x2_rw` |
|---|---|---|
| `BRIDGE_ID_WIDTH` | `$clog2(NUM_MASTERS)`, minimum 1 | 1 |
| `MASTER_ID_WIDTH` | widest master `id_width` | 4 |
| `ID_PREFIX_WIDTH` | `$clog2(NUM_MASTERS)`, 0 for one master | 1 |
| `XBAR_ID_WIDTH` | `MASTER_ID_WIDTH + ID_PREFIX_WIDTH` | 5 |

: Parameters

The tracker choice is fixed by the generator (`SlaveAdapterGenerator.track_by_id`):
by ID when the slave sets `enable_ooo`, or when the bridge has more than one
master and the slave is a real `axi3` / `axi4` / `axi5` port; an in-order
FIFO otherwise (single master, apb/axil/wb shim slaves, the internal
subtractive slave).

## Functional Description

### Bridge ID Concept

**Problem** -- two masters may use the same AXI ID:

```
Master 0: ARID = 4'h5
Master 1: ARID = 4'h5
A slave returning RID = 4'h5 cannot say which master it answers.
```

**Solution (built)** -- the master adapter prepends its index:

```
fabric ID = {BRIDGE_ID, master ID}

Master 0, ARID = 4'h5 -> 5'b0_0101
Master 1, ARID = 4'h5 -> 5'b1_0101     (bridge_2x2_rw)
```

### ID Width Calculation

```
ID_PREFIX_WIDTH = $clog2(NUM_MASTERS)   (0 for a single master)

2 masters:  1 bit      3-4 masters: 2 bits
5-8 masters: 3 bits    9-16 masters: 4 bits

4 masters, 4-bit master IDs: slave ports see 6-bit IDs, masters see 4.
```

### Multi-Master OR-Merge Gating

Every slave-side address, ID and `bridge_id` field is an OR of per-master
terms, each gated by that master's AW / AR arbiter grant for the slave, so
an idle master with a stale address contributes nothing:

```systemverilog
// bridge_2x2_rw_xbar.sv
assign ddr_axi_bridge_id_aw = (cpu_32b_aw_gnt_ddr ? cpu_bridge_id_aw : '0) |
                              (dma_32b_aw_gnt_ddr ? dma_bridge_id_aw : '0);
```

The grant already implies the master is valid and decoded to this slave.
An ungated OR let an idle master's zero `bridge_id` corrupt the routing
tag and send a B to the wrong master.

### ID Injection (Request Path, built)

```systemverilog
// <master>_adapter.sv
assign xbar_axi_awid = {BRIDGE_ID_WIDTH'(BRIDGE_ID), MASTER_ID_WIDTH'(fub_axi_awid)};
assign xbar_axi_arid = {BRIDGE_ID_WIDTH'(BRIDGE_ID), MASTER_ID_WIDTH'(fub_axi_arid)};
```

`BRIDGE_ID` is the per-instance master index. The concatenation is wiring
and adds no cycle. There is no "registered injection" option. A
single-master bridge prepends nothing.

### ID Stripping and Response Routing (built)

The response is NOT routed by decoding the prefix bits of BID / RID. The
slave adapter returns the originating master's index on a sideband
(`bid_bridge_id` / `rid_bridge_id`, with `bid_valid` / `rid_valid`), and
the crossbar's B / R muxes select on it:

```systemverilog
// bridge_2x2_rw_xbar.sv (B toward cpu, master index 0)
((ddr_axi_bid_bridge_id == 0) && ddr_axi_bid_valid ? ddr_axi_bid : '0) | ...
```

The master adapter then returns the low `MASTER_ID_WIDTH` bits
(`fub_axi_bid = cpu_32b_b.id[3:0]`), so the master sees its own ID.

### By-ID Routing (built)

Each by-ID slave adapter reads the master index off the response's ID and
bounds its transactions in flight with one counter per direction:

```
Route:    bid_bridge_id = BID[ID_WIDTH-1 -: BRIDGE_ID_WIDTH]
          rid_bridge_id = RID[ID_WIDTH-1 -: BRIDGE_ID_WIDTH]
          (bid_valid / rid_valid are tied high)
Count:    wr_out_cnt up on the AW handshake, down on B;
          rd_out_cnt up on AR, down on the R beat with RLAST
Full:     a counter at max_outstanding gates the crossbar-side AWREADY /
          ARREADY (bridge BUG-009); it compares the registered count
```

Nothing is stored per transaction. Two masters' same ID differ in the
prefix, and one master's repeated ID comes back in order (the slave's AXI
obligation) and to the same master. Details and the measurement that
retired the CAM: [By-ID Response Routing](../ch04_id_management/01_cam_architecture.md).

### In-Order FIFO Tracker (built)

Slaves that do not route by ID keep a `max_outstanding`-entry (default 16) FIFO of `bridge_id`,
pushed on the address handshake and popped on B / RLAST. Routing uses the
FIFO head, so such a slave must complete in request order; a
simulation-only check flags a returned ID that does not match the head
(bridge BUG-008). The same not-full gate applies.

### Outstanding Transaction Limits

The limit per slave is the tracker depth: `max_outstanding` writes and
`max_outstanding` reads (default 16 each) outstanding at each slave adapter,
counter or FIFO. When the tracker is full
the slave's AWREADY / ARREADY toward the crossbar drops until a response
frees an entry. There is no per-master outstanding limit key.

## Timing

- **ID injection / stripping**: 0 cycles (concatenation and bit-select).
- **By-ID route**: 0 added cycles and no logic (a bit-select of the ID).
- **Outstanding counter**: 0 added cycles; a slot frees in the cycle after
  the response handshake.
- **FIFO head**: 0 added cycles.

The measured end-to-end latency (2 cycles each way in `bridge_2x2_rw`,
HAS Table 5.7) includes whichever tracker the slave uses.

## Design Notes

### Resource Utilization

The per-master prefix, and the by-ID routing that reads it back, are
wiring. A by-ID slave adapter adds two counters of `$clog2(max_outstanding)+1`
bits; the FIFO tracker is two 16-entry FIFOs of `BRIDGE_ID_WIDTH` bits.
Measured totals for the fixtures are in HAS 5.3.

### Debug and Observability

```
Request:  fub_axi_awid / arid  vs  xbar_axi_awid / arid (prefix added)
Slave:    xbar_bridge_id_aw / _ar at the address handshake
By ID:    wr_out_cnt / rd_out_cnt, wr_trk_full / rd_trk_full
Response: bid_bridge_id / rid_bridge_id with bid_valid / rid_valid
```

### Common Issues

**Response goes to the wrong master**
- FIFO-tracked slave completing out of order (look for the BUG-008 check message)
- Slave truncating the ID: its `id_width` must be at least `XBAR_ID_WIDTH`
  (the validator enforces this for axi3/axi4/axi5 slaves)

**Address channel stalls**
- Tracker full: 16 outstanding at that slave with no B / RLAST returning
- A hung slave stalls its path indefinitely; there is no timeout in the bridge

**Response at a master that never issued it**
- The slave returned an ID it was never sent; by-ID routing follows its prefix bits

## Related Modules

- Section 2.1: Master Adapter (prefix injection and stripping)
- Section 2.3: Crossbar Core (grant-gated OR-merge, B / R muxes)
- Section 2.8: Response Routing
- HAS ch04_interfaces/01_axi4_interface.md (port ID widths)

## Testing

1. **Multi-master ID isolation**: two masters issue the same ID to one
   slave; each response returns to its own master with the original ID.
2. **Out-of-order at a by-ID slave**: the slave answers IDs out of request
   order; each response still reaches its master (the mix_b / mix_d
   arbitration tests exercise this).
3. **Tracker capacity**: 16 outstanding at one slave holds off the 17th
   address until a response frees an entry (bridge BUG-009 tests).
4. **Timeout**: not testable -- there is no timeout in the bridge. The
   system-level answer is a watchdog outside it.

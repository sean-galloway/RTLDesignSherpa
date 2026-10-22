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

# 2.1 Master Adapter

## Overview

Every master port in the bridge gets its own Master Adapter. The adapter sits between the master and the crossbar core, and it exists to make the crossbar's life simple: timing is isolated at the boundary, channels are specialized to what the master actually uses, and every transaction carries a Bridge ID before it enters the fabric.

### Purpose and Function

Concretely, the adapter does five things:

1. **Timing Isolation**: Inserts pipeline registers (skid buffers) to break combinatorial paths from master to crossbar
2. **Channel Specialization**: Separates read-only, write-only, and read-write masters for optimal resource utilization
3. **Fabric ID**: Widens the AXI ID to `{BRIDGE_ID, id}` so IDs are unique across masters
4. **Address Decode and Width Paths**: Selects the target slave and converts width on paths that need it (`axi4_dwidth_converter_wr` / `_rd`)
5. **Per-ID Target Gate and Response Steering**: lets a master keep requests in flight at several slaves (same-ID requests stay on one slave), and arbitrates B / R across its width paths

### Figure 2.1: Master Adapter Architecture

![Master Adapter Architecture](../assets/graphviz/master_adapter.png)

The figure follows the generated `<master>_adapter`: skid buffers at the port, the combinational address decode, the per-ID target gate that also widens the ID to `{BRIDGE_ID, id}`, and one width path per distinct slave width. W follows its AW through the `w_trk` FIFO, and B / R climb back through a response mux whose path arbiter picks among the width paths.

## Parameters

Everything here comes straight out of the TOML/CSV configuration — the generator does the arithmetic, you just declare the ports.

### Per-Master Parameters (from TOML/CSV)

```toml
[[bridge.masters]]
name = "cpu"
channels = "rw"              # "rd", "wr", or "rw"
arid_width = 4               # External ID width
awid_width = 4               # Can differ from ARID
addr_width = 32              # Address bus width
data_width = 64              # Data bus width
# pipeline_depth: NOT A KEY. Skid depth is set per channel by the generator;
# the contract is 2..8 inclusive, so 1 is rejected.
```

### Global Parameters (affect all adapters)

```toml
[bridge]
# internal_data_width: NOT A KEY -- there is no fixed internal crossbar width.
# Width conversion and the ID prefix width are derived, not configured:
# converters are emitted wherever a master and slave width differ, and
# ID_PREFIX_WIDTH = $clog2(num_masters) lands in <bridge>_pkg.sv.
```

## Ports

Two interfaces per adapter: one facing the master, one facing the fabric. Note the ID widths change across that boundary — wider on the inside.

### External Master Interface (per master)
```
Input Channels (from master):
- ARVALID, ARREADY, ARADDR, ARBURST, ARCACHE, ARID, ARLEN, 
  ARLOCK, ARPROT, ARQOS, ARSIZE

- AWVALID, AWREADY, AWADDR, AWBURST, AWCACHE, AWID, AWLEN,
  AWLOCK, AWPROT, AWQOS, AWSIZE

- WVALID, WREADY, WDATA, WSTRB, WLAST

Output Channels (to master):
- RVALID, RREADY, RDATA, RID, RLAST, RRESP

- BVALID, BREADY, BID, BRESP
```

### Internal Crossbar Interface (per master)
```
Output Channels (to crossbar):
- AR* signals + Internal ARID (wider)
- AW* signals + Internal AWID (wider)  
- W* signals (unchanged)

Input Channels (from crossbar):
- R* signals + Internal RID (wider)
- B* signals + Internal BID (wider)
```

## Functional Description

### Channel Specialization

The Bridge generator emits one adapter per master, named after the port: `<name>_adapter.sv` in the bridge's `rtl/generated/<bridge>/` directory (for example `cpu_adapter.sv` in `bridge_2x2_rw`, `cpu_rd_adapter.sv` in `bridge_1x2_rd`, where the port itself is called `cpu_rd`). There is no separate file per channel type; the `channels` key decides which channel logic the one module contains:

#### Read-Only Masters
**Channels**: AR (Address Read), R (Read Data)

```
Configuration: channels = "rd"
RTL Generated: <name>_adapter.sv  (module <name>_adapter)

Optimizations:
- No write address channel logic
- No write data channel logic
- No write response channel logic
- Reduced arbitration participation (read path only)
```

#### Write-Only Masters
**Channels**: AW (Address Write), W (Write Data), B (Write Response)

```
Configuration: channels = "wr"
RTL Generated: <name>_adapter.sv  (module <name>_adapter)

Optimizations:
- No read address channel logic
- No read data channel logic
- Reduced arbitration participation (write path only)
```

#### Read-Write Masters
**Channels**: AR, R, AW, W, B (Full AXI4 interface)

```
Configuration: channels = "rw"
RTL Generated: <name>_adapter.sv  (module <name>_adapter)

Full Functionality:
- All five AXI4 channels implemented
- Participates in both read and write arbitration
- Maximum flexibility but larger resource footprint
```

### Per-Port Monitor Wrappers (when `use_monitor = true`)

When the bridge TOML configuration sets `use_monitor = true` for a master port, the generator instantiates per-direction monitor wrappers immediately downstream of the master adapter:

- **`axi4_master_rd_mon`**: Wraps the AR/R channels, emits packets with `UNIT_ID=1`
- **`axi4_master_wr_mon`**: Wraps the AW/W/B channels, emits packets with `UNIT_ID=1`

Each wrapper:
- Samples all channel signals and timestamp at handshake points
- Emits 128-bit monitor packets on internal monbus
- Passes signals through transparently in the common case, but it CAN stall:
  `axi4_master_rd_mon` gates the address channel on the monitor's back-pressure,
  `assign w_gated_arvalid = fub_axi_arvalid & (w_block_ready | ~cfg_monitor_enable);`
  so a saturated transaction table holds off new addresses until it drains.
  With `cfg_monitor_enable` low the gate is bypassed and the path really is
  transparent.
- Is instantiated only when requested (generator-time configuration)

The generated per-port monbus streams are later aggregated by a tree of `monbus_arbiter` instances at the bridge top.

### Skid Buffer Architecture

Each AXI4 channel passes through a skid buffer for timing isolation. The skid buffer implements:

#### Registered Forward Path
```systemverilog
// Simplified skid buffer concept
always_ff @(posedge clk) begin
    if (!rst_n) begin
        valid_reg <= 1'b0;
    end else if (!valid_reg || ready_out) begin
        valid_reg <= valid_in;
        data_reg  <= data_in;
    end
end
```

#### Single-Cycle Backpressure Response
- When downstream is not ready, accepts one additional beat into holding register
- Signals ready_in = 0 in same cycle to upstream
- No combinatorial paths between upstream and downstream

#### Pipeline Depth
- Default: AW 2, W 4, B 2, AR 2, R 2; `[bridge.defaults.skid_depths]` and the
  port's `interface.skid_depths` override them (they were parsed and ignored
  until GitHub #119 L7).
- Range: **2..8 inclusive, any integer**, or **0** where the port's
  `latency` mode cuts the stage (`cut_ax`: W/B/R; `cut_none`: all five).
  `gaxi_skid_buffer` builds DEPTH 0 as a combinational pass-through; its
  elaboration guard rejects 1 and anything above 8.
- Trade-off: Latency vs. timing closure

**Performance Impact**:
- Adds 1 cycle latency per channel
- Enables higher clock frequencies
- Prevents critical paths through crossbar

### Bridge ID Management

Inside the fabric every transaction ID is `{BRIDGE_ID, local id}`.
`BRIDGE_ID` is the master's index, so two masters can never alias an ID at a
slave (bridge TASK-005); it is prepended only when there is more than one
master. The local id is what the master adapter makes of the master's own
ID:

- **A remap slot**, when the master's ID is wider than `$clog2(max_outstanding)`
  bits (bridge TASK-018). A master has at most `max_outstanding` requests in
  flight per direction, so at most that many distinct IDs, and a slot that
  wide names each of them. A `bridge_id_remap` table per direction hands the
  slots out (below).
- **The master's ID itself**, when it is no wider than a slot. Remapping would
  not narrow it, so the adapter keeps it and tracks it in the per-ID target
  table instead. A read-return-atomic port (rw AXI5 with `atomic`) also keeps
  its own ID: its atomic AW answers on both B and R under one AWID, which
  one table per direction cannot name.

The generated assignment in `cpu_adapter.sv` (`bridge_2x2_rw`: two 8-bit
masters, 16 outstanding) is:

```systemverilog
assign xbar_axi_awid = {BRIDGE_ID_WIDTH'(BRIDGE_ID), MASTER_ID_WIDTH'(aw_rmp_slot)};
assign xbar_axi_arid = {BRIDGE_ID_WIDTH'(BRIDGE_ID), MASTER_ID_WIDTH'(ar_rmp_slot)};
```

A kept ID uses `fub_axi_awid` / `fub_axi_arid` in place of the slot. The
widths come from `<bridge>_pkg.sv`, which takes them from
`width_utils.xbar_id_width`:

| Package constant | Meaning | `bridge_2x2_rw` |
|---|---|---|
| `MASTER_ID_WIDTH` | widest master-local ID: slot or kept ID | 4 |
| `ID_PREFIX_WIDTH` | master-index bits prepended, `$clog2(NUM_MASTERS)` | 1 |
| `XBAR_ID_WIDTH` | fabric and slave-port ID width | 5 |

: Bridge ID Management

A slave's declared `id_width` must be at least `XBAR_ID_WIDTH`, or the config
validator rejects the bridge.

#### ID Width Examples

```
XBAR_ID_WIDTH = $clog2(num_masters) + max over masters of
                ( $clog2(max_outstanding)   if id_width > $clog2(max_outstanding)
                  id_width                  otherwise )

- 2 masters, 8-bit IDs, 16 outstanding -> 1 + 4 = 5 bits
- 5 masters, 8-bit IDs, 16 outstanding -> 3 + 4 = 7 bits (was 3 + 8 = 11)
- 2 masters, 4-bit IDs, 16 outstanding -> 1 + 4 = 5 bits (IDs kept)
- 1 master,  8-bit ID,  64 outstanding -> 0 + 6 = 6 bits
```

The width matters beyond the slave ports: every per-ID structure downstream
of the adapter is sized by it. The width converters keep read state per
fabric ID, and at 11 bits that was 2048 entries per converter.

#### ID Remap (bridge_id_remap)

`projects/components/fabric-gen-ip/bridge/rtl/bridge_id_remap.sv`, one per
direction (`u_aw_id_remap`, `u_ar_id_remap`), `max_outstanding` entries. Each
entry holds an original ID, its target slave (one-hot), a metadata bit, and a
count of its requests in flight.

- **Request.** The request's ID is compared with every live entry. A hit
  reuses that entry's slot, so requests of one ID keep one fabric ID and stay
  ordered at the slave; a miss takes the lowest free slot. The slot drives
  the local part of `xbar_axi_awid` / `xbar_axi_arid`, and the handshake
  counts the entry up.
- **Gate.** The table's `req_ok` is `aw_id_ok` / `ar_id_ok`: an ID that is
  live toward one slave may only add requests to that slave, and on a
  trace-echo port only with the same trace bit (the metadata). Its `full`,
  set at `max_outstanding` in flight, is `aw_trk_full` / `ar_trk_full`.
  Because a live entry always has a request in flight, a table that is not
  full always has a free slot.
- **Response.** The B / R mux selects the returned ID's low slot bits into
  `b_rmp_slot` / `r_rmp_slot` instead of into the fub ID. The table reads the
  entry at that slot and drives `fub_axi_bid` / `fub_axi_rid` with the
  original ID, and on trace-echo ports `b_trk_trace` / `r_trk_trace` with its
  trace. A B, or an R with RLAST, counts the entry down a cycle after its
  handshake, and the entry frees at zero. The pop is registered because
  decoding the returned slot into a count on the same cycle, behind the path
  arbiter, was the adapter's slowest path (-0.445 ns on `bridge_5x3_channels`
  at 100 MHz on the Artix-7). Counting late only holds an entry, and a full
  table, one cycle longer.

The request lookup is a `max_outstanding`-way compare against registered
entries. The response restore is a `max_outstanding`:1 read after the path
arbiter, ahead of the wrapper's B / R skid buffer. The table is proven in
`formal/bridge/bridge_id_remap` (unbounded, suprove), and
`test_bridge_2x2_rw_id_remap` drives three times as many IDs as slots through
both masters and checks the mapping at all four ports.

#### ID Restore (Response Path)

On a remapped port the table restores the ID, as above. On a port that
keeps its ID, the adapter returns the low `MASTER_ID_WIDTH` bits of BID / RID
to the master, and the master sees its original ID.

Routing a response back to the right master does not decode those bits.
Each slave adapter also receives the originating master's index as a
sideband (`xbar_bridge_id_aw` / `_ar`) and returns it as `bid_bridge_id` /
`rid_bridge_id`; the crossbar steers B / R by it. For an AXI3/AXI4/AXI5
slave of a multi-master bridge that is the returned BID/RID's prefix bits,
with nothing stored; single-master bridges and shim/subtractive slaves use
an in-order FIFO. See Section 2.5 and ch04.

### Protocol Normalization

The Master Adapter enforces several protocol requirements:

#### Valid Address Ranges
- Checks addresses against slave address maps
- Flags out-of-range accesses for error handling
- Prevents deadlocks from illegal addresses

#### Burst Constraints
- Validates ARLEN/AWLEN vs. 4KB boundary rules
- Ensures burst types are supported (FIXED, INCR, WRAP)
- Checks SIZE vs. DATA_WIDTH compatibility

#### Signal Defaults
- Provides default values for unused signals
- Ensures ARCACHE/AWCACHE have legal values
- Sets ARPROT/AWPROT based on configuration

### Response Path Slave Selection Tracking

#### Problem: Stale Slave Select Decode

Here's the part that bites people. The master adapter decodes the incoming address combinationally to pick a target slave. When the wrapper's skid buffer pops and `fub_axi_awaddr`/`fub_axi_araddr` reverts, the decode changes even though the converter is still in flight pushing the request to the crossbar. This causes the response MUX to route read/write responses from the wrong slave.

#### Solution: Capture at the Handshake, Steer by What Returns

The decode is captured when the request is accepted, never re-read later.
The W path keeps a FIFO of it (`w_trk_*`, pushed at AW, popped at WLAST),
because W carries no ID and follows AW order. B and R are no longer steered
by a FIFO of targets at all: they are taken in the order the width paths
offer them (path arbiter below), and what the adapter keeps per request is
indexed by ID. Until 2026-10-15 an AW/AR -> B/R FIFO of targets steered the
response mux, which is why a master could hold only one target at a time;
read-return-atomic and trace-echo ports kept that FIFO a little longer
(GitHub #119 L1b), because their per-request state rode its entries.

### Several Targets in Flight (limitation fixed: GitHub #119 L1, L1b)

A master used to be held to one target slave at a time, because B / R were
replayed in issue order from the tracking FIFO. Now the adapter keeps only
the ordering AXI requires:

- **Per-ID state**: on a remapped port the ID remap table above, one entry
  per slot, matched by the whole ID. On a port that keeps its ID, the per-ID
  target table (`aw_idt_cnt[]` / `aw_idt_tgt[]`, same for AR):
  `2**id_track_bits` entries (TOML `[bridge].id_track_bits`, default 4, and
  never more bits than the port's ID), indexed by the ID's low bits. Each entry
  holds an in-flight count and that ID's target slave. The address handshake
  increments the count; a B, or an R with RLAST, decrements it by the returned
  ID. IDs that share the index bits are treated as one ID: safe, at worst a
  needless stall.
- **Gates**: `ar_gate_ok = ar_id_ok && !ar_trk_full`, and
  `aw_gate_ok = aw_id_ok && !aw_trk_full && (w_trk empty || w_slave_select == target)`.
  Here `*_id_ok` means the ID is idle, or already in flight to the SAME
  slave. The W term exists because W has no ID and follows AW order. Two
  masters each owing W to two slaves would otherwise wait on each other at
  the slaves' W ports.
- **Outstanding limit**: `aw_out_cnt` / `ar_out_cnt` cap the port at its
  `max_outstanding` (default 16; bridge GitHub #119 L5) in
  flight (bridge BUG-009's not-full rule), so no count wraps.
- **Path arbiter**: with more than one width path, `b_pgnt` / `r_pgnt` pick a
  path round robin. A grant holds while offered and not taken, B and R
  alike, and is re-arbitrated every beat. The selection feeds `b_slave_select` / `r_slave_select`
  as a representative slave of the path, so the response mux and the path
  readies are unchanged. One width path needs no arbiter. Among the slaves
  on one path, the crossbar's response arbiter has already chosen (MAS 2.3).
- **Trace echo** (ports with AXI5 `trace`): each table entry also holds the
  in-flight ID's trace bit. A request whose ID is in flight with a DIFFERENT
  trace waits, so the bit is single-valued per ID, and B/R echo
  `aw_idt_trace[BID]` / `ar_idt_trace[RID]` -- also for a slave that has no
  trace of its own. On a remapped port the trace bit is the remap entry's
  metadata, read at the returned slot.
- **Read-return atomics** (rw AXI5 ports with `atomic`): an atomic AW is also
  counted in the AR table under its AWID (`ar_idt_push_aw`), since its R comes
  back with that ID. Its gate `aw_rr_gate_ok` is the AR per-ID rule plus a
  free AR slot, and it yields to an AR pushing the same ID index in the same
  cycle. An atomic that decodes to the subtractive slave queues its ID in a
  local-DECERR FIFO (`lr_*`), which the R path arbiter grants like one more
  path (`r_local_head`). These two were the last ports on the one-target FIFO
  (GitHub #119 L1b, 2026-10-15).

## Timing

### Latency

**Request Path** (Master → Crossbar): 1 cycle -- one registered skid stage.

**Response Path** (Crossbar → Master): 1 cycle -- one registered skid stage.

**Total**: 2 cycles each way through the bridge (one skid in the master
adapter, one in the slave adapter). Measured, not derived: see HAS Table 5.7
and `test_bridge_2x2_rw_latency`, which asserts 2 exactly.

> **Depth is not latency.** This block read "with 4-stage pipeline: 4 cycles"
> and a round trip of "2-8 cycles depending on pipeline depth". A
> `gaxi_skid_buffer` presents its output one cycle after the write regardless
> of DEPTH; the depth sets how many beats it can ABSORB under backpressure,
> not how long a beat takes to cross it. The ID prefix and strip are pure
> wiring (a concatenation and a bit-select) and add no cycles.

### Throughput

- **Maximum**: 1 transaction per cycle per channel (fully pipelined)
- **Backpressure**: Propagates with 1-cycle latency
- **Burst Performance**: No degradation; bursts flow continuously when ready

### Critical Paths

Typical critical paths (if skid buffers not used):
- Master ARVALID → Crossbar arbitration logic
- Crossbar grant → Master ARREADY
- Slave RDATA → Master RDATA

**Solution**: Skid buffers break all these paths at the cost of 1-cycle latency.

## Design Notes

### Resource Utilization

#### Per-Master Adapter Resources (Typical)

**Read-Write Master (64-bit data, 32-bit addr, 4-bit ID)**:
```
Logic Elements:  ~200-400 (depending on ID width and features)
Registers:       ~150-250 (pipeline stages + control)
Block RAM:       0

Breakdown:
- Skid buffers (5 channels × ~30 regs each): ~150 regs
- ID manipulation logic: ~50 LEs
- Control FSMs: ~100 LEs
- Routing logic: ~50 LEs
```

**Read-Only Master**: ~60% of read-write resources  
**Write-Only Master**: ~65% of read-write resources

#### Scaling Considerations

Resource usage scales with:
- Number of masters (linear scaling, one adapter per master)
- ID width (logarithmic: +BID_WIDTH bits per transaction)
- Pipeline depth (linear: deeper pipelines = more registers)
- Data width (linear: wider data = wider skid buffers)

### Future Enhancements

#### Planned Features
- **Dynamic Pipeline Depth**: Adjust depth based on operating frequency
- **FIFO Mode**: Deeper buffering (16-256 entries) for burst-intensive masters
- **QoS Support**: Priority-based arbitration hints
- **Performance Counters**: Transaction counts, stall cycles, utilization metrics

#### Under Consideration
- **Clock Domain Crossing**: Per-master clock domains with async FIFOs
- **Width Conversion at Adapter**: Move width logic to adapters for distributed conversion
- **Outstanding Transaction Tracking**: Windowing for improved OOO performance

## Related Modules

- Section 2.3: Crossbar Core (interconnect architecture)
- Section 2.4: Arbitration (how adapters compete for slaves)
- Section 2.5: ID Management (fabric ID widening, sideband bridge_id, by-ID / FIFO tracking)
- HAS ch04_interfaces/01_axi4_interface.md (port signals)

## Testing

### Debug and Observability

#### Recommended Debug Signals

For ILA or waveform capture:
```
- Master adapter input valid/ready (all channels)
- Master adapter output valid/ready (all channels)
- Bridge ID assignments per transaction
- Pipeline stage occupancy
- Backpressure events (ready = 0 while valid = 1)
```

#### Common Issues and Debug

**Symptom**: Master hangs waiting for READY  
**Check**: 
- Is adapter receiving grants from arbiters?
- Is slave responding to requests?
- Is response path clear?

**Symptom**: Incorrect data returned to master  
**Check**:
- Bridge ID extraction logic
- ID width mismatches
- Response routing in crossbar

**Symptom**: Timing violations  
**Check**:
- Increase pipeline_depth parameter
- Verify clock frequency vs. design complexity
- Check for combinatorial loops

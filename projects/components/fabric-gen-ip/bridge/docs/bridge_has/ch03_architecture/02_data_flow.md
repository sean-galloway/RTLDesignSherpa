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

# Data Flow

## Transaction Flow Overview

### Write Transaction Flow

1. **Master issues AW** - Address and control information
2. **Bridge decodes address** - Determines target slave
3. **Arbitration** - Grants access if multiple masters contend
4. **AW forwarded to slave** - ID unchanged; the originating master is pushed onto the slave adapter's `bridge_id` FIFO
5. **Master sends W data** - Following the granted AW
6. **W forwarded to slave** - Using same grant
7. **Slave returns B response** - with the master's own ID; the FIFO head selects the destination
8. **Bridge routes B to master** - Using ID to find originator

### Read Transaction Flow

1. **Master issues AR** - Address and control information
2. **Bridge decodes address** - Determines target slave
3. **Arbitration** - Grants access if multiple masters contend
4. **AR forwarded to slave** - ID unchanged; master recorded in the read `bridge_id` FIFO
5. **Slave returns R data** - Potentially multiple beats
6. **Bridge routes R to master** - Using ID to find originator

## Channel Independence

### AXI4 Channel Separation

Each AXI4 channel operates independently:

| Channel | Direction | Contents | Arbitration |
|---------|-----------|----------|-------------|
| AW | Master to Slave | Write address | Per-slave |
| W | Master to Slave | Write data | Follows AW grant |
| B | Slave to Master | Write response | ID-based routing |
| AR | Master to Slave | Read address | Per-slave |
| R | Slave to Master | Read data | ID-based routing |

: AXI4 Channel Summary

### Parallel Operation

- Read and write transactions can proceed simultaneously
- Different masters can access different slaves in parallel
- Same slave serializes access via arbitration

## Bridge ID and ID Widening

### Bridge ID (BID) Concept

```
Master-local ID:           [MASTER_ID_WIDTH-1:0], a remap slot or the master's ID
Bridge ID (master index):  BRIDGE_ID_WIDTH = clog2(NUM_MASTERS)
AXI ID on a slave port:    {BRIDGE_ID, local ID}, XBAR_ID_WIDTH bits
```

### IDs inside the fabric

With more than one master, each master adapter prepends its index to every
request ID (bridge TASK-005), so two masters can never alias an ID at a
slave. Below the index sits a master-local ID. For a master whose ID is
wider than `$clog2(max_outstanding)` bits, that is a remap slot (bridge
TASK-018): the adapter has at most `max_outstanding` requests in flight per
direction, so at most that many distinct IDs, and its remap table gives each
live ID a slot. A request whose ID is already live reuses its slot, so one
ID stays one fabric ID and stays ordered at the slave. In `bridge_2x2_rw`:

```systemverilog
input  logic [7:0]  cpu_m_axi_awid     // master side: 8 bits
output logic [4:0]  ddr_s_axi_awid     // slave side: {BRIDGE_ID, slot} = 5 bits
```

A master no wider than a slot keeps its own ID as the local part
(`bridge_2x2_ooo`: 4-bit masters, 5-bit slave IDs), and so does a
read-return-atomic port. The slave-side width is the widest local ID plus
`$clog2(NUM_MASTERS)` bits (`XBAR_ID_WIDTH` in `<bridge>_pkg.sv`); a slave
declared narrower is rejected by the config validator. A single-master
bridge prepends nothing. On B and R the master adapter restores the ID from
the returned slot, or strips the prefix from a kept ID, so a master always
sees its own ID.

The width is not only a pin count. Every per-ID structure past the master
adapter is sized by it: a width converter keeps read state per fabric ID,
and `bridge_5x3_channels` (five 8-bit masters) went from 11-bit IDs, 2048
entries per converter, to 7-bit, 128 entries.

## Response Routing

Each slave adapter hands the crossbar the index of the master a response
belongs to (`bid_bridge_id` / `rid_bridge_id`), and the crossbar's B and R
muxes select on that. A by-ID slave adapter reads it off the prefix bits of
the returned BID / RID. A FIFO-tracked one stores the granted master's index
(the `bridge_id` sideband) at the address handshake and returns its head.
Which form a slave gets is fixed at generation:

| Slave | Tracker | Order the slave may complete in |
|---|---|---|
| AXI3 / AXI4 / AXI5 slave, more than one master | by ID: the ID's prefix bits route, `wr_out_cnt` / `rd_out_cnt` count to `max_outstanding` (default 16) | any order across IDs |
| any slave with `enable_ooo = true` | by ID | any order across IDs |
| single-master bridge, apb / axil / wb shim slaves, internal subtractive slave | in-order `bridge_id` FIFO, `max_outstanding` deep (default 16) | request order across all IDs |

: Response Routing

```systemverilog
// by-ID form (multi-master slave)
assign bid_bridge_id = xbar_ddr_axi_bid[ID_WIDTH-1 -: BRIDGE_ID_WIDTH];
wr_out_cnt <= wr_out_cnt + (AW accepted) - (B accepted);     // up to max_outstanding
assign wr_trk_full = (wr_out_cnt == max_outstanding);

// FIFO form
wr_fifo[wr_ptr[...]] <= xbar_bridge_id_aw;      // push on AW accept
assign bid_bridge_id  = wr_fifo[rd_ptr[...]];   // route by FIFO head
```

### B Channel (Write Response)

1. Slave issues B carrying the fabric ID it was sent
2. The slave adapter reads the master index off the BID's prefix (or pops its FIFO)
3. The returned `bridge_id` selects the master
4. The master adapter strips the prefix and forwards B

### R Channel (Read Data)

1. Slave issues R carrying the fabric ID
2. The slave adapter's read tracker names the master; the count drops (or the FIFO pops) on RLAST
3. The master adapter strips the prefix

Either tracker holds `max_outstanding` transactions (default 16); when it is full the slave's
AWREADY / ARREADY toward the crossbar drops (bridge BUG-009).

### The requirement the FIFO form creates

A FIFO-tracked slave is routed by *position*, so it must return B/R in
request order across ALL IDs. Those slaves are in order by construction
(the protocol shims and the subtractive slave) or have a single master;
a simulation-only check flags a violation (bridge BUG-008, was BRIDGE-010).
A multi-master AXI3/AXI4/AXI5 slave has no such requirement: it is routed
by ID. (Until 2026-10-18 a per-ID CAM, `bridge_cam`, looked the master index
up; the ID already carries it, and the lookup was the fabric's critical path
on the Artix-7, HAS 5.1.)

## Ordering: what the fabric actually guarantees

Per-ID ordering is the slave's AXI obligation; across IDs a by-ID
slave may complete in any order. The fabric adds one structural rule:

**Per master -- per-ID targets.** A master may have transactions in flight
at several slaves at once. The master adapter keeps a small table per ID
(the remap table on a remapped port, one entry per slot; otherwise
`[bridge].id_track_bits`, default 4: 16 entries indexed by the ID's low
bits) and `aw_gate_ok`/`ar_gate_ok` hold a new address phase only when its
ID is already in flight to a DIFFERENT slave -- the AXI same-ID ordering
rule, enforced where it can be, before the request leaves. Responses from
different slaves come back in whatever order the slaves produce them: the
crossbar arbitrates among the slaves on each master width path, and the
adapter among its paths. A new AW also waits while W is still owed to a
different slave: W carries no ID and follows AW order, so two masters each
owing W to two slaves could otherwise wait on each other at the slaves' W
ports. Read-return-atomic and trace-echo ports work the same way (their
per-request state is held per ID too, MAS 2.1; GitHub #119 L1b). The rule was lifted 2026-10-15 (limitation fixed: GitHub #119 L1); before that every master held one target slave at a time.

**Per FIFO-tracked slave -- responses must come back in order.** See "The
requirement the FIFO form creates" above.

Worked example: master 0 issues a read to a slow slave 0 with ID 1, then a
read to slave 1 with ID 2. The slave 1 response returns first. With ID 2
changed to ID 1, the second read is held at the master adapter until the
first returns. `test_bridge_2x2_rw_multitarget` measures both cases.

## References

* Dally & Towles, *Principles and Practices of Interconnection Networks*, Morgan Kaufmann 2004 — per-slave arbiters as a separable allocator degenerated to one resource per channel (ch18 §19.3), and skid buffers as buffered flow control (ch12). ([Reference archive](../../../references/README.md))
* Roy, *Advanced Digital System Design*, Springer 2023 — AXI's lack of a strict timing relationship between AW and W, and the use of the stored transaction ID to correlate B back to AW (§18.2.3). ([Reference archive](../../../references/README.md))
* Duato/Yalamanchili/Lionel, *Interconnection Networks*, Morgan Kaufmann 2003 — deterministic routing preserves order only on a single path; out-of-order responses across IDs need explicit ID-keyed tables such as Bridge's CAM mode (ch3/4). ([Reference archive](../../../references/README.md))

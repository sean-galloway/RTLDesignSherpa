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
Master ID:                 [MASTER_ID_WIDTH-1:0]
Bridge ID (master index):  BRIDGE_ID_WIDTH = clog2(NUM_MASTERS)
AXI ID on a slave port:    {BRIDGE_ID, master ID}, XBAR_ID_WIDTH bits
```

### IDs are widened inside the fabric

With more than one master, each master adapter prepends its index to every
request ID (bridge TASK-005), so two masters can never alias an ID at a
slave. In `bridge_2x2_rw`:

```systemverilog
input  logic [3:0]  cpu_m_axi_awid     // master side: 4 bits
output logic [4:0]  ddr_s_axi_awid     // slave side: {BRIDGE_ID, id} = 5 bits
```

The slave-side width is the widest master's `id_width` plus
`$clog2(NUM_MASTERS)` bits (`XBAR_ID_WIDTH` in `<bridge>_pkg.sv`); a slave
declared narrower is rejected by the config validator. A single-master
bridge prepends nothing. On B and R the master adapter returns only the low
master-ID bits, so a master always sees its own ID.

## Response Routing

The prefix bits are not decoded to route a response. Each slave adapter
also receives the granted master's index as a sideband (`bridge_id`),
stores it at the address handshake, and returns it with the response
(`bid_bridge_id` / `rid_bridge_id`); the crossbar's B and R muxes select
on that. Which store a slave gets is fixed at generation:

| Slave | Tracker | Order the slave may complete in |
|---|---|---|
| AXI4 / AXI5 slave, more than one master | `bridge_cam` (`u_wr_cam` / `u_rd_cam`), tag = AXI ID, data = `bridge_id`, 16 deep | any order across IDs |
| any slave with `enable_ooo = true` | `bridge_cam` | any order across IDs |
| single-master bridge, apb / axil / wb shim slaves, internal subtractive slave | in-order `bridge_id` FIFO, 16 deep | request order across all IDs |

: Response Routing

```systemverilog
// CAM form (multi-master AXI4 slave)
bridge_cam #(.TAG_WIDTH(ID_WIDTH), .DATA_WIDTH(BRIDGE_ID_WIDTH),
             .DEPTH(16), .ALLOW_DUPLICATES(1)) u_wr_cam (
    .allocate_tag  (xbar_ddr_axi_awid),   .allocate_data  (xbar_bridge_id_aw),
    .deallocate_tag(xbar_ddr_axi_bid),    .deallocate_data(bid_bridge_id), ...);

// FIFO form
wr_fifo[wr_ptr[...]] <= xbar_bridge_id_aw;      // push on AW accept
assign bid_bridge_id  = wr_fifo[rd_ptr[...]];   // route by FIFO head
```

### B Channel (Write Response)

1. Slave issues B carrying the fabric ID it was sent
2. The slave adapter looks the BID up in its CAM (or pops its FIFO)
3. The returned `bridge_id` selects the master
4. The master adapter strips the prefix and forwards B

### R Channel (Read Data)

1. Slave issues R carrying the fabric ID
2. The slave adapter's read tracker names the master; the entry is freed on RLAST
3. The master adapter strips the prefix

Either tracker holds 16 transactions; when it is full the slave's
AWREADY / ARREADY toward the crossbar drops (bridge BUG-009).

### The requirement the FIFO form creates

A FIFO-tracked slave is routed by *position*, so it must return B/R in
request order across ALL IDs. Those slaves are in order by construction
(the protocol shims and the subtractive slave) or have a single master;
a simulation-only check flags a violation (bridge BUG-008, was BRIDGE-010).
A multi-master AXI4/AXI5 slave has no such requirement: the CAM routes by
ID.

## Ordering: what the fabric actually guarantees

Per-ID ordering is the slave's AXI obligation; across IDs a CAM-tracked
slave may complete in any order. The fabric adds one structural rule:

**Per master -- one target at a time.** A master may not have transactions
outstanding to more than one slave simultaneously. `aw_gate_ok`/`ar_gate_ok`
hold off a new address phase until every outstanding transaction targets the
same slave. This is a deadlock fix: the response mux replays in address-issue
order, slaves respond in their own order, and cross-slave outstanding
transactions from several masters can wedge the heads against each other.
Same-slave pipelining is unaffected.

**Per FIFO-tracked slave -- responses must come back in order.** See "The
requirement the FIFO form creates" above.

The sequence an earlier revision of this page offered as a worked example --
master 0 issuing to slave 0 and slave 1 concurrently, then the fast slave
answering first -- is exactly what `aw_gate_ok` prevents. It cannot occur.

## References

* Dally & Towles, *Principles and Practices of Interconnection Networks*, Morgan Kaufmann 2004 — per-slave arbiters as a separable allocator degenerated to one resource per channel (ch18 §19.3), and skid buffers as buffered flow control (ch12). ([Reference archive](../../../references/README.md))
* Roy, *Advanced Digital System Design*, Springer 2023 — AXI's lack of a strict timing relationship between AW and W, and the use of the stored transaction ID to correlate B back to AW (§18.2.3). ([Reference archive](../../../references/README.md))
* Duato/Yalamanchili/Lionel, *Interconnection Networks*, Morgan Kaufmann 2003 — deterministic routing preserves order only on a single path; out-of-order responses across IDs need explicit ID-keyed tables such as Bridge's CAM mode (ch3/4). ([Reference archive](../../../references/README.md))

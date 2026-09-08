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

: Table 3.2: AXI4 Channel Summary

### Parallel Operation

- Read and write transactions can proceed simultaneously
- Different masters can access different slaves in parallel
- Same slave serializes access via arbitration

## Bridge ID (there is no ID extension)

### Bridge ID (BID) Concept

```
Original Master ID: [ID_WIDTH-1:0]
AXI ID on the slave port: the master's original ID, unmodified
BID Width: clog2(NUM_MASTERS)
```

### IDs are pass-through, not extended

The generated RTL does **not** widen or prepend anything. A master's ID reaches
the slave unchanged, and the slave port is declared at the same width:

```systemverilog
input  logic [3:0]  cpu_axi4_awid     // master side
output logic [3:0]  ddr_s_axi_awid    // slave side -- same width
```

The generator says so itself: *"Master id_width drives the slave-port ID width
(pass-through)."*

Earlier revisions of this page described a bridge-ID-prepend scheme, with
`4'b0101` becoming `6'b00_0101` and the upper bits extracted on the response.
That design was never built. It is documented here only because the mechanism
that replaced it has a consequence worth understanding.

## Response Routing

Each slave adapter keeps an **in-order FIFO** of the originating master's
`bridge_id`: pushed on the address handshake, popped on the response.

```systemverilog
wr_fifo[wr_ptr[...]] <= xbar_bridge_id_aw;      // push on AW accept
assign bid_bridge_id  = wr_fifo[rd_ptr[...]];   // route by FIFO HEAD
```

### B Channel (Write Response)

1. Slave issues B carrying the master's own (unmodified) ID
2. The slave adapter pops its `bridge_id` FIFO
3. That FIFO entry -- **not** anything in the BID -- selects the master
4. The B beat is forwarded unchanged

### R Channel (Read Data)

1. Slave issues R carrying the master's own (unmodified) ID
2. The slave adapter's read FIFO selects the master, popped on RLAST
3. RLAST indicates the final beat

### The requirement this creates

Because routing is keyed on FIFO *position* rather than on the returned ID,
**each slave port must return B/R in request order across ALL IDs.** AXI4
permits a slave to complete different-ID transactions out of order, and a
multi-ported memory controller normally does; nothing in the fabric detects
or prevents it. Two masters with writes outstanding at one slave are enough to
expose it -- the response goes to the wrong master, carrying an ID that master
never issued. Tracked as BRIDGE-010.

## Ordering: what the fabric actually guarantees

**Out-of-order completion is not supported.** There are no ID tracking tables;
`bridge_cam.sv` exists in the tree but is instantiated in zero generated
bridges. Ordering is enforced structurally instead, in two places:

**Per master -- one target at a time.** A master may not have transactions
outstanding to more than one slave simultaneously. `aw_gate_ok`/`ar_gate_ok`
hold off a new address phase until every outstanding transaction targets the
same slave. This is a deadlock fix: the response mux replays in address-issue
order, slaves respond in their own order, and cross-slave outstanding
transactions from several masters can wedge the heads against each other.
Same-slave pipelining is unaffected.

**Per slave -- responses must come back in order.** See "The requirement this
creates" above, and BRIDGE-010.

The sequence an earlier revision of this page offered as a worked example --
master 0 issuing to slave 0 and slave 1 concurrently, then the fast slave
answering first -- is exactly what `aw_gate_ok` prevents. It cannot occur.

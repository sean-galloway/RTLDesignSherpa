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

# Read Return Ring (`scoria_rd_return_ring`)

**Module:** `scoria_rd_return_ring.sv`
**Location:** `rtl/fub/`
**Category:** in-flight read data buffer
**Parent:** `scoria_axi4_layer`
**Status:** complete and sim-verified; formal suite `formal/scoria/rd_return_ring/scoria_rd_return_ring.sby`

---

## Purpose

The read return ring decouples the read scheduling CAM from in-flight read data. It allocates a ticket in AR order when a read is admitted, accepts the ticket into an issue-order FIFO when the read issues, lands DFI return beats into the ticket's slot, and drains completed reads back to the read intake in AR order. Because the CAM entry is freed at issue, the number of reads the controller can hold in flight is bounded by this ring's depth, not by the CAM's entry count.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `DEPTH` | int | power of 2 | 32 | in-flight reads |
| `AXI_DATA_WIDTH` | int | 1+ | 64 | data width |
| `AXI_BEATS_PER_BURST` | int | 1+ | 4 | beats per DRAM burst |
| `TW` | int | derived | `$clog2(DEPTH)` | ticket width |
| `BCW` | int | derived | `$clog2(AXI_BEATS_PER_BURST)` or 1 | beat-counter width |
| `OCW` | int | derived | `$clog2(DEPTH + 1)` | occupancy-counter width |

: Table 2.10.1: Read return ring parameters

## Interface

### Allocate

| Signal | Direction | Width | Description |
|---|---|---|---|
| `alloc_valid_i` | in | 1 | allocate a ticket |
| `alloc_ready_o` | out | 1 | ring not full |
| `alloc_ticket_o` | out | `TW` | allocated ticket = current tail |

: Table 2.10.2: Ticket allocation interface

### Issue notify

| Signal | Direction | Width | Description |
|---|---|---|---|
| `issue_valid_i` | in | 1 | ticket has issued to DRAM |
| `issue_ready_o` | out | 1 | issue-order FIFO not full |
| `issue_ticket_i` | in | `TW` | ticket that issued |

: Table 2.10.3: Issue-order FIFO interface

### DFI read return

| Signal | Direction | Width | Description |
|---|---|---|---|
| `dfi_ret_valid_i` | in | 1 | DFI return beat valid |
| `dfi_ret_ready_o` | out | 1 | a ticket is at the issue-Q head |
| `dfi_ret_data_i` | in | `AXI_DATA_WIDTH` | return data |
| `dfi_ret_resp_i` | in | 2 | return response |
| `dfi_ret_last_i` | in | 1 | last beat of this burst |

: Table 2.10.4: DFI read return interface

### Drain and observability

| Signal | Direction | Width | Description |
|---|---|---|---|
| `drain_valid_o` | out | 1 | drain data valid |
| `drain_ready_i` | in | 1 | drain ready |
| `drain_data_o` | out | `AXI_DATA_WIDTH` | drain data |
| `drain_resp_o` | out | 2 | drain response |
| `drain_last_o` | out | 1 | last beat of this read |
| `occ_o` | out | `OCW` | allocated tickets (observability) |
| `busy_o` | out | 1 | ring not idle |

: Table 2.10.5: Drain and observability interface

## Microarchitecture internals

### Tickets in AR order

Allocation always claims the current tail slot. `alloc_ticket_o = r_tail`, and on a valid allocation the tail increments. The head pointer tracks the oldest allocated slot; the slot is freed when its last beat is consumed by the drain. Occupancy `r_occ` increments on allocate and decrements on free.

### Issue-order FIFO

When the scheduler issues a read, the CAM forwards the ticket to the ring's issue-order FIFO. The FIFO is sized `DEPTH`; because a ticket is pushed at most once per allocation, it can never fill before the ring itself does. DFI return beats always land in the issue-order FIFO head's slot, so `dfi_ret_ready_o = w_iq_rd_valid`. The FIFO pops when a complete burst (`dfi_ret_last_i`) has been written into the slot.

### DFI returns land in the issue-Q head slot

The BRAM data array is indexed by ticket and beat:

```text
w_ret_idx = ticket * AXI_BEATS_PER_BURST + r_ret_beat
```

The return beat is written whenever `dfi_ret_valid_i && dfi_ret_ready_o`. The slot's `ready` bit is set and its `resp` field is captured on the burst's last beat.

### 2-deep prefetch skid over BRAM

The ring uses a fetch pointer `r_fptr` that walks allocated slots in ring order and reads each slot's beats as soon as the slot is complete. A 2-deep skid buffer sits over the synchronous-read BRAM so the next slot can prefetch while the current slot's tail drains. Without the prefetch skid, a one-beat-per-slot geometry would cap the drain at one beat every three cycles.

### Head freed at last-beat consume

The head pointer advances only when the drain consumes the last beat of the head slot:

```text
w_free = drain_valid_o && drain_ready_i && w_hd_blast
```

This keeps the occupancy count tied to actual data consumption rather than to fetch completion.

### Occupancy output

`occ_o` reports the current allocated-but-not-freed count. In `scoria_axi4_layer` this output is left unconnected; it exists for observability and for the formal proof assumptions.

### DEPTH bounds in-flight reads

`DEPTH = 32` is a power of 2. It is the return-ring depth, not the CAM depth (`NUM_ENTRIES = 8`), that bounds read bandwidth. With a 27-cycle DRAM round trip, 32 in-flight reads lets the controller sustain one read per cycle across the latency, whereas eight entries held for the full round trip would have capped bandwidth at roughly 180 MB/s on the board.

## FSM policy

There is no state machine. The ring is a head/tail pointer pair, a per-slot ready/resp array, an issue-order FIFO, and a prefetch skid over the BRAM.

## Timing

Allocation is combinational from `alloc_valid_i` to `alloc_ready_o`. DFI return beats are accepted combinationally when a ticket is at the issue-Q head. BRAM read latency is exactly one cycle, matched by the fetch pipeline. Drain is combinational from the skid head to `drain_valid_o`.

## Notes

- **Two non-synthesis input-contract assertions** at `scoria_rd_return_ring.sv:280-283`:
  - `assert (!(dfi_ret_valid_i && !w_iq_rd_valid))` — a DFI return beat arrived with no ticket in flight.
  - `assert (!(issue_valid_i && w_empty))` — a ticket was issued while the ring was empty.
- **Formal treatment:** both assertions are stated as assumptions in `formal/scoria/rd_return_ring/formal_scoria_rd_return_ring.sv`. The proof takes them as given, and the simulation checks remain as independent cross-checks.
- **BRAM latency trap:** the data storage is reset-free so Vivado maps it to Block RAM. Read latency is exactly one cycle; adding an output register without matching the fetch tag pipeline would silently corrupt the data path.

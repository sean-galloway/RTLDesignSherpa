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

# Front End: Pending Queues and the AR Take

**RTL:** `onyx_ccu.sv:541-548` (sideband decode), `619-656` (pending
queues and candidates), `685-688` and `713-719` (the AR take),
`1309-1334` and `1379-1404` (their sequential updates).

A cache port reaches the table through two inputs that arrive separately:
the sideband pulse that says *what* the cache is launching (class and line),
and the AR that carries the read itself. The front end turns the pulse into
a grant candidate and, once granted, takes the matching AR into the slot.

## Sideband decode

`coh_req_vld[d] = c_coh_req_valid[d] & is_coh_req(c_coh_req_type[d])`. A
pulse allocates unless its class is `WRITE_BACK` (`3'b100`), `WRITE_CLEAN`
(`3'b111`) or `EVICT` (`3'b101`) (`onyx_ccu.sv:509-513`): a write-back's
or a WriteClean's data is the write port's business, and a clean eviction
needs no coherence action without a directory. The allocating classes are
`READ_NOT_SHARED_DIRTY`, `READ_UNIQUE`, `CLEAN_UNIQUE`, and `READ_SHARED`
and `MAKE_UNIQUE`, which the house caches do not issue but which decode.

The sideband has no ready. A pulse is recorded or lost; it is never stalled.

## Pending queue (one per cache)

| Field | Width | Content |
|---|---|---|
| `r_pend_cnt[d]` | `PEND_W` = 3 | entries held, 0..4 |
| `r_pend_addr[d][k]` | `ADDR_WIDTH` | the pulse's address |
| `r_pend_type[d][k]` | 3 | the pulse's class |
| `r_pend_ovf[d]` | 1 | sticky: a pulse arrived with the queue full (debug only) |

: Table 2.1: Pending queue state (`PEND_DEPTH` = 4, a localparam)

The queue is a shift register with its head at entry 0. In one cycle:

- **Pop** when the grant goes to this port and the candidate was the queue
  head (`w_cand_live[d] = 0`): every entry shifts down one.
- **Push** when a decoded pulse arrives and it is not itself granted in the
  same cycle. A push in a popping cycle lands at `cnt - 1` (the freed tail);
  otherwise at `cnt`, if `cnt < 4`. A push into a full queue sets
  `r_pend_ovf` and the pulse is dropped; the simulation check names it
  (`onyx_ccu.sv:1640`), and the formal harness proves it unreachable under
  the caches' launch bound (`ap_no_pend_ovf`, `ap_pend_count`). The depth
  is the launches a cache can hold with their AR untaken (HAS Table 5.2).

The handbook's `design/shift-queue-same-cycle-push-pop.md` is the pattern.

## The candidate

```
w_cand_vld[d]  = (r_pend_cnt[d] != 0) ? 1 : coh_req_vld[d]
w_cand_live[d] = (r_pend_cnt[d] == 0)
w_cand_addr[d] = queue empty ? c_coh_req_addr[d] : r_pend_addr[d][0]
w_cand_type[d] = queue empty ? c_coh_req_type[d] : r_pend_type[d][0]
```

An empty queue bypasses: the live pulse is the candidate and can be granted
in its own cycle, in which case it is never pushed. The candidate is
combinational from the pulse, so the grant (and with it `dbg_grant_addr`
and the lock compare) sees the sideband in the cycle it arrives.

The IO port's candidate is described in ch02/07; it joins the same
candidate arrays at index `N_PORTS` (`onyx_ccu.sv:652-655`).

## The AR take

A grant arms the requester's AR: `r_arw_vld[d] <= 1`, `r_arw_slot[d] <=
slot` (`onyx_ccu.sv:1360-1363`; not for the IO's WriteUnique, which has no
read). Then:

- `c_arready[d] = r_arw_vld[d]` and `io_arready = r_arw_vld[IO]`
  (`onyx_ccu.sv:716-717`): **ARREADY comes from a register only**, never
  combinationally from ARVALID.
- On the handshake the slot records `r_ar_taken`, `r_arid`, `r_arcache`,
  `r_arprot`, `r_aruser` from the AR, and the arm clears
  (`onyx_ccu.sv:1380-1389`). For the IO read it also captures the burst
  (`r_io_araddr`, `r_io_arlen`, `r_io_arsize`, `r_io_arburst`,
  `r_io_arlock`, `r_io_arqos`, `r_io_arregion`) for the memory AR.
- While a requester is armed it gets no second grant (`~r_arw_vld[d]` in
  `w_cand_ok`), so at most one granted slot per requester waits for its AR.

The pairing is positional: the cache presents its ARs in launch order and
its pulses in the same order, so the next AR of a port belongs to the slot
its last grant armed. Two simulation checks hold the cache to it
(`onyx_ccu.sv:1612-1618`): the AR's line equals the slot's line, and
`ARLEN == 0` exactly when the class carries no data (CleanUnique,
MakeUnique). The AR's own length, size, burst, lock, QoS and region are not
used for a cache (the memory AR is regenerated from the slot, ch02/04).

## What the front end guarantees

- A requester's AR is accepted only into a slot granted to that requester
  and not yet holding its AR (`ap_arready_slot`).
- The AR taken is the slot's line (`ap_ar_pairing`).
- A pulse is never lost silently: either granted, queued, or flagged.

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

# Memory Read Path: AR Stage, Hold and R Router

**RTL:** `onyx_ccu.sv:820-870` (AR candidate, hold, payload), `872-887`
(R router), `1451-1460` (sequential).

## The AR candidate

The memory AR stage picks the **lowest-indexed** slot that is ready to read
(`w_marc_vld`, `w_marc_slot`, `onyx_ccu.sv:840-851`):

```
r_vld & r_ar_taken & ~r_nodata & ~r_mem_issued & ~r_dt
  & (DEFER_AR ? w_gathered : w_ac_all)
  & ~(write port holds a burst to this line)
```

- `DEFER_AR = 0`: once every peer has **accepted** its AC. With idle peers
  the CRs return before the first memory beat and nothing waits; this is
  the pair fabric's timing.
- `DEFER_AR = 1`: once every CR is **in** with no DataTransfer
  (`~r_dt` and `w_gathered`). Every issued read is a necessary one; every
  miss served from memory pays the gather first.
- A slot with no peers (the IO's ReadNoSnoop) is all-accepted and gathered
  from the grant, so its read is a candidate as soon as its AR is taken.
- **The write-in-flight hold (onyx BUG-002).** While the write port holds a
  burst (`w_wfly_vld = r_wstate != W_IDLE`) to the slot's line
  (`r_wfly_line`, captured at the burst's selection), the slot is not a
  candidate. AXI orders nothing between a read and a write in flight, and a
  snooped cache that has already completed its own write-back answers
  Invalid or Shared, so stale beats would be forwarded. The simulation
  check (`onyx_ccu.sv:1619-1625`) applies to reads whose bytes are used: a
  supplied slot's read, presented alongside its own absorption, is
  discarded.

## The AR hold

```
w_mar_vld  = r_mar_vld | w_marc_vld
w_mar_slot = r_mar_vld ? r_mar_slot : w_marc_slot
```

A candidate presented and not taken is latched (`r_mar_vld`, `r_mar_slot`)
and presented again, unchanged, every cycle until `mem_arready`
(`ap_mar_stable`). A DataTransfer arriving while the AR is presented does
not withdraw it; the read issues and its beats are dropped. The handshake
sets `r_mem_issued` and clears the hold.

`mem_arvalid` and the AR payload are functions of registers only (the
table, the hold, the write port's state): no memory-side input reaches them
combinationally.

## The AR payload

| Field | A cache's read | The IO's read |
|---|---|---|
| `mem_arid` | `IW'(slot)` | `IW'(slot)` |
| `mem_araddr` | `{r_line, OFFSET_W'(0)}` | `r_io_araddr` |
| `mem_arlen` | `FILL_BEATS - 1` | `r_io_arlen` |
| `mem_arsize` | `BYTE_W` (full width) | `r_io_arsize` |
| `mem_arburst` | INCR | `r_io_arburst` |
| `mem_arlock` | 0 | `r_io_arlock` |
| `mem_arqos`, `mem_arregion` | 0 | `r_io_arqos`, `r_io_arregion` |
| `mem_arcache`, `mem_arprot`, `mem_aruser` | the slot's, from the requester's AR | the slot's |

: Table 2.5: Memory AR payload (`onyx_ccu.sv:856-870`)

The IO's fields come from one capture register set, valid because one IO
read is in flight at a time (ch02/07).

## The R router

A memory beat names its slot by `mem_rid[SLOT_W-1:0]`; the upper ID bits
are ignored. The router classifies it (`onyx_ccu.sv:883-887`):

```
live = mem_rvalid & r_vld[s] & r_mem_issued[s] & ~r_mem_done[s]
fwd  = live & w_gathered[s] & ~r_dt[s]     -> to requester r_dir[s]
drop = live & r_dt[s]                      -> consumed, discarded
else                                       -> held (mem_rready low)
```

- **Forward:** the beat goes to the requester's R select (ch02/05) with the
  slot's `r_arid` as RID and the memory's RRESP, RUSER and RLAST.
  `mem_rready` is that requester's RREADY when the R select presents the
  memory beat, so the memory R channel waits on the requester
  combinationally.
- **Drop:** a peer supplied the line; `mem_rready = 1` and the beat is
  discarded.
- **Hold:** the gather is not complete (only possible with `DEFER_AR = 0`).
  The memory R channel stalls for the bounded remainder of the slowest
  peer's service; with idle peers it does not happen.
- **No read outstanding:** `live` requires the slot to have a read issued
  and undrained. A beat for anything else is a memory fault: it is held,
  never routed, and the simulation check names it
  (`onyx_ccu.sv:1626-1627`). The qualifier was added at onyx's first formal
  run, where a beat nobody asked for was forwarded to whatever port a stale
  slot named (TASK-001 step 4).

`RLAST` on a consumed beat (forwarded and taken, or dropped) sets
`r_mem_done`. Beats of different slots may interleave on a cache's R
channel; AXI permits it per ID, and jet-prime's fill engine demuxes by ID.

## What the harnesses state here

`ap_mar_legal` (the AR only for a slot with every AC accepted and no
DataTransfer known, unless held), `ap_mar_stable`, `ap_mar_no_wr_race`
(BUG-002), `ap_route_mem` (a forwarded beat belongs to a gathered slot with
no supplier and carries the requester's own ID), `ap_r_inflight` /
`ap_r_beats` (each cache sees exactly the IDs it issued, none after their
last beat, and every AR gets its beats), and `ap_mo` (the memory bookkeeping matches the reads
actually outstanding).

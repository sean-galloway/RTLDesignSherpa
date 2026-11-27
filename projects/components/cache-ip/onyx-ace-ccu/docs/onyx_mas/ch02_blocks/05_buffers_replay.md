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

# Snoop-Data Buffers and Replay Engines

**RTL:** `onyx_ccu.sv:889-1011` (replay candidates, buffers, R select),
`1462-1485` (replay sequential).

## The buffers

One buffer per requester, `N_REQ = N_PORTS + 1` in all (`g_buf[a]`,
`onyx_ccu.sv:937-949`):

| Property | Value |
|---|---|
| Depth | `BUF_DEPTH = SLOTS * FILL_BEATS` words of `BUS_WIDTH` |
| Address | `{slot, beat}` (`BUF_AW = SLOT_W + BEAT_INDEX_WIDTH`) |
| Write port | one: the CD beat the buffer's CD pick chose (ch02/03), at `{w_sni_head[src], r_cd_beat[src]}` |
| Read ports | two, asynchronous: the requester's replay at `{r_rpl_slot, r_rpl_beat}`, and the absorption at `{r_w_slot, r_w_beat}` |
| Implementation | `(* ram_style = "distributed" *)`, `ramstyle = "MLAB"`; no reset; payload only |

: Table 2.6: Snoop-data buffer

The supplier's line lands in the buffer of the slot's **requester**, not of
the supplier: the replay reads only its own requester's buffer, and the
absorption reads the buffer of `r_dir[r_w_slot]`. A slot's rows are written
once per transaction (its one supplier's beats) and read after the gather.

At `SLOTS = 18` and `FILL_BEATS = 8` (64-byte lines on a 64-bit bus) each
buffer is 144 words, three buffers at two ports.

## The replay engine (one per requester)

| State | Content |
|---|---|
| `r_rpl_vld[d]` | the engine holds a slot |
| `r_rpl_slot[d]` | the slot |
| `r_rpl_beat[d]` | the buffer beat being presented |
| `r_rpl_cnt[d]` | beats replayed so far (the IO's RLAST) |
| `r_rpl_hold[d]` | the current replay beat was presented and not taken |

: Table 2.7: Replay engine state

**Candidate** (`onyx_ccu.sv:901-916`): the **lowest-indexed** slot of
requester `d` that is gathered, has its AR taken, is supplied or carries no
data (`r_dt | r_nodata`), is not an IO write, is not yet replayed, and is
not the one the engine already holds. An idle engine loads it, starting at
beat 0 for a cache and at the IO's address offset within the line
(`r_io_araddr[OFFSET_W-1 -: BEAT_INDEX_WIDTH]`) for the IO.

**Beats:**

- a no-data slot (CleanUnique, MakeUnique) replays one beat: data 0,
  RLAST 1;
- a cache's supplied slot replays the whole line, beats 0 to
  `FILL_BEATS - 1`, RLAST on the last;
- the IO's supplied slot replays `io_arlen + 1` beats from its offset,
  RLAST when `r_rpl_cnt == r_io_arlen` (the read lies within the line; the
  simulation check enforces it, ch02/07).

Replay beats carry `RID = r_arid[slot]`, `RRESP = OKAY`, `RUSER = 0`. On
the last beat's handshake `r_rpl_done` sets and the engine frees.

## The R select (one per requester)

Each requester's R channel is driven by one of two sources
(`onyx_ccu.sv:951-1011`):

```
mem_want  = the router forwards a memory beat to this requester
rpl_pres  = r_rpl_vld & (r_rpl_hold | ~mem_want)
mem_pres  = mem_want & ~rpl_pres
```

A memory beat has priority over a replay beat that has not yet been
presented; once a replay beat is presented and not taken (`r_rpl_hold`), it
stays presented, so the R payload never changes under RVALID (AXI
stability, `ap_r_stable`). A memory beat refused this way waits on the
memory R channel (`mem_rready` low). The R outputs are a combinational mux
of the memory R inputs and the buffer's asynchronous read: a cache's or the
IO's `RVALID`, `RDATA` and `RLAST` follow `mem_rvalid` and `mem_rdata` in
the same cycle when the memory beat is selected.

## Why per requester

A requester with a supplied line and a memory read on another slot may be
offered both in one cycle; one engine per requester, and the memory beat
first, keeps each requester's R channel a single AXI stream while
different requesters' channels proceed in parallel. `ap_route_rpl` states
that a replayed beat belongs to a gathered slot of that requester that was
supplied or needs no data.

## Relationship to the HAS

HAS Chapter 3.4 says the replay engine "serves the port's oldest slot";
the RTL serves the lowest-indexed eligible slot, which is not the oldest
when slots are reused out of order. Nothing depends on age: a cache demuxes
by ID.

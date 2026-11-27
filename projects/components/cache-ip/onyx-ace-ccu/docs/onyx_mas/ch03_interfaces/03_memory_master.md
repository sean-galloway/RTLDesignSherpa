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

# Memory-Side AXI4 Master Timing

One AXI4 master, read and write sides independent.

## Timing class per signal

| Signal | Class | Source |
|---|---|---|
| `mem_arvalid`, `mem_ar*` | from flops | the AR candidate over table registers, or the hold `r_mar_*` (ch02/04); no input reaches them combinationally |
| `mem_rready` | comb | 1 for a dropped beat; else the requester's RREADY when its R select presents the memory beat; 0 for a held beat |
| `mem_awvalid`, `mem_aw*` | comb | in `W_AW`: the absorption's own fields, or the selected writer's AW passed through |
| `mem_wvalid`, `mem_w*` | comb | in `W_W`: the absorption's buffer beat, or the writer's W passed through |
| `mem_bready` | comb | in `W_B`: 1 for the absorption, else the writer's BREADY |

: Table 3.3: Memory-side timing classes

## IDs

- **Reads:** `ARID` = the slot index. Up to `SLOTS` reads are outstanding,
  each with a distinct ID; the memory may return them in any order and may
  interleave their beats. Only `mem_rid[SLOT_W-1:0]` is read.
- **Writes:** one burst outstanding. `AWID` is the writer's (a cache's, the
  IO's) or `IW'(8'hA0 | requester)` for an absorption; with one burst in
  flight, `BID` is never needed to route the response, and onyx forwards
  `mem_bid` as the writer's `BID`.

## What the memory must provide

- **Read data for issued reads only.** A beat whose ID names no read
  outstanding is held forever (`mem_rready` stays low) and named by a
  simulation check; it is a memory fault.
- **Read and write independence.** onyx itself orders a read behind a write
  in flight to the same line (ch02/04) and a write behind a gathering slot
  on the same line (ch02/06); it does not require the memory to order them.

## Rates

- Reads: one AR handshake per cycle at most; R one beat per cycle, shared
  by all requesters (the router takes one beat a cycle).
- Writes: one burst at a time, each burst at least IDLE + AW + one cycle per
  W beat + B (ch02/06). The write port is onyx's narrowest resource: every
  write-back, IO write and absorption in the system takes its turn on it.

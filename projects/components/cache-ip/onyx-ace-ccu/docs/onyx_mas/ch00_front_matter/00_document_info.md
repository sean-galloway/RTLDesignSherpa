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

# Document Information

This document is the Micro-Architecture Specification (MAS) for `onyx`, the
family's snoop-based ACE coherency unit: N coherent L1 caches on the cache
side (2 to 4), one ACE-Lite IO port, one AXI4 master toward memory, the
snoop fanout to every peer and the gather of their responses. The binding
architecture lives in the [onyx HAS](../../onyx_has/onyx_has_index.md)
(v0.3); this book records how the RTL implements it, block by block and
cycle by cycle.

**Written from the RTL.** Unlike the jet MAS 0.1, which was a contract for
an implementation not yet written, this book describes `onyx_ccu.sv`,
`onyx_top.sv`, `onyx_monlite.sv` and `onyx_counters.sv` as they stand on
2026-11-27. Line references (`onyx_ccu.sv:NNN`) are to that revision; they
drift with edits, and the signal names are the stable handle.

## References

### Related Documents

| Source | Title | Version |
|--------|-------|---------|
| RTL Design Sherpa | onyx Product Requirements Document | see `PRD.md` |
| RTL Design Sherpa | onyx Hardware Architecture Specification | 0.3 |
| RTL Design Sherpa | jet MAS (layout model) | 0.1 |
| ARM | AMBA AXI and ACE Protocol Specification | IHI0022H |
| RTL Design Sherpa | AMBA ACE Interface Definition (in-repo) | `cache-ip/References/` |

: Related Documents and Specifications

## Terminology

**Requester**
A cache port (index `0` .. `N_PORTS-1`) or the IO port (index `N_PORTS`).
`N_REQ = N_PORTS + 1` requesters share the table. In the RTL a requester
index is `RQ_W = clog2(N_REQ)` bits wide and is stored per slot in `r_dir`.

**Peer**
A cache that receives the AC of a transaction. A cache's transaction has
`N_PORTS - 1` peers (every other cache); the IO's shareable transaction has
`N_PORTS` (every cache); the IO's non-shareable read has none.

**Slot**
One entry of the transaction table. The slot index is also the memory read
ID (`mem_arid`) and the row index of the snoop-data buffers.

**Gather**
The collection of every peer's CR for one slot. "Gathered" is
`r_cr_left[s] == 0` (`w_gathered`). "All accepted" is `r_ac_left[s] == 0`
(`w_ac_all`).

**Verdict**
The slot's `r_dt` (some peer answered DataTransfer) and `r_pd` (that peer
also passed dirty).

**Absorption**
onyx's own write of a PassDirty line from the snoop-data buffer to memory.

**Replay**
Delivery of a supplied line (or an upgrade's single no-data beat) to the
requester from the snoop-data buffer.

**Old write-back**
A cache write presented, and not taken, while a slot on its line was still
gathering (`r_aw_old`): it predates that slot's verdict (onyx BUG-003).

**D-8 sideband**
The caches' coherence sideband: `c_coh_req_valid/addr/type` (one pulse per
fill, upgrade or write-back launch) and `c_coh_done_valid/id` (the retire).

**FILL_BEATS / BYTE_W / OFFSET_W / LINE_W**
`LINE_BYTES / (BUS_WIDTH/8)`, `clog2(BUS_WIDTH/8)`, `clog2(LINE_BYTES)`,
`ADDR_WIDTH - OFFSET_W` (`onyx_ccu.sv:222-231`).

## Revision History

| Rev | Date | Author | Notes |
|-----|------|--------|-------|
| 0.1 | 2026-11-27 | seang | Initial onyx MAS, written from the RTL as built (onyx TASK-001 step 7). |

: onyx MAS Document Revision History

**Last Updated:** 2026-11-27

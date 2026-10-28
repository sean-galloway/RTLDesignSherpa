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

This document is the Micro-Architecture Specification (MAS) for `jet`, the
lockup-free upgrade of the amber blocking MESI snoopy L1 cache: amber's
protocol, arrays, and interfaces plus a miss-status file (MSHRs),
hit-under-miss, miss merging, and a decoupled writeback path. The binding
architecture lives in the [jet HAS](../../jet_has/jet_has_index.md) (v0.3,
J1–J7 closed 2026-10-28); this book closes the implementation decisions the
HAS deferred.

**Status warning.** No jet RTL exists at 0.1. Every micro-architecture
statement in this book is a contract for the landing implementation, in the
same sense as amber MAS 0.5 ("contracts for the landing implementation");
the amber MAS's RTL-diff procedure (its ch05/02) applies here when the RTL
lands.

## References

### Related Documents

| Source | Title | Version |
|--------|-------|---------|
| RTL Design Sherpa | jet Product Requirements Document | 0.2 |
| RTL Design Sherpa | jet Hardware Architecture Specification | 0.3 |
| RTL Design Sherpa | jet MSHR design spec (superpowers spec) | 2026-10-28 |
| RTL Design Sherpa | amber MAS (sibling; landed-RTL reference) | 0.8 |
| ARM | AMBA AXI and ACE Protocol Specification | IHI0022H |
| gem5 | Ruby `MESI_Two_Level` protocol extract | commit f5c5a6e |
| Chinnakonda | Designing a Multiprocessor Cache Subsystem | local Calibre conversion |

: Related Documents and Specifications

## Terminology

**MAB / MSHR**
Miss address buffer / miss-status holding register. jet's `jet_mshr` is a
MAB in Chinnakonda's terms (§9.10.2): it holds the miss address and context,
NOT the fill data — fill beats write straight into the data array.

**Merge list**
The per-MSHR-entry list of requester sequence tags waiting on that entry's
fill (Chinnakonda's Pause Q entries, §9.8).

**PoS**
Point of serialization (Chinnakonda §10.7): the pipeline point where
same-line accesses serialize. In jet, the lookup stage (tag read + MSHR CAM
match in the same window).

**Snarf**
Serving a snoop's data from the writeback buffer instead of the array
(Chinnakonda §10.8.1); amber's SINK_WB_ACK semantics.

**PF_GUARD**
Amber's guard on the pending-fill bypass: the bypass promises snoop data
only when the fill's response phase has begun (fill beats can actually
arrive). Generalized per MSHR entry in jet.

**Set oversubscription**
Frontend victimization hazard (Chinnakonda §9.10.2): each in-flight miss
claims its victim way at alloc, so at most WAYS misses per set may be
outstanding.

**Anti-livelock hold-off**
Bounded snoop hold-off on a line whose upgrade (CleanUnique) was just
granted, until the write commits (Chinnakonda §10.9 / §8.1).

**WB buffer**
`jet_wb_buffer`, the decoupled writeback buffer (J5), `VICTIM_DEPTH` 1–4,
default 2.

**Response sequencer**
`jet_rsp_seq`, the issue-order response release (J4). GAXI has no ID field,
so out-of-order internal completion is re-sequenced at the response port.

**FUB / MAC / GAXI / MonBus / sdpram_core / CRRESP / DT / PD / IS / WU**
As in the amber MAS terminology (same definitions).

## Revision History

| Rev | Date | Author | Notes |
|-----|------|--------|-------|
| 0.1 | 2026-10-28 | seang | Initial jet MAS: written against the landed J1–J7 rulings and the 2026-10-28 design spec. No RTL yet; all micro-architecture is a contract for the landing implementation. |

: jet MAS Document Revision History

**Last Updated:** 2026-10-28

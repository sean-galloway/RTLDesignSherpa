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

# Event Encodings and Emission Points

**Status:** landed (2026-10-29) — the v1 emitters are the six classes
marked below; the class structure is the commitment (the J7 metrics
consume exactly these classes).

## Packet classes (jet additions)

| Class | Payload sketch | J7 metric feed | v1 emission |
|---|---|---|---|
| `MSHR_ALLOC` (0x10) | set index, fill class, occupancy-after | occupancy histogram, miss concurrency | emitted |
| `MSHR_MERGE` (0x11) | entry age, merge depth | merge rate (J3 validation) | emitted |
| `MSHR_RETIRE` (0x12) | occupancy-before, fill latency (alloc→commit cycles) | fill-latency distribution | emitted |
| `MSHR_OCCUPANCY` (0x13) | gauge sample | occupancy histogram | emitted |
| `WB_OCCUPANCY` (0x14) | gauge sample | drain/fill overlap | emitted (the WB_CAPTURE/WB_RETIRE pair below folds into this gauge in v1) |
| `STALL_TAG_FULL` (0x15) | rsp-seq tag-full stall, duration | congestion breakdown | emitted (the only STALL_ subclass v1 emits) |
| `HIT_UNDER_MISS` (0x16) | outstanding-miss count, hit latency | the hit-under-miss win | **not emitted in v1** — derivable from inherited hit events + the occupancy gauge; the enum is reserved |
| `SNOOP_SRC` | answer source (array / pending-fill / WB) | snoop-during-miss correctness | not emitted in v1 — derivable from the snoop event + MSHR/WB occupancy context |

The inherited amber classes (hit, miss, snoop, eviction, transition) carry
over unchanged so the amber/jet runs share one decode. (Table reconciled
to the landed emitters 2026-10-29, final review Minor 1: rows marked "not
emitted in v1" are the T13 board-bringup decision — emit them or keep the
derivation.)

## Encoding rules

Same 128-bit MonBus packet + 64-bit timestamp sideband as amber; the UNIT
id distinguishes the core observer from the two transport observers;
event-class codes allocate from the jet extension space so amber streams
decode identically.

## Tap sourcing note

The Task 10 implementation splices the stall and WB-occupancy taps at
`jet_top` from wires that already exist on the proven blocks, rather than
adding new event-tap ports to `jet_control` or `jet_wb_buffer`:

- `STALL_TAG_FULL` is driven from `ctrl_lkup_stall_o` and
  `ctrl_lkup_stall_reason_o`, which `jet_control` already exposes for
  congestion accounting.
- `WB_OCCUPANCY` is driven from `wb_occupancy_o`, which `jet_wb_buffer`
  already exposes as its occupancy gauge.

No new ports were added to `jet_control` or `jet_wb_buffer` because the
required information is already available at the top level; adding
single-purpose tap ports would churn the proven functional blocks without
changing the information content. Only `jet_mshr` received new event-tap
ports (`alloc_o`, `alloc_set_o`, `alloc_cls_o`, `merge_o`, `merge_idx_o`,
`merge_depth_o`, `retire_o`, `retire_idx_o`) because the alloc/merge/retire
instantiation details are internal to that block.

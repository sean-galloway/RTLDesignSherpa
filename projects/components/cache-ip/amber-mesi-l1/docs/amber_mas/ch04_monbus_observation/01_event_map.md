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

# MonBus Event Encodings and Emission Points

## Overview

Because amber has no register block, the MonBus observation map replaces the traditional register-map chapter. Every software-visible event is emitted as a MonBus packet by `amber_monlite`.

## Event Encoding

| Event code | Name | Emitting module | Trigger |
|------------|------|-----------------|---------|
| `AMBER_EV_HIT` | hit | `amber_monlite` | `CTRL_HIT_RD` or `CTRL_HIT_WR` |
| `AMBER_EV_MISS` | miss | `amber_monlite` | `CTRL_MISS_VICTIM` |
| `AMBER_EV_SNOOP` | snoop | `amber_monlite` | AC handshake accepted |
| `AMBER_EV_EVICT` | eviction | `amber_monlite` | dirty victim staged to `amber_victim` |
| `AMBER_EV_TRANSITION` | MESI transition | `amber_monlite` | tag-array state write |
| `AMBER_EV_FILL_START` | fill start | `amber_monlite` | `CTRL_MISS_FILL` |
| `AMBER_EV_FILL_END` | fill end | `amber_monlite` | `CTRL_FILL_WRITE` |
| `AMBER_EV_DRAIN_START` | drain start | `amber_monlite` | `CTRL_MISS_DRAIN` |
| `AMBER_EV_DRAIN_END` | drain end | `amber_monlite` | `drain_done` |
| `AMBER_EV_DROPPED` | dropped packet | `amber_monlite` | packet dropped due to backpressure |

: Table 4.1.1: MonBus event encodings

The exact numeric codes are assigned in `amber_pkg` and match the house `monitor_common_pkg` allocation rules.

## Payload Fields

All packets carry:

- `agent_id` — house `MON_AGENT_ID` for amber.
- `unit_id` — sub-unit within amber (control, snoop, etc.).
- `event_code` — one of the codes above.
- `timestamp` — 64-bit side-band sampled at emission.

Event-specific payload:

| Event | Payload fields |
|-------|---------------|
| hit | `set`, `way`, `state_before`, `state_after`, `we` |
| miss | `set`, `way`, `miss_class`, `we` |
| snoop | `snoop_type`, `hit`, `response_class` |
| eviction | `set`, `way`, `dirty`, `line_addr` |
| transition | `set`, `way`, `old_state`, `new_state`, `cause` |
| fill_start / fill_end | `line_addr` |
| drain_start / drain_end | `line_addr` |
| dropped | `dropped_count` |

## Miss-Class Encoding

Miss classes follow the `cache_sim` computation:

| Code | Class | Meaning |
|------|-------|---------|
| `AMBER_MISS_COMPULSORY` | compulsory | First access to this line. |
| `AMBER_MISS_CAPACITY` | capacity | Line was evicted by capacity pressure. |
| `AMBER_MISS_CONFLICT` | conflict | Line was evicted by mapping conflict. |

The golden model supplies the class; the RTL records what it is told. When the model is not present, the class is recorded as `AMBER_MISS_UNKNOWN`.

---

**Last Updated:** 2026-10-06

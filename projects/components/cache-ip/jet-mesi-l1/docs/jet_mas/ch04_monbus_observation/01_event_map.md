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

**Status:** planned contract — final bit assignments land with the RTL;
the class structure below is the commitment (the J7 metrics consume exactly
these classes).

## Packet classes (jet additions)

| Class | Payload sketch | J7 metric feed |
|---|---|---|
| `MSHR_ALLOC` | set index, fill class, occupancy-after | occupancy histogram, miss concurrency |
| `MSHR_MERGE` | entry age, merge depth | merge rate (J3 validation) |
| `MSHR_RETIRE` | occupancy-before, fill latency (alloc→commit cycles) | fill-latency distribution |
| `HIT_UNDER_MISS` | outstanding-miss count, hit latency | the hit-under-miss win |
| `STALL_<class>` | stall class code, duration on release | congestion breakdown |
| `WB_CAPTURE` / `WB_RETIRE` | WB occupancy, drain latency | drain/fill overlap |
| `SNOOP_SRC` | answer source (array / pending-fill / WB) | snoop-during-miss correctness |

The inherited amber classes (hit, miss, snoop, eviction, transition) carry
over unchanged so the amber/jet runs share one decode.

## Encoding rules

Same 128-bit MonBus packet + 64-bit timestamp sideband as amber; the UNIT
id distinguishes the core observer from the two transport observers;
event-class codes allocate from the jet extension space so amber streams
decode identically.

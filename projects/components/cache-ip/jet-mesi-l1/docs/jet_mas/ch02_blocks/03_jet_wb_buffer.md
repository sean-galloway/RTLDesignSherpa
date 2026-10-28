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

# jet_wb_buffer: Decoupled Writeback Buffer

**Status:** planned contract. The J5 structure: dirty victims captured at
miss alloc, drained oldest-first by `l1_drain`, independently of the fill
they were evicted for.

## Entry format

`VICTIM_DEPTH` entries (elaboration 1–4, default 2):

| Field | Content |
|---|---|
| `valid` | captured, not yet BRESP-retired |
| `line` | victim line address (the snoop-compare key) |
| `state` | M (only dirty victims are captured) |
| `data` | the full line, read from the data array at capture |
| `beats_sent` | drain progress |

## Lifecycle

1. **Capture (at alloc).** When `jet_control` allocates a miss whose victim
   is dirty: the victim's beats are read from the data array (port B, or
   port A between fill beats) into a free WB entry, and the MSHR entry
   records `wb_slot`. The fill proceeds immediately — no drain wait (this
   is what amber's serialized MISS_DRAIN did NOT allow).
2. **Drain (independent).** `l1_drain` empties entries oldest-first:
   AW/W beats out, BRESP back. Per Chinnakonda §10.10.1 the **address is
   held until BRESP** (a fabric read to the same line must not issue while
   the write is outstanding); the data beats may leave as accepted.
3. **Retire.** On BRESP the entry frees.

## Snoop service (snarf, §10.8.1)

A snoop matching `line` in a valid WB entry is served from the entry's
data with amber's SINK_WB_ACK semantics: CR/CD from the buffer, and the
entry's post-snoop state effect recorded so the drain writes back the
correct thing (an invalidated snarfed victim still drains — the fabric
already took the data; the drain completes the memory update). This closes
the ships-in-the-night corner (§10.12.2): a pre-BRESP WriteBack plus a
clean-invalidating snoop to the same line is answered from the buffer,
never "not present".

## Congestion rule (J6)

WB-full stalls ONLY new dirty-victim misses (clean-victim misses allocate
freely). Drains always complete — the write path is always drainable — so
the stall is bounded by one drain's latency. Snoops never wait on the WB
buffer (they snarf), closing §8.2 case 5 by construction.

## Why not a combined fill/victim/replay queue

Chinnakonda §10.10.5 offers the combined-Q option (adaptable to read- or
write-heavy mixes; superset-field waste). jet keeps the MAB and WB buffer
separate: at 8+2 entries the superset waste would exceed the adaptability
win, and the separate structures keep the formal surface small (the
composed-corner proof in ch05/01 reasons about two bounded FIFOs, not one
shared pool). Recorded as the considered alternative.

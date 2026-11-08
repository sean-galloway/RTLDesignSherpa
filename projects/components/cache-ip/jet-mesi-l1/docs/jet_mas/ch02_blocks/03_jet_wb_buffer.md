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
| `data` | the line, **one word per (slot, beat)** in a beat-addressed store shared by all entries (`r_data[VICTIM_DEPTH*FILL_BEATS]`, distributed RAM, no reset) |
| `beats_rcvd` | capture progress (the slot closes when the line is complete) |

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

**How the stream reads the entry (FPGA review 2026-11-07).** The CAM's
matched slot (`sn_match_idx_o`) is latched by `jet_control` at the grant;
each CD beat is then read from the store by `(sn_rd_slot_i, sn_rd_beat_i)`
on `sn_rd_data_o`. The entry may retire on its BRESP mid-stream, so while
the stream runs `jet_control` holds `sn_lock_i` and the buffer **does not
reuse the retired slot**: a locked tail slot is not free (`w_any_free`
excludes it, so `cap_gnt_o` and `wb_full_o` honour the lock), and the
words stay in place until the stream ends. The earlier contract copied the
whole line into a snapshot register at the grant; a line-wide read port on
beat-written storage forces the store into flops (and, under the reset
macro, onto the reset net), which was the second-largest flop block of the
core on the Genesys2. Handbook: `design/sram-and-memories.md`, "A line-wide
read interface forces a flop array: read payload by beat".

## Storage and ports

| Port group | Shape | Notes |
|---|---|---|
| capture `cap_i / cap_beat_i / cap_beat_data_i` → `cap_gnt_o / cap_slot_o` | one beat per cycle into `r_data[{open_slot, beats_rcvd}]` | the only write port |
| drain `drain_valid_o / drain_addr_o`, `drain_beat_idx_i` → `drain_beat_data_o`, `drain_done_i` | head slot; `l1_drain` presents its W beat index and takes the word the same cycle | the l1_victim-shaped head, now beat-serial |
| snarf `sn_line_i` → `sn_hit_o / sn_match_idx_o`; `sn_lock_i / sn_rd_slot_i / sn_rd_beat_i` → `sn_rd_data_o`; `sn_bresp_cycle_o`, `sn_eff_i` | CAM on `line`, then a beat read of the matched slot | the lock pins the slot against reuse |

`r_valid`, `r_allocated`, `r_line`, `r_beats_rcvd`, `r_eff` and the pointers are
reset; `r_data` is not — every word is qualified by its slot's valid bit.

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

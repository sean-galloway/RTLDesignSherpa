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

# onyx_counters

**RTL:** `rtl/fub/onyx_counters.sv`.

Eight 32-bit counters on the event taps, exact under any burst. The MonBus
carries each event's payload and time through a bounded queue and reports
what it drops; the counts the D6 measurement is made of (reads issued
against reads wasted) have to be exact, and a counter is the honest
instrument for a count.

## The counters

| Index | Output | Increment per cycle |
|---|---|---|
| 0 | `cnt_txn` | `evt_grant` |
| 1 | `cnt_supplied` | number of ports with `evt_gather & evt_gather_dt` |
| 2 | `cnt_mem_read` | `evt_mem_ar` |
| 3 | `cnt_read_wasted` | number of ports with `evt_read_wasted` |
| 4 | `cnt_absorb` | `evt_absorb` |
| 5 | `cnt_wb` | `evt_wb` (cache write-backs and IO writes) |
| 6 | `cnt_cu_dt` | number of ports whose gather completes a CleanUnique slot with DataTransfer |
| 7 | `cnt_old_wb` | number of caches whose write is presented, not taken this cycle, on a line a slot still gathers, and not already old |

: Table 4.3: onyx counters

The per-port increments are popcounts (`PC_W` bits) because two ports can
complete two slots' gathers in one cycle.

**Clear and freeze.** `clear_i` (one-cycle pulse) zeroes all eight;
`freeze_i` (level) holds them. The rig ties both to its tally's clear and
freeze so one host protocol snapshots the MonBus tally and the counters
together. **Saturation:** a counter stops incrementing once it exceeds
`0xFFFFFFFF - N_PORTS`, so it never wraps.

## The corner counts without a manager port

`cu_dt` and `old_wb` need per-slot state `onyx_ccu` does not export. The
counter block rebuilds it from the grant and gather taps
(`onyx_counters.sv:85-127`):

- per slot, the granted line `r_sl_line` (no reset), whether the slot is a
  CleanUnique `r_sl_cu`, and whether it is still gathering `r_sl_gath`
  (set at the grant, cleared by the slot's gather-done tap or when
  `slot_vld_i` drops);
- `r_aw_old`, the same recurrence as `onyx_ccu`'s
  (`c_awvalid & ~c_awready & (r_aw_old | line still gathers)`).

An `old_wb` event is the cycle a write first becomes old: presented, not
accepted in that cycle, on a gathering line, not yet marked. A write
selected before the slot's grant completes its AW in its accepting cycle
and is not counted, as `onyx_ccu`'s `r_aw_old` excludes it. The pair rig
checks the mirrored `r_aw_old` against the manager's every cycle.

Reading them: `cu_dt` counts killed upgrades whose peer passed the line
dirty (onyx BUG-001's case); with the read alongside the snoop it is the
one kind of supplied slot whose memory read is never issued, so
`read_wasted = supplied - cu_dt` in that mode. `old_wb` counts the
write-backs the BUG-003 order rule acts on (HAS Chapter 4.4).

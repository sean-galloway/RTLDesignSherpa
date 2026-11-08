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

# l1_victim: Depth-1 Victim Buffer

**Module:** `l1_victim.sv`
**Location:** `projects/components/cache-ip/common-ip/rtl/fub/`
**Status:** RTL landed; this chapter is the micro-architecture contract the RTL implements.

---

## Overview

`l1_victim` is a depth-1 buffer that holds one dirty victim's **address and valid** while its write-back (drain) is outstanding. The depth-1 size matches the single-outstanding-miss model: there can be only one dirty victim at a time because the pipeline blocks on the miss until it resolves.

The victim's **line data does not live here** (FPGA review 2026-11-07). It is gathered beat by beat into `victim_line_mem` inside `l1_control`, a `FILL_BEATS`-word store with no reset, and read back one beat at a time by its two consumers: the drain (through `ctrl_victim_beat_idx` / `ctrl_victim_beat_data`) and the snoop bypass (`victim_sn_word`, indexed by the snoop beat counter). A line-wide `victim_data` bus, as the earlier contract had it, forces the store into flops: a register with a whole-line read interface cannot be a RAM, and under the async-reset macro it also adds `LINE_BYTES*8` pins to the reset net (handbook: `design/sram-and-memories.md`, "A line-wide read interface forces a flop array"). Beat-addressed, the store maps to distributed RAM.

---

## Fields

| Field | Width | Meaning |
|-------|-------|---------|
| `victim_addr` | `ADDR_WIDTH` | Full line address (for AW). |
| `victim_valid` | 1 | Buffer is occupied. |

The dirty line itself is `l1_control.victim_line_mem[FILL_BEATS]` (`BUS_WIDTH` per beat), written during the `CTRL_MISS_VICTIM` gather and qualified by `victim_valid`; it carries no reset.

---

## Handshake with l1_control

| Signal | Direction | Meaning |
|--------|-----------|---------|
| `victim_load` | input from `l1_control` | Mark the buffer occupied this cycle (the gather of the line into `victim_line_mem` has completed). |
| `victim_addr_in` | input from `l1_control` | Line address to load. |
| `victim_clear` | input (the drain's done pulse) | Release the buffer. |
| `victim_busy` | output to `l1_control` | Buffer already occupied. |
| `victim_empty` | output to `l1_control` | Buffer is empty. |

`victim_load` asserts for one cycle in `CTRL_MISS_VICTIM` when the victim is dirty. The buffer is busy until `l1_drain` reports done.

---

## Bypass for Snoops

If a snoop arrives for the victim line while the drain is still outstanding, `l1_victim` can supply the data without re-reading `l1_data_array`. `l1_control` checks:

```systemverilog
victim_valid && (snoop_line_addr == victim_addr)
```

If matched, the snoop responder sources CD beats from `victim_line_mem[sn_beat]` (`victim_sn_word`) instead of from `data_array` port B. This is the victim bypass; it reads the store one beat at a time, exactly as the drain does.

---

## Timing

| Cycle | Event |
|-------|-------|
| `CTRL_MISS_VICTIM`, victim is M | The gather writes `victim_line_mem[k]` from port A beat by beat (with `DATA_SYNC_READ` the beat address leads the word by one cycle); `victim_load` asserts on completion and `victim_valid` sets next cycle. |
| `CTRL_MISS_DRAIN` | `l1_drain` consumes `victim_addr`, presents `victim_beat_idx` for each W beat and takes the word on `victim_beat_data` the same cycle; begins AW/W burst. |
| Drain done (`ctrl_drain_done`) | `victim_valid` cleared. |

The buffer is never loaded while valid; the single-outstanding property guarantees this cannot happen.

---

**Last Updated:** 2026-11-07

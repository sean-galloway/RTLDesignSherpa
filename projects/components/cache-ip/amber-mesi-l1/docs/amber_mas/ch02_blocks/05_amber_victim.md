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

# amber_victim: Depth-1 Victim Buffer

**Module:** `amber_victim.sv`
**Location:** `projects/components/cache-ip/amber-mesi-l1/rtl/fub/`
**Status:** Pre-RTL micro-architecture contract

---

## Overview

`amber_victim` is a depth-1 buffer that holds one dirty cache line while its write-back (drain) is outstanding. The depth-1 size matches the single-outstanding-miss model: there can be only one dirty victim at a time because the pipeline blocks on the miss until it resolves.

---

## Fields

| Field | Width | Meaning |
|-------|-------|---------|
| `victim_addr` | `ADDR_WIDTH` | Full line address (for AW). |
| `victim_data` | `LINE_BYTES*8` | Dirty line data. |
| `victim_valid` | 1 | Buffer is occupied. |

---

## Handshake with amber_control

| Signal | Direction | Meaning |
|--------|-----------|---------|
| `victim_load` | input from `amber_control` | Load the buffer from `amber_data_array` port A this cycle. |
| `victim_addr_in` | input from `amber_control` | Line address to load. |
| `victim_data_in` | input from `amber_control` | Line data to load. |
| `victim_busy` | output to `amber_control` | Buffer already occupied. |
| `victim_empty` | output to `amber_control` | Buffer is empty. |

`victim_load` asserts for one cycle in `CTRL_MISS_VICTIM` when the victim is dirty. The buffer is busy until `amber_drain` reports done.

---

## Bypass for Snoops

If a snoop arrives for the victim line while the drain is still outstanding, `amber_victim` can supply the data without re-reading `amber_data_array`. `amber_control` checks:

```systemverilog
victim_valid && (snoop_line_addr == victim_addr)
```

If matched, the snoop responder sources CD beats from `victim_data` instead of from `data_array` port B. This is the victim bypass.

---

## Timing

| Cycle | Event |
|-------|-------|
| `CTRL_MISS_VICTIM`, victim is M | `victim_load` asserted; `victim_valid` sets next cycle. |
| `CTRL_MISS_DRAIN` | `amber_drain` consumes `victim_addr` and `victim_data`; begins AW/W burst. |
| Drain done (`ctrl_drain_done`) | `victim_valid` cleared. |

The buffer is never loaded while valid; the single-outstanding property guarantees this cannot happen.

---

**Last Updated:** 2026-10-06

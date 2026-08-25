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

# 4.1 Width Converter FSMs

These are the state machines inside the width converters.

## 4.1.1 Upsize Structure (no FSM)

The **axi_data_upsize** module has NO state machine. Earlier revisions
of this chapter documented an ACCUMULATE/OUTPUT FSM; the RTL is a
register-and-gating structure built deliberately so that output and the
next accumulation OVERLAP -- an explicit OUTPUT state would insert the
very bubble the design avoids.

The real structure:

- `r_beat_count` walks slots as narrow beats land in the accumulator;
- a group completes on `WIDTH_RATIO` beats or an early `narrow_last`;
- `r_wide_valid` presents the completed group on the wide side while
  the NEXT group starts accumulating -- when a wide handshake and a
  completing narrow beat coincide, non-blocking last-write-wins
  ordering keeps the freshly completed group (the RTL's header records
  the drop bug this replaced);
- `narrow_ready = !r_wide_valid || wide_ready`, so the narrow side
  stalls only when the wide side is holding a beat hostage.

On an early `narrow_last`, unwritten accumulator slots are zeroed in
the same single write that deposits the first beat of a group --
residual data from the previous group must not leak into a partial
wide beat.

## 4.1.2 Downsize Structure (single buffer, no FSM)

Same story: no IDLE/LOAD/OUTPUT machine. The single buffer performs an
**atomic replace** -- `wide_ready` asserts during the LAST narrow beat
of the current wide beat, so the replacement lands as the drain
finishes and a steady stream pays no per-beat bubble (measured 0.992
beats/cycle, see 2.3):

```systemverilog
assign wide_ready = !r_wide_buffered || (narrow_ready && w_last_narrow_beat);
```

With `TRACK_BURSTS=1` the condition narrows to `mid_burst_replace`,
which excludes each burst's final beat -- one bubble per burst
boundary, not per beat. A beat pointer (`r_beat_ptr`) selects the slice
driven onto the narrow side; `narrow_last` in tracked mode comes only
from the beat counter reaching `burst_len + 1`.

## 4.1.3 Full Converter FSMs

### Write Converter (axi4_dwidth_converter_wr)

```
IDLE:
  - AW valid → accept AW, store info
  - W valid → buffer W data

AW_ACCEPT:
  - downstream AW ready → forward adjusted AW

W_CONVERT:
  - upsize accumulating narrow W beats
  - on output → forward wide W beat

B_FORWARD:
  - B from downstream → forward to master
```

### Read Converter (axi4_dwidth_converter_rd)

```
IDLE:
  - AR valid → accept AR, store info, forward adjusted AR

AR_FORWARD:
  - downstream AR ready → wait for R

R_CONVERT:
  - downsize splitting wide R into narrow beats
  - track burst count for RLAST

R_FORWARD:
  - narrow R beat ready → forward to master
  - on RLAST → IDLE
```

## 4.1.4 Timing Diagrams

### Upsize (8:1 ratio, m_ready held high)

No `s_ready` bubble: the wide handshake overlaps the next group's first
narrow beat.

```
clk     __|¯¯|__|¯¯|__|¯¯|__|¯¯|__|¯¯|__|¯¯|__|¯¯|__|¯¯|__|¯¯|__|¯¯|
s_valid ¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯
s_data    D0   D1   D2   D3   D4   D5   D6   D7   D8   D9   ...
s_ready ¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯
m_valid _______________________________________|¯¯¯¯|_______________
m_data                                          WIDE0
m_ready ¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯
```

`s_ready` only drops if the wide side stalls with a completed group
waiting (`!r_wide_valid || wide_ready` fails).

### Downsize (8:1 ratio, single buffer, atomic replace)

`s_ready` re-asserts DURING the last narrow beat, so WIDE1 is accepted
as D7 drains -- back-to-back wide beats with no gap:

```
clk     __|¯¯|__|¯¯|__|¯¯|__|¯¯|__|¯¯|__|¯¯|__|¯¯|__|¯¯|__|¯¯|__|¯¯|
s_valid ¯¯¯¯¯¯¯|_________________________________________|¯¯¯¯|_____
s_data    WIDE0                                            WIDE1
s_ready ¯¯¯¯¯¯¯|__________________________________________|¯¯¯¯|____
m_valid ________|¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯
m_data           D0   D1   D2   D3   D4   D5   D6   D7   E0   E1 ...
m_ready ¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯
```


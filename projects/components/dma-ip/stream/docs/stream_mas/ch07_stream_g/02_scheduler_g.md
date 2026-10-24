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

# scheduler_g (STREAM)

**Module:** `scheduler_g.sv`
**Location:** `projects/components/dma-ip/stream/rtl/fub_g/`
**Status:** Implemented (stream TASK-020)
**Last Updated:** 2026-10-24

---

## Overview

`scheduler_g` has the ports of `scheduler` (Section 2.4) plus the sequencer port of rapids-g's
`scheduler_g`: `seq_wr_en` / `seq_wr_addr` / `seq_wr_data` (a word write into the window),
`seq_rd_addr` / `seq_rd_data` (a combinational word read, registered by the sequencer), `seq_attn` (the
channel needs the firmware), `seq_fault` (the serving hart halted: fatal) and `seq_alg_max` (the image's
highest next-address selector). Its datapath is `scheduler_core`, driven through the core's sequencing
port (Table 2.4.1) instead of by the state machine.

## The Window

The window is RAPIDS MAS Section 5.2's, word for word and bit for bit, so one firmware image runs both
designs. Where STREAM has no counterpart the bit reads as a constant the firmware already handles:

| Word / bit | rapids-g | STREAM |
|---|---|---|
| STATUS [13:12] opcode | DATA / CTRL_READ / CTRL_WRITE | always DATA (0) |
| STATUS [17] tile_bad, [23] header only | the tile header | 0 |
| STATUS [18] pkt_ok | the packet records can go | 1: FETCH_DESC -> XFER_DATA is taken the cycle after the start |
| R 5 LENGTH, R 17 head length, R 19-20 beat totals | bytes; the totals a ceiling | beats; the totals are the length |
| R 13 FIFO [17], [18] | -- | write_complete, rd_ahead (the prefetch is a beat ahead) |
| R 14 CFG | BYTE_LANES, OFF_W, EN_READ, EN_WRITE, ROW_COL, TILE_HDR | the same fields; EN_READ = EN_WRITE = 1, TILE_HDR = 0 |
| R 22 ALG | the latched next-address selector | the same, from chunk 0 [224:217] (reserved bits in STREAM's legacy layout, 0 on a plain descriptor) |

: Table 7.2.1: Window differences

The next-address selector is judged by `scheduler_core` as it latches a descriptor (`desc_alg_max`: 0 on
the state machine, the image's `seq_alg_max` here), so STATUS [11] and HEAD_SUM [0] call invalid what the
take will refuse, on both designs alike.

## Commands and the Automatic Edges

The command legality table and the pre-validation flags (STAGE, ARM, ARM_NEXT, GEN_OK, DECLINE, STAGE_ARM)
are rapids-g's (RAPIDS MAS Section 5.2). Two STREAM particulars:

- **COMPLETE -> IDLE waits for the commits.** STREAM's state machine holds COMPLETE until every write of a
  last descriptor has committed (`write_complete`), so the channel is not idle while data still lands. An
  IDLE command, or an ARM without ARM_NEXT, arms the leave; the hardware takes it when `write_complete`
  holds. NEXT_DESC is immediate, as the state machine's is, so a chain streams while commits drain.
- **The read-ahead prefetch takes only a staged head.** `scheduler_core`'s `head_ok` is `r_staged`: a
  chained legacy head the firmware has STAGEd (with or without STAGE_ARM) is peeked by the read side and
  advanced in place by the write side; the core reports the advance (`wr_advance`), and `scheduler_g`
  treats it as the take it is -- the staged flags clear, a STAGE_ARM head comes in armed with its chain
  outcome, and the beat totals follow the new head. A head not yet staged waits: the channel finishes the
  running descriptor and walks the states when the firmware stages it. With the prefetch disabled
  (`cfg_rd_prefetch_enable` = 0) the walk is the only path, as on rapids-g.
- **The advance wins over the completion.** The last writes of a descriptor can issue on the cycle its
  reads finish with a staged chained head present, so the in-place advance and `exec_complete` are true
  together. The state machine takes the advance; so does `scheduler_g`: the armed auto-completion and a
  COMPLETE command both yield to `wr_advance` that cycle (the command is dropped as late, not counted as
  illegal), and the channel stays in XFER_DATA on the new head. Taking COMPLETE instead left the new
  head loaded and never issued.

## MonBus

`scheduler_core` sends STREAM's packets (DESC_START on entry to FETCH_DESC, DESC_COMPLETE or IRQ on entry
to COMPLETE and on an in-place advance, ERROR once). The firmware's own packets (FW_DEBUG, FW_ERROR;
STREAM event codes 0x09 and 0x0A) merge onto the same port, one buffered, offered on every cycle the core
has none; `mon_valid` never depends on `mon_ready`.

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

# stream-g Overview

**Status:** Implemented (stream TASK-020)
**Last Updated:** 2026-10-24

---

## What stream-g Is

stream-g is STREAM with its scheduler state machines replaced by firmware. The core has one gatling, the
four-context barrel RV32I core (`projects/components/riscv-ip/gatling-rv32i`), running one firmware image
for all of its 4, 8 or 16 channels. It is rapids-g (RAPIDS MAS Chapter 5) applied to STREAM: the firmware
makes every decision STREAM's state machine makes and does the EXT address arithmetic STREAM's `scheduler`
does in hardware -- taking a descriptor, validating it, starting it, finishing it, following a chain, and
the EXT run bases, pushed ahead into a small queue per direction.

Everything that happens at the engines' rate stays hardware: the counters the done strobes decrement, the
address advance within a run, the read-ahead prefetch, the commit accumulator, the timeouts, the sticky
errors and the MonBus packets. That hardware is `scheduler_core` (Section 2.4), the datapath STREAM's
`scheduler` wraps, so the two designs share one copy.

stream-g is register-compatible with STREAM: the same register map (plus the firmware-load registers
`FW_CTRL`, `FW_ADDR`, `FW_DATA` and `FW_RDATA` at 0x3A0-0x3AC, which a STREAM build also decodes and reads
as "no firmware"), the same descriptor format, the same host software. A build identifies itself with
`FW_CTRL.STREAM_G` = 1.

## What Is Shared with rapids-g, and What Is Not

The sequencer block, the register window and the firmware are rapids-g's, used unchanged:

| Piece | Where it lives | stream-g |
|---|---|---|
| The sequencer: gatling, instruction ROM (or the loadable BRAM), scratch, window decoder, register mailbox | `rapids/rtl/macro_g/rapids_seq_g.sv` | instantiated as is, one per core |
| The register window of a scheduler (STATUS, CMD, HEAD_SUM, the bases, FW packets) | RAPIDS MAS Section 5.2 | `scheduler_g` reproduces it bit for bit (Section 7.2) |
| The firmware image: the executive, the policy table, the two-slot poll, the Z-order algorithm | `rapids/rtl/fw_g/sched_g.S` -> `generated/fw/sched_g_fw.svh` | the same include, through rapids' include directory |
| The loadable firmware memory and its registers | RAPIDS MAS Section 5.3 | the same registers at the same offsets, one set (one gatling) |

: Table 7.1.1: What stream-g takes from rapids-g

What differs is STREAM's: the descriptor length is in beats, so the beat totals are the length itself
(no bytes-to-beats ceiling); there are no control engines, packet records or tile ports, so the window
bits for them read as constants; and STREAM's read-ahead prefetch (Section 2.4) stays hardware. A chained
legacy head the firmware has STAGEd is peeked by the read side and advanced in place by the write side,
the channel never leaving XFER_DATA, exactly as under the state machine; a head the firmware has not
staged yet is not prefetched, and the channel walks COMPLETE / NEXT_DESC / FETCH_DESC when the firmware
does stage it. Leaving COMPLETE for IDLE waits for every write to commit, as STREAM's state machine holds.

## Structure

| Level | stream | stream-g | How the -g module is made |
|---|---|---|---|
| fub | `scheduler` = state machine + 2 run-base generators + `scheduler_core` | `scheduler_g` = command port + base FIFOs + `scheduler_core` | hand-written (`rtl/fub_g/`) |
| macro | `scheduler_group_array` | `scheduler_group_array_g`: the same, with `scheduler_g` and one `rapids_seq_g` | generated |
| macro | `stream_core` | `stream_core_g` | generated |
| top | `stream_top_ch8`, `stream_top_ch16` | `stream_g_top_ch8`, `stream_g_top_ch16` | generated |
| sequencer | -- | `rapids_seq_g` (rapids-g's) | reused |
| firmware | -- | rapids-g's `sched_g.S` | reused |

: Table 7.1.2: stream and stream-g, level by level

`bin/gen_stream_g.py` derives every generated file from the STREAM file of the same name (Section 7.3);
a change to STREAM reaches stream-g by rerunning it. One gatling serves 4, 8 or 16 channels (one hart per
channel at 4 and 8, two channels per hart at 16, `rapids_seq_g`'s defaults); the generated array refuses
any other channel count, and `SHARED_ENGINES` = 0, at elaboration.

## What stays hardware, and why

As on rapids-g, two transitions are interlocks, not policy, and stay hardware so they take effect in the
cycle STREAM's `scheduler` would take them: a channel reset forces CH_IDLE; a fatal fault -- a descriptor
or engine error, an escalated timeout, or the serving hart halting -- forces CH_ERROR, which drops the
engine valids at once. Every other transition is a firmware command, checked against the edge table of
RAPIDS MAS Section 5.2.

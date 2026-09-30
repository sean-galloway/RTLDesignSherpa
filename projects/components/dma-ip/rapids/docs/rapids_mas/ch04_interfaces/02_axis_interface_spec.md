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

# AXI-Stream Interface Specification

**Module:** `src_data_path_axis.sv` (source master), `snk_data_path_axis.sv` (sink slave)
**Location:** `projects/components/dma-ip/rapids/rtl/macro/`
**Status:** Implemented
**Last Updated:** 2026-09-30

---

## Overview

RAPIDS has one AXI-Stream master on the source half and one AXI-Stream slave on the sink half. Both carry packed bytes. Unlike RAPIDS Beats, the stream is no longer a train of full beats: each descriptor is one packet, the last beat of a packet may be partial, and `TSTRB` says which byte lanes are valid. The handshake, the width parameters and the monitor tap are those of RAPIDS Beats, see [AXI-Stream Interface Specification](../../rapids_beats_mas/ch04_interfaces/02_axis_interface_spec.md) (shared with RAPIDS Beats). The two data paths are specified in [Source Data Path AXIS](../ch03_macro_blocks/07_src_data_path_axis.md) and [Sink Data Path AXIS](../ch03_macro_blocks/04_snk_data_path_axis.md).

---

## Packet Contract

| Property | Rule |
|----------|------|
| Packet | One descriptor is one packet, ending with `TLAST`. |
| Packing | Bytes are packed from lane 0 upward. The descriptor start offset in memory does not appear on the stream. |
| `TSTRB` | Contiguous from lane 0. All ones on every beat but the last. |
| Partial beat | Only the `TLAST` beat may be partial, carrying the remaining bytes. |
| Packet length | Equals the descriptor length in bytes. |
| Zero length | A zero-length descriptor produces no packet. |

: Table 4.2.1: Packet Contract

---

## Source Master Signals

| Signal | Value |
|--------|-------|
| `m_axis_tdata` | Re-packed bytes from the drain shifter. |
| `m_axis_tstrb` | Low `min(bytes_left, DATA_WIDTH/8)` lanes set. |
| `m_axis_tlast` | Set when the remaining byte count equals the bytes in this beat. |
| `m_axis_tid` | Channel number. |
| `m_axis_tdest` | Channel number. |
| `m_axis_tuser` | Zero. |

: Table 4.2.2: Source Master Signals

The source path pops memory beats and re-packs them, so a stream beat is not tied one to one to a memory beat. The first pop of an offset descriptor only primes the hold register and produces no output unless the packet fits in that single beat. When the last memory beat leaves bytes in the hold register, one extra flush beat carries them.

---

## Sink Slave Signals

| Signal | Use |
|--------|-----|
| `s_axis_tdata` | Payload, shifted into the per-channel hold by the descriptor offset. |
| `s_axis_tstrb` | Valid byte lanes. Only the `TLAST` beat may be partial. |
| `s_axis_tid` | Channel select, low `CIW` bits. |
| `s_axis_tdest`, `s_axis_tuser` | Unused. |
| `s_axis_tlast` | Ends the packet. |
| `s_axis_tready` | Deasserted while the output register is busy, a flush beat is pending, or the selected channel has no packet record. |

: Table 4.2.3: Sink Slave Signals

The sink stalls a packet until the scheduler has issued the record of its descriptor. A packet for a channel whose record queue is empty is not accepted, so no byte enters the SRAM before the destination offset is known. The queue holds four records per channel.

The spill of a shifted beat is held per channel. After `TLAST`, if the hold register still holds bytes, `TREADY` drops for one flush beat that writes them to the SRAM.

---

## Length Check

At `TLAST` the sink compares the bytes received with the length in the head record of the channel. A mismatch sets the sticky per-channel `r_pkt_len_error` bit, which is ORed with the write engine error into `sched_wr_error`. Nothing is padded or dropped silently. The bytes received are counted from the lanes set in `TSTRB` on each beat.

---

**Last Updated:** 2026-09-30

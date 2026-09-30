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

## Byte sink ingress: stream junk in a partial last beat corrupts the channel's next packet

**Status**: RESOLVED 2026-09-30 (strobe mask in `snk_data_path_axis.sv`; regression `test_stale_hold_junk`)

### Description

`snk_data_path_axis` shifts each stream beat up by the descriptor's destination
offset and keeps the bytes that spill past the beat boundary in a per-channel
hold. The shift took `s_axis_tdata` whole, so the non-strobed lanes of a partial
last beat (stream junk) were shifted into the hold as well. When the packet had no
spill, nothing flushed or cleared the hold, and the junk was ORed into the first
memory beat of the next packet on the same channel. The next packet's strobed
lanes then read the OR of its data and the junk.

Found by the byte-RAPIDS perf campaign on the board (a chain such as 203 B at
offset 1) and reproduced in the UART sim harness: an offset-5 packet of 20 B
followed by an offset-0 packet of 40 B on one channel wrote 0xFF into byte 0 of the
second packet.

### Location

`rtl/macro/snk_data_path_axis.sv`, the `w_in_wide` placement term. The source
egress re-packer is not affected: its hold is overwritten, not accumulated.

### Fix

`tdata` is masked by `tstrb` before the shift (`w_in_data_m`), so a non-strobed
lane contributes zero to the hold and to the memory beat.

### Verification

`test_stale_hold_junk` in `snk_data_path_axis_test` (three offset/length pairs,
0xFF in the non-strobed lanes). It fails on all three cases against the unmasked
RTL (second packet byte reads 0xFF) and passes with the mask.

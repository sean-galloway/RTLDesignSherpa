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

## DRAIN_SIZE > 1 drops SOURCE beats (short delivery + CRC mismatch)

**Status**: Active / Investigation

### Description

With `AXI_XFER_CONFIG.DRAIN_SIZE > 1`, the SOURCE path delivers **fewer beats than
requested** to the AXIS egress, then reports the channel idle. The checker sees a
short beat count and a CRC mismatch against the golden model.

Reproduced in the RAPIDS beats characterization harness (`rapids_char_harness`)
with a multi-channel source transfer:

- Config: `RD_XFER_BEATS=8, WR_XFER_BEATS=8, ALLOC_SIZE=16, DRAIN_SIZE=8`,
  4 active channels x 512 beats/channel (2048 total).
- Observed: `o_chk_beat_count_total = 1844` (expected 2048); `ch0/ch2/ch3`
  SOURCE CRC mismatch (`chk != golden`); `src_system_idle = 1` (DUT believes the
  transfer completed). The external egress bus meter corroborates: `sout`
  productive beats froze at 1844.
- With `DRAIN_SIZE=1` the same transfer delivers all 2048 beats, golden-clean.

Roughly ~10% of beats are dropped; the loss is not a clean multiple of
`DRAIN_SIZE`, so this is not a simple final-partial-chunk fencepost.

### Location

Source drain path: `rtl/macro_beats/src_data_path_axis_beats.sv` /
`src_sram_controller*` drain-control + `beats_drain_ctrl`. The drain granularity
(`cfg_drain_size`) governs how many beats are released per drain operation; a
value > 1 loses beats near buffer/transfer boundaries.

### Impact

- SOURCE data loss whenever `DRAIN_SIZE > 1`. SINK path was not observed to drop
  (its `DRAIN_SIZE=8` sim run completed), but should be re-verified.
- No impact at the shipped/characterization setting: both the cocotb harness TB
  (`rapids_char_harness_tb`) and the board campaign (`run_characterization.py`)
  use `DRAIN_SIZE=1`.

### Workaround

Use `DRAIN_SIZE=1` (current default in all RAPIDS char collateral). This does
**not** cost utilization: a `DRAIN_SIZE=8` A/B in sim showed identical AXI/AXIS
utilization, so there is no throughput reason to raise it until the drain-path
boundary handling is fixed.

### Next Steps

1. Trace `beats_drain_ctrl` / `src_sram_controller` drain accounting at
   `DRAIN_SIZE>1` around SRAM wrap and end-of-transfer.
2. Add a directed DV test sweeping `DRAIN_SIZE ∈ {1,2,4,8}` x non-aligned
   transfer sizes to pin the boundary condition.
3. Re-verify the SINK drain path at `DRAIN_SIZE>1`.

### Discovered

2026-07-14, during RAPIDS beats external bus-meter characterization (Nexys A7).

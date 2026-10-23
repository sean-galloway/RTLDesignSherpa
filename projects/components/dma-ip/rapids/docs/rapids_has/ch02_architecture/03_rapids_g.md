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

# rapids-g: Firmware-Sequenced Schedulers

**Status:** Implemented (rapids TASK-034)
**Last Updated:** 2026-10-22

---

rapids-g is a build of RAPIDS in which each half's channel schedulers are sequenced by firmware on one gatling (a barrel RV32I core with one hardware context per channel by default) instead of by a state machine per channel. To software it is RAPIDS: the same register map, the same descriptor format, the same channel states in `CH_STATE`, the same MonBus events, the same network planes. The tops are `rapids_g_top` (AXIS) and `rapids_g_cxs_top` (CXS), with 4 or 8 channels per half.

What changes is where the decisions and the address arithmetic are made. The firmware takes and validates descriptors, follows chains, and computes the EXT row and column run bases; the hardware keeps everything that runs at the engines' rate, and forces CH_IDLE on a channel reset and CH_ERROR on a fatal error in the same cycle as RAPIDS. While a descriptor transfers, the firmware validates the next one waiting for the channel, so the hardware starts it the moment the current one completes.

| | RAPIDS | rapids-g |
|---|---|---|
| Register map, descriptors, channel states | -- | identical |
| Per-descriptor overhead | a few cycles | about 90 clocks at 8 channels, hidden behind the descriptor in flight (Section 6.4) |
| EXT run bases | `stream_run_addr_gen` per channel and direction (64 multipliers at 8 channels) | firmware, by addition |
| Channels | 8 or 16 | 4 or 8 |

: Table 2.3: RAPIDS and rapids-g

Which design to use for a given workload, with the measured tables: Section 6.4. Micro-architecture: RAPIDS MAS Chapter 5.

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

# 16-Channel Register Map

RAPIDS comes in two register-map sizes. The shared Register Map chapter
describes the 8-channel map, which `rapids_top`, `rapids_cxs_top`,
`rapids_8ch_top` and `rapids_8ch_cxs_top` use. `rapids_16ch_top` and
`rapids_16ch_cxs_top` use the 16-channel map. That map is the 8-channel map
with only the channel-count-dependent registers changed:

| Register | 8-channel map | 16-channel map |
|----------|---------------|----------------|
| `CHn_DESC_ADDR_LOW` / `_HIGH` | n = 0..7 at 0x000-0x03C | n = 0..15 at 0x000-0x07C |
| `KICK_ENABLE` | 0x040, `KICK0`..`KICK7` | 0x080, `KICK0`..`KICK15` |
| `CHANNEL_ENABLE`, `CHANNEL_RESET`, `CHANNEL_IDLE`, `DESC_ENGINE_IDLE`, `SCHEDULER_IDLE`, `SCHED_ERROR`, `AXI_RD_COMPLETE`, `AXI_WR_COMPLETE` | one bit per channel, [7:0] | [15:0] |
| `CH_STATE[n]` | n = 0..7 at 0x150 | n = 0..15 at 0x180 |
| `VERSION.NUM_CHANNELS` | 8 | 16 |
| `PERF_CH_SEL.CH_SEL` | [2:0] | [3:0] |
| `RDMON_PERF_CH_OVERFLOW_HI`, `WRMON_PERF_CH_OVERFLOW_HI` | absent | MON +0x1F8 / +0x1FC: channels 8..15 (4 bits each) |

: Register Differences, 8- and 16-Channel Maps

Every other register keeps the name, offset and fields it has in the 8-channel
map. Software that addresses registers by name (the generated
`rtl/rapids_regmap.py` and `rtl/rapids_regmap_16ch.py`) needs no change except
loading the map for its build. Software that hard-codes `KICK_ENABLE` at 0x040
must move it to 0x080.

The 16-channel RDL is derived from the 8-channel one by
`bin/gen_rapids_regs_16ch.py`, never edited by hand. The same script writes
the per-size glue that the shared `rapids_top_base` includes.

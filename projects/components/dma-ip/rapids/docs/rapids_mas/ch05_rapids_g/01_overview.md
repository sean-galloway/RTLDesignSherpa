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

# rapids-g Overview

**Status:** Implemented (rapids TASK-034)
**Last Updated:** 2026-10-22

---

## What rapids-g Is

rapids-g is RAPIDS with its scheduler state machines replaced by firmware. Each half of the core (source and sink) has one gatling, the four-context barrel RV32I core (`projects/components/riscv-ip/gatling-rv32i`), running one firmware image for all of that half's 4, 8 or 16 channels. The firmware makes every decision RAPIDS's state machine makes and does the EXT address arithmetic RAPIDS's `scheduler` does in hardware:

- taking a descriptor, validating it, starting it, finishing it, and following a chain;
- the EXT run bases, `base + ((i0 * stride_0) & wrap_0) + ((i1 * stride_1) & wrap_1)`, computed by repeated addition (gatling has no multiplier) and pushed ahead into a small queue per direction.

Everything that happens at the engines' rate stays hardware: the counters the done strobes decrement, the address advance within a run, the timeouts, the sticky errors, the packet records and the MonBus packets. That hardware is `scheduler_core`, the same module RAPIDS's `scheduler` uses (Section 2.1), so the two designs share one datapath.

rapids-g is register-compatible with RAPIDS: the same register map, the same descriptor format, the same host software, the same network planes.

Two capabilities RAPIDS does not have: the firmware pre-validates the next descriptor while the current one runs, so the hardware starts it the moment the current one completes (Section 5.2); and each half's gatling can read and write its own half's registers -- including the eight per-channel `CH_SCRATCH` bits it shares with the host -- through the host's register command queue (Section 5.3).

## Structure

| Level | rapids | rapids-g | How the -g module is made |
|---|---|---|---|
| fub | `scheduler` = state machine + ceilings + 2 run-base generators + `scheduler_core` | `scheduler_g` = command port + ceilings + base FIFOs + `scheduler_core` | hand-written (`rtl/fub_g/`) |
| macro | `scheduler_group_array` | `scheduler_group_array_g`: the same, with `scheduler_g` and one `rapids_seq_g` | generated |
| macro | `rapids_src`, `rapids_snk`, `rapids_core` | `rapids_src_g`, `rapids_snk_g`, `rapids_core_g` | generated |
| top | `rapids_top_base`, `rapids_top`, `rapids_cxs_top` | `rapids_g_top_base`, `rapids_g_top`, `rapids_g_cxs_top` | generated |
| sequencer | -- | `rapids_seq_g`: gatling + instruction ROM + scratch + window decoder | hand-written (`rtl/macro_g/`) |
| firmware | -- | `rtl/fw_g/sched_g.S` | assembled into `rtl/macro_g/generated/fw/sched_g_fw.svh` |

: Table 5.1.1: rapids and rapids-g, level by level

`bin/gen_rapids_g.py` derives every generated file from the RAPIDS file of the same name (Section 5.4); a change to RAPIDS reaches rapids-g by rerunning it.

## Channels per gatling

By default each hart serves one channel at 4 and 8 channels (`NUM_HARTS` = `NUM_CHANNELS`): 4 or 8 harts, one slot each, every hart issuing one instruction every `NUM_HARTS` clocks. At 16 channels the default is 8 harts with two slots each (channels h and h + 8), measured best overall (Section 5.5; rapids TASK-036); 16 harts x 1 and 4 harts x 4 are also built and tested. `NUM_HARTS` = 4 at 8 channels gives each hart two slots, channels h and h + 4. The generated array refuses any other channel count, and `SHARED_ENGINES` = 0, at elaboration. An 8-channel core therefore has two gatlings, one per half, each sequencing eight schedulers; a 16-channel core has two, each sequencing sixteen.

## What stays hardware, and why

Two transitions are interlocks, not policy, and stay hardware so they take effect in the cycle RAPIDS's `scheduler` would take them:

- a channel reset forces CH_IDLE;
- a fatal fault -- a descriptor, engine or control error, an escalated timeout, or the serving hart halting -- forces CH_ERROR, which drops the engine valids at once.

Every other transition is a firmware command, checked against an edge table (Section 5.2).

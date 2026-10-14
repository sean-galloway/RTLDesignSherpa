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

# l1_fill and l1_drain

**Modules:** `l1_fill.sv`, `l1_drain.sv`
**Location:** `projects/components/cache-ip/common-ip/rtl/fub/`
**Status:** RTL landed; this chapter is the micro-architecture contract the RTL implements.

---

## l1_fill

### Purpose

`l1_fill` issues whole-line read bursts to the memory-side master and forwards received beats to `l1_data_array` port A and to the pending-fill bypass register.

### Interface

| Signal | Direction | Meaning |
|--------|-----------|---------|
| `fill_start` | input from `l1_control` | Launch a fill for `fill_addr`. |
| `fill_addr` | input from `l1_control` | Line-aligned address. |
| `fill_done` | output to `l1_control` | All beats received (RLAST accepted). |
| `fill_beat_valid` | output to `l1_control` / data array | A fill beat is valid this cycle. |
| `fill_beat_data` | output | Fill beat data. |
| `fill_beat_idx` | output | Beat index within line. |
| `fill_last` | output | Last beat of burst. |

### Burst parameters

- `ARLEN = FILL_BEATS - 1`
- `ARSIZE = log2(BUS_WIDTH/8)`
- `ARBURST = INCR`
- `ARADDR` line-aligned

### Timing

1. `fill_start` asserted in `CTRL_MISS_FILL`.
2. `l1_fill` asserts `fub_axi_arvalid` to the memory-side read master.
3. As R beats arrive, `fill_beat_valid` pulses; `fill_beat_idx` increments.
4. Each beat is written to `l1_data_array` port A and the `pf_data_valid` mask is updated.
5. On `RLAST` acceptance, `fill_done` pulses for one cycle.

---

## l1_drain

### Purpose

`l1_drain` takes a dirty line from `l1_victim` and issues a whole-line write-back burst to the memory-side write master.

### Interface

| Signal | Direction | Meaning |
|--------|-----------|---------|
| `drain_start` | input from `l1_control` | Launch drain from `l1_victim`. |
| `drain_done` | output to `l1_control` | B response received. |
| `drain_beat_ready` | input from memory master | W-channel ready. |
| `drain_beat_valid` | output | W-channel valid. |
| `drain_beat_data` | output | W-channel data. |
| `drain_beat_strb` | output | W-channel strobe (all-1s for whole-line). |
| `drain_beat_last` | output | W-channel last. |

### Burst parameters

- `AWLEN = FILL_BEATS - 1`
- `AWSIZE = log2(BUS_WIDTH/8)`
- `AWBURST = INCR`
- `AWADDR = victim_addr`
- `WSTRB = all-1s` for every beat

### Timing

1. `drain_start` asserted in `CTRL_MISS_DRAIN` when `l1_victim` is valid.
2. `l1_drain` asserts `fub_axi_awvalid` and begins driving W beats as the master accepts them.
3. After `WLAST` is accepted and the B response arrives, `drain_done` pulses.

### On the onyx rig

For `amber_ace_top`, dirty evictions are issued as `WriteBack` transactions. `amber_ace_issue` supplies `AWSNOOP` and the AW address; `l1_drain` supplies the W beats. Clean evictions are `Evict` transactions with no data.

---

**Last Updated:** 2026-10-06

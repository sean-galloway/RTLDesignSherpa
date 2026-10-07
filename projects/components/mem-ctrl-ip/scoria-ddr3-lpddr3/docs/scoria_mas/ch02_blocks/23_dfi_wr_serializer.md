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

# DFI Write Serializer (`scoria_dfi_wr_serializer`)

**Module:** `scoria_dfi_wr_serializer.sv`
**Location:** `rtl/fub/`
**Category:** DFI write datapath
**Parent:** `scoria_dfi_layer`
**Status:** implemented

## Purpose

`scoria_dfi_wr_serializer` turns the write-data stream into the DFI write-data pins. On a WR command (`wr_fire_i`), it waits `t_phy_wrlat_i` DFI cycles and then streams one DFI word per cycle from the write-data FIFO onto `dfi_wrdata_o` until the burst's `last` word. The data is pre-staged in the CDC FIFO, so the drive path never stalls once it starts.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `DFI_DATA_WIDTH` | int | — | 128 | DFI data bus width (`DRAM_BEAT_WIDTH * DFI_RATE`) |
| `DFI_RATE` | int | power of 2 | 2 | DFI frequency ratio |
| `DFI_STRB_WIDTH` | int | — | `DFI_DATA_WIDTH/8` | byte-strobe width |
| `DFI_EN_WIDTH` | int | — | `DFI_RATE` | write-enable width |
| `WRLAT_W` | int | — | 8 | `t_phy_wrlat` width |

: Table 2.23.1: `scoria_dfi_wr_serializer` parameters

## Interface

| Signal | Direction | Width | Description |
|---|---|---|---|
| `dfi_clk` | in | 1 | DFI / PHY clock |
| `dfi_rstn` | in | 1 | active-low synchronous reset |
| `t_phy_wrlat_i` | in | `WRLAT_W` | WR command to `dfi_wrdata_en` delay |
| `wr_fire_i` | in | 1 | WR command accepted strobe |
| `wd_valid_i` | in | 1 | write-data FIFO valid |
| `wd_ready_o` | out | 1 | write-data FIFO ready |
| `wd_data_i` | in | `DFI_DATA_WIDTH` | write data |
| `wd_strb_i` | in | `DFI_STRB_WIDTH` | byte strobe |
| `wd_last_i` | in | 1 | last word of burst |
| `dfi_wrdata_o` | out | `DFI_DATA_WIDTH` | DFI write data |
| `dfi_wrdata_en_o` | out | `DFI_EN_WIDTH` | DFI write data enable |
| `dfi_wrdata_mask_o` | out | `DFI_STRB_WIDTH` | DFI write data mask |

: Table 2.23.2: `scoria_dfi_wr_serializer` ports

## Microarchitecture internals

### Stateless multi-burst serializer

The serializer uses a delay line rather than an FSM. `wr_fire_i` shifts into `r_age[PIPE-1:0]`, where `PIPE = MAX_WRLAT + 1 = 32`. A fire matures when it reaches index `t_phy_wrlat_i`; `r_owed` counts matured-but-not-finished bursts. The path drives whenever `r_owed != 0` and the FIFO has a word.

```text
PIPE       = MAX_WRLAT + 1 = 32
w_fired    = {r_age, wr_fire_i}
w_mature   = w_fired[t_phy_wrlat_i]
w_owed_now = r_owed + (w_mature ? 1 : 0)
w_drive    = (w_owed_now != 0) && wd_valid_i
wd_ready_o = w_drive
```

This handles every write cadence by construction: back-to-back bursts mature contiguously, `tCCD`-paced writes mature with the correct bubble, and multiple in-flight writes add to `r_owed` independently.

### Owed-burst accounting

`r_owed` tracks bursts that have matured but have not yet finished. It increments when `w_mature` is true and decrements when a driven word is the last word of its burst:

```text
w_burst_last = w_drive && wd_last_i
r_owed_next  = w_owed_now - (w_burst_last ? 1 : 0)
```

The counter width `OWEDW = 3` is small because the controller rate-matches write commits to the data path; only a few write bursts can be in flight at once. If `r_owed` saturates, the behavior is undefined, but the upstream staging invariant makes saturation unreachable.

### Mask generation

DFI mask is active-high "mask this byte", while the upstream strobe is active-high "write this byte". The conversion is a simple inversion:

```text
dfi_wrdata_mask_o = ~wd_strb_i
```

When `w_drive` is low, both `dfi_wrdata_en_o` and `dfi_wrdata_mask_o` are driven to zero.

## FSM policy

There is no FSM. The serializer is a shift-register delay line plus an owed-burst counter.

## Timing

- Latency from `wr_fire_i` to the first `dfi_wrdata_en_o` assertion is `t_phy_wrlat_i` DFI cycles.
- Each burst then runs one DFI word per cycle with no bubbles until `wd_last_i`.
- The `dfi_wrdata_o` bus is wired straight from `wd_data_i` because the upstream FIFO already holds the full DFI word.

## Notes

- The prior implementation used an FSM that assumed seamless continuation and dropped `tCCD` bubbles, driving write data early (`scoria_dfi_wr_serializer.sv:62-64`). The current delay-line design removes that assumption.
- `MAX_WRLAT = 31` covers the DDR3 write-latency range. A build with a larger programmed `t_phy_wrlat` will see `w_mature` clamped to zero and the write data never driven.
- The write-data FIFO is assumed never empty while `r_owed != 0`; the CDC staged-token invariant and rate-matched commit upstream guarantee this in normal operation.

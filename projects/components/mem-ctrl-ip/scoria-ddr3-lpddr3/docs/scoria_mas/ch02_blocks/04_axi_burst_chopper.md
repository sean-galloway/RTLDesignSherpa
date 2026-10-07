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

# AXI Burst Chopper (`scoria_axi_burst_chopper`)

**Module:** `scoria_axi_burst_chopper.sv`
**Location:** `rtl/fub/`
**Category:** address-channel burst chopper
**Parent:** `scoria_axi4_layer`
**Status:** complete and sim-verified

---

## Purpose

The AXI burst chopper splits one host AXI address-channel command into N sub-commands, each no longer than one DRAM burst. The downstream intakes assume one AXI burst equals one DFI burst, so this block is the request-side guarantee: every sub-command that leaves the chopper has at most `AXI_BEATS_PER_BURST` beats and steps to the next `AXI_BURST_BYTES`-aligned boundary.

The module is generic over AW and AR. The write path instantiates it with `PAD_TO_CHUNK=1` so short sub-commands are declared full-length and padded upstream by `scoria_wr_splitter`. The read path uses `PAD_TO_CHUNK=0`; short reads keep their true length because the R-channel framing follows AR.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `AXI_ID_WIDTH` | int | — | 8 | AXI ID width |
| `AXI_ADDR_WIDTH` | int | — | 32 | AXI address width |
| `AXI_USER_WIDTH` | int | — | 1 | AXI USER width |
| `STRB_BYTES` | int | — | 8 | Bytes per AXI beat (`AXI_DATA_WIDTH/8`) |
| `AXI_BEATS_PER_BURST` | int | power of 2, >= 1 | 1 | AXI beats per DFI burst |
| `PAD_TO_CHUNK` | int | 0..1 | 0 | 1 = declare every sub-command as a full `AXI_BEATS_PER_BURST` beats |

: Table 2.4.1: AXI burst chopper parameters

`AXI_BEATS_PER_BURST` must be a power of two; an initial assertion enforces this. The module derives `AXI_BURST_BYTES = AXI_BEATS_PER_BURST * STRB_BYTES` for address stepping.

## Interface

### Host address channel in

| Signal | Direction | Width | Description |
|---|---|---|---|
| `fub_axid` | in | `AXI_ID_WIDTH` | AXI ID |
| `fub_axaddr` | in | `AXI_ADDR_WIDTH` | AXI address |
| `fub_axlen` | in | 8 | burst length (beats - 1) |
| `fub_axsize` | in | 3 | burst size |
| `fub_axburst` | in | 2 | burst type |
| `fub_axlock` | in | 1 | lock signal |
| `fub_axcache` | in | 4 | cache type |
| `fub_axprot` | in | 3 | protection type |
| `fub_axqos` | in | 4 | QoS value |
| `fub_axregion` | in | 4 | region identifier |
| `fub_axuser` | in | `AXI_USER_WIDTH` | user sideband |
| `fub_axvalid` | in | 1 | valid strobe |
| `fub_axready` | out | 1 | ready strobe |

### Sub-command address channel out

| Signal | Direction | Width | Description |
|---|---|---|---|
| `m_axid` | out | `AXI_ID_WIDTH` | sub-command ID |
| `m_axaddr` | out | `AXI_ADDR_WIDTH` | sub-command address |
| `m_axlen` | out | 8 | sub-command length |
| `m_axsize` | out | 3 | sub-command size |
| `m_axburst` | out | 2 | sub-command burst type |
| `m_axlock` | out | 1 | sub-command lock |
| `m_axcache` | out | 4 | sub-command cache |
| `m_axprot` | out | 3 | sub-command protection |
| `m_axqos` | out | 4 | sub-command QoS |
| `m_axregion` | out | 4 | sub-command region |
| `m_axuser` | out | `AXI_USER_WIDTH` | sub-command user sideband |
| `m_axvalid` | out | 1 | sub-command valid |
| `m_axready` | in | 1 | sub-command ready |

### Aggregation sideband

| Signal | Direction | Width | Description |
|---|---|---|---|
| `m_ax_agg` | out | 1 | high when the host command splits into more than one sub |
| `m_ax_last` | out | 1 | high on the final sub-command of the host burst |

: Table 2.4.2: AXI burst chopper interface

`m_ax_agg` is low for a single-sub command and high for every sub of a split. `m_ax_last` is high only on the last sub. The sideband rides with the address through the intake and into the CAM so the response path can collapse per-sub `B`/`RLAST` without a separate counter.

## Microarchitecture internals

The chopper is FSM-free. A single `r_active` bit, a remaining-beat counter, and a running address drive all outputs. The first sub-command is presented combinationally from the host inputs; the host command is accepted when that first sub launches. Subsequent subs are presented from a latched copy while `fub_axready` stays low.

```text
w_total = fub_axlen + 1
w_rem   = w_first ? w_total : r_rem
w_this  = min(w_rem, AXI_BEATS_PER_BURST)
w_addr  = w_first ? fub_axaddr : r_addr
m_axlen = PAD_TO_CHUNK ? AXI_BEATS_PER_BURST - 1 : w_this - 1
m_ax_agg = w_first ? (w_total > AXI_BEATS_PER_BURST) : 1'b1
m_ax_last = (w_rem <= AXI_BEATS_PER_BURST)
fub_axready = w_first && m_axready
```

On each accepted sub-command, `r_rem` decreases by `w_this` and `r_addr` advances by `AXI_BURST_BYTES`. When the last sub is accepted, `r_active` clears and `fub_axready` reopens.

## FSM policy

There is no state machine. The only sequential state is the latched command and the running remainder/address. All output muxing is combinational.

## Timing

The first sub-command is valid in the same cycle `fub_axvalid` is high. The critical path is the host input through the remainder calculation and address mux to `m_axvalid`/`m_axready`. Each subsequent sub-command is accepted one cycle after `m_axready` (registered advance). The host is back-pressured for the drain interval.

## Notes

- **PAD_TO_CHUNK asymmetry:** The write side sets `PAD_TO_CHUNK=1` and relies on `scoria_wr_splitter` to inject zero-strobe filler beats. The read side sets `PAD_TO_CHUNK=0`; short reads need no padding because `RLAST` follows the real beat count.
- **Ragged but legal:** The chopper handles any host `AxLEN`, including bursts that are not a multiple of `AXI_BEATS_PER_BURST`. In scoria's normal path, ragged writes are padded by the splitter and ragged reads are rejected downstream; the chopper itself remains general.
- **Power-of-two assertion:** `initial assert (AXI_BEATS_PER_BURST >= 1 && power-of-2)` fires at elaboration if the parameter is mis-set.

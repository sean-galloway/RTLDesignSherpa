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

# Write Splitter (`scoria_wr_splitter`)

**Module:** `scoria_wr_splitter.sv`
**Location:** `rtl/fub/`
**Category:** AXI write request reframer
**Parent:** `scoria_axi4_layer`
**Status:** complete and sim-verified

---

## Purpose

The write splitter sits between the host AXI write channel and `scoria_wr_intake`. It chops AW into DFI-burst-sized sub-commands and reframes the W stream so each sub-command receives exactly one `WLAST` on an `AXI_BEATS_PER_BURST` boundary. This is purely a request-side transform; B responses are consolidated later, on the return path.

The key change from the old shared `axi_master_wr_splitter` is that `WLAST` is regenerated from the W handshake, not from an AW-side beat budget. The previous scheme lost framing for narrow bursts that split into many single-beat DRAM bursts, leaving most sub-bursts without a `WLAST` and stalling the write-data CAM. Counting the W stream directly fixes that for any `AXI_BEATS_PER_BURST`, including one.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `AXI_ID_WIDTH` | int | — | 8 | AXI ID width |
| `AXI_ADDR_WIDTH` | int | — | 32 | AXI address width |
| `AXI_DATA_WIDTH` | int | — | 64 | AXI data width |
| `AXI_USER_WIDTH` | int | — | 1 | AXI USER width |
| `AXI_BEATS_PER_BURST` | int | power of 2, >= 1 | 1 | AXI beats per DFI burst |

: Table 2.5.1: Write splitter parameters

The derived widths `IW`, `AW`, `DW`, `UW`, and `SW` (`AXI_DATA_WIDTH/8`) are local only.

## Interface

### Host AXI write in

| Signal | Direction | Width | Description |
|---|---|---|---|
| `fub_awid` | in | `AXI_ID_WIDTH` | host AW ID |
| `fub_awaddr` | in | `AXI_ADDR_WIDTH` | host AW address |
| `fub_awlen` | in | 8 | host AW length |
| `fub_awsize` | in | 3 | host AW size |
| `fub_awburst` | in | 2 | host AW burst type |
| `fub_awlock` | in | 1 | host AW lock |
| `fub_awcache` | in | 4 | host AW cache |
| `fub_awprot` | in | 3 | host AW protection |
| `fub_awqos` | in | 4 | host AW QoS |
| `fub_awregion` | in | 4 | host AW region |
| `fub_awuser` | in | `AXI_USER_WIDTH` | host AW user |
| `fub_awvalid` | in | 1 | host AW valid |
| `fub_awready` | out | 1 | host AW ready |
| `fub_wdata` | in | `AXI_DATA_WIDTH` | host W data |
| `fub_wstrb` | in | `AXI_DATA_WIDTH/8` | host W strobe |
| `fub_wlast` | in | 1 | host W last |
| `fub_wuser` | in | `AXI_USER_WIDTH` | host W user |
| `fub_wvalid` | in | 1 | host W valid |
| `fub_wready` | out | 1 | host W ready |

### Sub-command AXI write out

| Signal | Direction | Width | Description |
|---|---|---|---|
| `m_awid` | out | `AXI_ID_WIDTH` | sub-command AW ID |
| `m_awaddr` | out | `AXI_ADDR_WIDTH` | sub-command AW address |
| `m_awlen` | out | 8 | sub-command AW length |
| `m_awsize` | out | 3 | sub-command AW size |
| `m_awburst` | out | 2 | sub-command AW burst type |
| `m_awlock` | out | 1 | sub-command AW lock |
| `m_awcache` | out | 4 | sub-command AW cache |
| `m_awprot` | out | 3 | sub-command AW protection |
| `m_awqos` | out | 4 | sub-command AW QoS |
| `m_awregion` | out | 4 | sub-command AW region |
| `m_awuser` | out | `AXI_USER_WIDTH` | sub-command AW user |
| `m_awvalid` | out | 1 | sub-command AW valid |
| `m_awready` | in | 1 | sub-command AW ready |
| `m_wdata` | out | `AXI_DATA_WIDTH` | sub-command W data |
| `m_wstrb` | out | `AXI_DATA_WIDTH/8` | sub-command W strobe |
| `m_wlast` | out | 1 | regenerated W last |
| `m_wuser` | out | `AXI_USER_WIDTH` | sub-command W user |
| `m_wvalid` | out | 1 | sub-command W valid |
| `m_wready` | in | 1 | sub-command W ready |

### Aggregation sideband

| Signal | Direction | Width | Description |
|---|---|---|---|
| `m_aw_agg` | out | 1 | high when the host AW splits into more than one sub |
| `m_aw_last` | out | 1 | high on the final sub-command |

: Table 2.5.2: Write splitter interface

## Microarchitecture internals

The AW path is an instance of `scoria_axi_burst_chopper` with `PAD_TO_CHUNK=1`. The W path is a down-counter plus padding generator.

`r_wcnt` counts beats until the next regenerated `m_wlast`. It reloads to `AXI_BEATS_PER_BURST-1` on every chunk boundary. `r_pad` holds the number of zero-strobe filler beats owed when the host burst ends mid-chunk.

```text
w_padding   = (r_pad != 0)
w_short_last = fub_wlast && (r_wcnt != 0)

m_wdata  = w_padding ? 0 : fub_wdata
m_wstrb  = w_padding ? 0 : fub_wstrb
m_wuser  = w_padding ? 0 : fub_wuser
m_wvalid = w_padding ? 1 : fub_wvalid
fub_wready = w_padding ? 0 : m_wready
m_wlast  = w_padding ? (r_pad == 1) : (r_wcnt == 0)
```

While padding, the host is held off (`fub_wready=0`) and the splitter emits locally generated filler beats. `m_wstrb=0` becomes `dfi_wrdata_mask_o = ~strb` in the DFI write serializer, so the device clocks the beat but writes nothing.

## FSM policy

The splitter is FSM-free. The AW side inherits the single-bit active state of the burst chopper. The W side uses two counters: `r_wcnt` for chunk framing and `r_pad` for filler insertion.

## Timing

AW and W are decoupled after the split. The W counter advances on `m_wvalid && m_wready`. Padding beats are inserted immediately when the host `WLAST` arrives before a chunk boundary. The first sub-command's AW is valid combinationally with the host `AWVALID`.

## Notes

- **WLAST from W, not AW:** The regenerated `m_wlast` depends only on the W beat counter. This is the fix for narrow x16 BL4 bursts that previously lost framing.
- **Zero-strobe padding:** Short host bursts are padded to the chunk boundary with `strb=0`. Every legal `AxLEN` therefore works, including `AxLEN=0`.
- **PAD_TO_CHUNK=1:** AW sub-commands are always declared as full `AXI_BEATS_PER_BURST` beats because the W stream will supply the data, real or padded.
- **Backpressure during padding:** `fub_wready` is forced low during filler insertion. The host cannot push additional beats until the current chunk completes.

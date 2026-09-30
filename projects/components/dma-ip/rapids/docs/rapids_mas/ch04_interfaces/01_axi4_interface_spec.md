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

# AXI4 Interface Specification

**Module:** `axi_read_engine.sv` (source AXI read master), `axi_write_engine.sv` (sink AXI write master)
**Location:** `projects/components/dma-ip/rapids/rtl/fub/`
**Status:** Implemented
**Last Updated:** 2026-09-30

---

## Overview

RAPIDS drives two AXI4 masters: a read master on the source half and a write master on the sink half. The channel signals, the outstanding-transaction limits and the response handling are those of RAPIDS Beats and are specified in [AXI4 Interface Specification](../../rapids_beats_mas/ch04_interfaces/01_axi4_interface_spec.md) (shared with RAPIDS Beats). This chapter records only what the byte-granular design adds.

The AXI side stays beat-oriented. Every burst starts at a beat-aligned address and moves whole beats. A descriptor that starts or ends inside a beat is handled by the byte lanes of the data path, not by narrow AXI transfers. Both engines are specified in [AXI Read Engine](../ch02_fub_blocks/03_axi_read_engine.md) and [AXI Write Engine](../ch02_fub_blocks/04_axi_write_engine.md).

---

## Byte Address to Beat Mapping

The scheduler splits a byte address into a beat address and a byte offset. `OFF_W` is `$clog2(DATA_WIDTH/8)`, which is 5 for the 256-bit board build.

| Quantity | Value |
|----------|-------|
| Offset | `addr[OFF_W-1:0]` |
| First beat address | `addr` with the low `OFF_W` bits cleared |
| Beats for a descriptor | `(offset + length + lanes - 1) >> OFF_W`, zero for zero length |

: Table 4.1.1: Address Split

The engines receive the working byte address and the remaining beat count. `ARADDR` and `AWADDR` are driven with the low `OFF_W` bits at zero, so every burst is beat-aligned.

---

## Burst Rules

| Rule | Read master | Write master |
|------|-------------|--------------|
| Burst start | beat-aligned | beat-aligned |
| Burst size | full bus width | full bus width |
| 4 KB boundary | no burst crosses one | no burst crosses one |
| Burst cap | smaller of the configured burst and the beats left to the 4 KB boundary | same |

: Table 4.1.2: Burst Rules

The number of beats left to the boundary is computed from the beat-aligned address, so a byte offset never lets a burst run past it.

---

## Write Strobes

The write master carries a byte enable with every beat. The data path stores the strobe next to the data in the sink SRAM, and the write engine drives it onto `WSTRB`. Interior beats of a packet are fully strobed. The first beat and the last beat of a descriptor that start or end inside a beat carry a partial strobe, so only the bytes of the descriptor are written and neighbouring bytes in memory are untouched.

The read master has no byte enables. It always reads whole beats and the source data path discards the bytes outside the descriptor.

| Signal | Width | Meaning |
|--------|-------|---------|
| `m_axi_wstrb` | `DATA_WIDTH/8` | Byte lanes written by the beat, from the stored strobe. |

: Table 4.1.3: Byte-Granular Write Signal

---

## Limitations

- TYPE=EXT descriptors remain beat-aligned in address and length. This is a permanent limitation.
- A descriptor never issues a narrow AXI transfer. Sub-beat behavior is entirely in the strobes.

---

**Last Updated:** 2026-09-30

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

# AMBA Clock Domain Crossing

**RTL:** `rtl/amba/cdc/`
**Filelists:** `rtl/amba/filelists/cdc_*.f`

CDC documentation is consolidated into a single reference:

## → [Clock Domain Crossing (cdc.md)](cdc.md)

It covers the decision guide, the reset behavior that separates the techniques,
and every building block. The per-module pages that used to live in this
directory (`cdc_primer`, `cdc_synchronizer`, `cdc_open_loop`,
`cdc_2_phase_handshake`, `cdc_4_phase_handshake`) were merged into it; their
content is now sections of that one document.

| Jump to | Covers |
|---------|--------|
| [Choosing a technique](cdc.md#choosing-a-technique) | Decision tree and quick-reference table |
| [Reset Considerations](cdc.md#reset-considerations) | Why encoding decides reset safety; the 2-phase hazard, with waveforms and silicon evidence |
| [cdc_synchronizer](cdc.md#cdc_synchronizer) | N-stage synchronizer for quasi-static signals |
| [cdc_open_loop](cdc.md#cdc_open_loop) | Source holds data + valid, no acknowledge |
| [cdc_2_phase_handshake](cdc.md#cdc_2_phase_handshake) | Toggle (NRZ) valid/ready handshake |
| [cdc_4_phase_handshake](cdc.md#cdc_4_phase_handshake) | Level (RZ) valid/ready handshake |
| [Async FIFO pointers](cdc.md#async-fifo-pointers-gray-and-johnson) | Gray vs Johnson, depth sizing, the 512-bit walkthrough |

---

**Before choosing a handshake:** if the two clock domains can be reset
independently -- a soft reset, a per-block reset, or separate power domains --
`cdc_2_phase_handshake` will fabricate a transfer out of an idle link. See
[Reset Considerations](cdc.md#reset-considerations).

---

## Navigation

- [Back to RTLAmba Index](../index.md)
- [AMBA Shared Infrastructure](../shared/README.md)

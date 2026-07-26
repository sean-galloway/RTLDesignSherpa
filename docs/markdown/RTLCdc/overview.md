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

# Clock Domain Crossing

**RTL:** `rtl/cdc/` (12 modules)
**Filelists:** `rtl/cdc/filelists/` -- lint the area with `cdc_all.f`
**Tests:** `val/cdc/`

Everything whose job is getting data safely across a clock boundary lives here:
the synchronizer, the handshakes, the asynchronous FIFOs, and the Gray and
Johnson coders that exist to make those crossings safe. Modules that merely
*use* these -- `fifo_control`, `counter_bin`, `glitch_free_n_dff_arn` -- stay in
`rtl/common`, because they serve FIFOs generally and not just crossings.

**Full catalogue:** [index.md](index.md)

## Start here

The single reference for choosing and using a technique is
[Clock Domain Crossing (cdc.md)](cdc.md). It covers the decision guide, the
reset behavior that separates the techniques, and every building block. The
per-module pages that used to exist for `cdc_primer`, `cdc_synchronizer`,
`cdc_open_loop`, `cdc_2_phase_handshake` and `cdc_4_phase_handshake` were merged
into it -- their content is now sections of that one document.

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

## How the pieces fit

A crossing is a choice about what the receiver needs, not about how many flops
you can afford:

- **A quasi-static value or a single flag** -- one that holds still long enough
  for the far side to sample it -- takes `cdc_synchronizer`. Nothing more.
- **A multi-bit value that changes as a unit** cannot use a plain synchronizer:
  the bits land in different cycles and the receiver sees a value that never
  existed. Gray-code it (`bin2gray` / `gray2bin`, or `counter_bingray` if it is
  a counter), or push it through a handshake or FIFO.
- **A transfer that needs acknowledgement** takes a handshake -- 2-phase for
  throughput, 4-phase when the reset story matters. Read the reset section
  before picking.
- **A stream** takes an asynchronous FIFO: `fifo_async` for plain data, or
  `gaxi_fifo_async` / `gaxi_skid_buffer_async` on a GAXI interface. Both pointer
  encodings are a parameter (`USE_JOHNSON`), not separate modules -- Gray needs
  a power-of-2 depth, Johnson takes any depth.

## Navigation

- [Catalogue of every module in this area](index.md)
- [Back to the documentation index](../index.md)
- [RTLCommon](../RTLCommon/index.md) -- the shared building blocks these use
- [RTLAmba](../RTLAmba/index.md) -- the protocol layers that consume them

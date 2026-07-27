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


# rtl-cdc Modules Index

This is the catalogue for `rtl/cdc/`. If you want orientation—which technique
to reach for, and why—start at [overview.md](overview.md).

**12 modules** in `rtl/cdc/`, and every one of them exists to get data across a
clock boundary. The count comes from `ls rtl/cdc/*.sv`—regenerate it rather
than hand-editing.

## Module Categories

| Category | Count |
|---|---|
| Synchronizer & handshakes | 4 |
| Gray / Johnson coders | 5 |
| Asynchronous FIFOs | 3 |

### Synchronizer and Handshakes

These four share one reference page instead of getting a page each, because
choosing between them is a single decision:

- **[cdc_synchronizer](cdc.md#cdc_synchronizer)** - N-stage flop synchronizer for a
  quasi-static value or a single flag
- **[cdc_open_loop](cdc.md#cdc_open_loop)** - source holds data and valid; no
  acknowledge comes back
- **[cdc_2_phase_handshake](cdc.md#cdc_2_phase_handshake)** - toggle (NRZ)
  valid/ready handshake. Read [Reset Considerations](cdc.md#reset-considerations)
  first: it will fabricate a transfer if the domains can reset independently
- **[cdc_4_phase_handshake](cdc.md#cdc_4_phase_handshake)** - level (RZ)
  valid/ready handshake

### Gray and Johnson Coders

These are the encodings that make a multi-bit crossing safe—only one bit
changes per step, so a mid-flight sample still lands on a value that actually
existed:

- **[bin2gray](bin2gray.md)** - binary to Gray code
- **[gray2bin](gray2bin.md)** - Gray code back to binary
- **[johnson2bin](johnson2bin.md)** - Johnson (twisted-ring) code to binary
- **[counter_bingray](counter_bingray.md)** - counter emitting binary and Gray together
- **[counter_johnson](counter_johnson.md)** - Johnson counter

### Asynchronous FIFOs

- **[fifo_async](fifo_async.md)** - asynchronous FIFO; `USE_JOHNSON` selects the
  pointer encoding (Gray needs a power-of-2 depth, Johnson takes any depth)
- **[gaxi_fifo_async](gaxi_fifo_async.md)** - the same crossing behind a GAXI
  valid/ready interface
- **[gaxi_skid_buffer_async](gaxi_skid_buffer_async.md)** - GAXI async FIFO with a
  skid buffer on each side

## Related

The modules these depend on stay in their own areas and get pulled in by `-f`
include—they're not copied here:

- [`glitch_free_n_dff_arn`](../rtl-common/glitch_free_n_dff_arn.md),
  [`fifo_control`](../rtl-common/fifo_control.md),
  [`counter_bin`](../rtl-common/counter_bin.md),
  [`find_first_set`](../rtl-common/find_first_set.md),
  [`find_last_set`](../rtl-common/find_last_set.md),
  [`leading_one_trailing_one`](../rtl-common/leading_one_trailing_one.md) -
  [rtl-common](../rtl-common/index.md). The three bit-search modules arrive
  through `johnson2bin`, which uses them to decode a Johnson pointer.
- [`gaxi_skid_buffer`](../rtl-amba/gaxi/gaxi_skid_buffer.md) - [rtl-amba](../rtl-amba/index.md)

The APB/APB5 CDC slaves that consume this area live with their protocol
documentation: [apb_slave_cdc](../rtl-amba/apb/apb_slave_cdc.md),
[apb5_slave_cdc](../rtl-amba/apb5/apb5_slave_cdc.md).

## Navigation

- **[Overview and decision guide](overview.md)**
- **[Back to Main Documentation Index](../index.md)**

<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> &middot; <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# CDC Synchronizer

**Module:** `cdc_synchronizer.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

Multi-bit synchronizer for clock domain crossing. Wraps the `glitch_free_n_dff_arn` primitive with a consistent naming interface for the AMBA infrastructure.

Suitable for quasi-static signals that change infrequently relative to the destination clock (configuration registers, status flags, level indicators). NOT suitable for pulse transfers or streaming data -- use `sync_pulse` or async FIFOs for those.

### Key Features

- Parameterizable bus width (1 to N bits)
- Configurable synchronizer depth (2-5 stages, default 3)
- Uses `glitch_free_n_dff_arn` internally for ASYNC_REG attributes
- Zero additional logic -- pure flop chain

---

## Module Interface

```systemverilog
module cdc_synchronizer #(
    parameter int WIDTH      = 1,   // Bus width to synchronize
    parameter int FLOP_COUNT = 3    // Number of synchronizer stages (2-5)
) (
    input  logic             clk,       // Destination clock
    input  logic             rst_n,     // Asynchronous active-low reset
    input  logic [WIDTH-1:0] async_in,  // Asynchronous input from source domain
    output logic [WIDTH-1:0] sync_out   // Synchronized output in destination domain
);
```

## Parameters

| Parameter | Default | Range | Description |
|-----------|---------|-------|-------------|
| `WIDTH` | 1 | 1+ | Number of bits to synchronize |
| `FLOP_COUNT` | 3 | 2-5 | Synchronizer chain depth (stages) |

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk` | input | 1 | Destination domain clock |
| `rst_n` | input | 1 | Asynchronous active-low reset |
| `async_in` | input | WIDTH | Input signal from source clock domain |
| `sync_out` | output | WIDTH | Synchronized output in destination domain |

---

## Usage Guidelines

- Input must be quasi-static: stable for at least `FLOP_COUNT + 1` destination clock cycles before being sampled
- For multi-bit buses, ALL bits must change simultaneously or use Gray coding
- Use `FLOP_COUNT=2` for relaxed MTBF, `FLOP_COUNT=3` for production (default)
- Do NOT use for pulse signals -- use `sync_pulse` instead
- Do NOT use for streaming data -- use `fifo_async` or `gaxi_fifo_async`

## Instantiation Example

```systemverilog
cdc_synchronizer #(
    .WIDTH      (4),
    .FLOP_COUNT (3)
) u_status_sync (
    .clk      (dest_clk),
    .rst_n    (dest_rst_n),
    .async_in (src_status),
    .sync_out (synced_status)
);
```

---

## Resources

- RTL: `rtl/amba/shared/cdc_synchronizer.sv`
- Primitive: `rtl/common/glitch_free_n_dff_arn.sv`
- Formal: `formal/amba/cdc_synchronizer/`
- Related: `sync_pulse.sv` (pulse crossing), `cdc_2_phase_handshake.sv` (data + handshake)

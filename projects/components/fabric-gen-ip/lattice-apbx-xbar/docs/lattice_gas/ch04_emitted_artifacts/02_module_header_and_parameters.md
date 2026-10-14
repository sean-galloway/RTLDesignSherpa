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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Module Header and Parameters

Every generated file begins with the standard RTL Design Sherpa banner and includes `reset_defs.svh`.

```systemverilog
// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa ...
//
// Module: apbx_xbar_2to4
// Purpose: Apbx Xbar 2to4 module
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps
`include "reset_defs.svh"
```

## Address-map comment

Immediately before the module declaration, the generator emits a comment block documenting the slave map:

```systemverilog
//   Slave 0: [0x10000000, 0x1000FFFF] (64KB)
//   Slave 1: [0x10010000, 0x1001FFFF] (64KB)
//   ...
```

This comment is derived from `base_addr` and `slave_size` and is the authoritative map for integrators.

## Port naming convention

| Direction | Naming |
|-----------|--------|
| Master-side inputs | `m<N>_apb_<signal>` |
| Master-side outputs | `m<N>_apb_<signal>` |
| Slave-side outputs | `s<N>_apb_<signal>` |
| Slave-side inputs | `s<N>_apb_<signal>` |

: Generated Port Naming Convention

Parity error outputs (APB5 with parity) use `m<N>_parity_error_wdata` / `m<N>_parity_error_ctrl` on the master side and `s<N>_parity_error_rdata` / `s<N>_parity_error_ctrl` on the slave side.

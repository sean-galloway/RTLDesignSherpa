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

# APB CSR Slave

The controller exposes an APB3 slave port for configuration and observation.

## Signals

| Signal       | Width | Direction | Notes                                  |
|--------------|-------|-----------|----------------------------------------|
| `apb_pclk`   | 1     | input     | APB bus clock (independent of mc_clk)  |
| `apb_presetn`| 1     | input     | APB reset (active low)                 |
| `psel`       | 1     | input     | Slave selected                         |
| `penable`    | 1     | input     | Access phase 2                         |
| `pwrite`     | 1     | input     | Write (1) or read (0)                  |
| `paddr`      | 12    | input     | 4 KB address space                     |
| `pwdata`     | 32    | input     | Write data                             |
| `prdata`     | 32    | output    | Read data                              |
| `pready`     | 1     | output    | Slave ready                            |
| `pslverr`    | 1     | output    | Error response                         |

## APB3 Conformance

Standard APB3 — single-cycle accesses for the typical case, multi-cycle for observation-counter reads (which require CDC).

## Error Behavior

`pslverr` is asserted in these cases:

- Write to a read-only register (e.g., `STATUS`)
- Read from a write-only register (none defined in v1)
- Access to an unimplemented address (any address not listed in the register map)

Errors do not affect controller state — the APB transaction simply terminates with `pslverr = 1`.

## Clock Domain Crossing

The CSR slave operates on `apb_pclk`, independent of `mc_clk`. A 2-flop synchronizer handshake transfers configuration writes into the `mc_clk` domain. The handshake guarantees atomic register update from the controller's perspective.

Observation reads use a parallel CDC mechanism: snapshot the live counter in the `mc_clk` domain, then transfer to `apb_pclk`. `pready` deasserts during the transfer (typically 2 `apb_pclk` cycles).

## Register Map

The full address map is documented in Section 6.3.

## Configuration Sequencing

See `csr_slave` description in §3.8 for the recommended programming sequence:

1. Hold `mc_rstn` asserted
2. Program timing parameters and MR values
3. Configure PASR mask (LPDDR2)
4. Configure characterization parameters
5. Release `mc_rstn`
6. Wait for `STATUS.init_done`
7. Begin AXI traffic

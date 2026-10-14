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

# cmd/rsp Fabric

Between the APB boundary modules, the generated module implements a command/response fabric with the following signals per master and per slave:

| Signal | Direction from master-side | Width | Meaning |
|--------|---------------------------|-------|---------|
| `cmd_valid` | master → fabric | 1 | Command available. |
| `cmd_ready` | fabric → master | 1 | Command accepted. |
| `cmd_pwrite` | master → fabric | 1 | Write (1) or read (0). |
| `cmd_paddr` | master → fabric | `ADDR_WIDTH` | Address. |
| `cmd_pwdata` | master → fabric | `DATA_WIDTH` | Write data. |
| `cmd_pstrb` | master → fabric | `STRB_WIDTH` | Byte strobe. |
| `cmd_pprot` | master → fabric | 3 | Protection. |
| `cmd_pauser` | master → fabric | 1 | APB5 sideband (only on APB5 master). |
| `cmd_pwuser` | master → fabric | 1 | APB5 sideband (only on APB5 master). |
| `rsp_valid` | fabric → master | 1 | Response available. |
| `rsp_ready` | master → fabric | 1 | Response accepted. |
| `rsp_prdata` | fabric → master | `DATA_WIDTH` | Read data. |
| `rsp_pslverr` | fabric → master | 1 | Slave error. |
| `rsp_pruser` | fabric → master | 1 | APB5 sideband (only on APB5 master). |
| `rsp_pbuser` | fabric → master | 1 | APB5 sideband (only on APB5 master). |

: cmd/rsp Fabric Signals

The slave-side cmd/rsp signals have the same names and directions reversed relative to the slave-side APB master modules.

## Fabric width invariance

The cmd/rsp width is fixed regardless of mixed APB4/APB5 ports. APB4 ports simply do not drive or receive the sideband signals; APB4 slaves tie them to zero and APB4 masters ignore them. This avoids parameterized struct widths inside the fabric.

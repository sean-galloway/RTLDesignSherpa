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

# Boundary Module Instantiation

The generated module instantiates proven boundary modules from the `rtl/common/` and `rtl/amba/` libraries rather than reimplementing APB protocol logic inline.

## Master-side modules

For each master `m`:

- `apb4_slave` when `master_versions[m] == 'apb4'`.
- `apb5_slave` when `master_versions[m] == 'apb5'`.

Parameterization:

```systemverilog
apb4_slave #(
    .ADDR_WIDTH(ADDR_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .STRB_WIDTH(STRB_WIDTH),
    .PROT_WIDTH(3)
) u_apb4_slave_m0 (...);
```

APB5 variants add user widths of 1 and, when parity is enabled, `ENABLE_PARITY=1`.

## Slave-side modules

For each slave `s`:

- `apb4_master` when `slave_versions[s] == 'apb4'`.
- `apb5_master` when `slave_versions[s] == 'apb5'`.

The same width and sideband parameter rules apply.

## Parity tie-offs

When parity is disabled on an APB5 port, the `*CHK` input pins are tied to zero and the `*CHK` output and `parity_error_*` pins are left unconnected. This lets the same `apb5_slave`/`apb5_master` modules be reused with or without parity without conditional module selection.

## PWAKEUP wiring

An APB5 master port's `PWAKEUP` input goes to the `apb5_slave` boundary IP, which uses it only for the `PWAKEUPCHK` check. Each `apb5_master` boundary IP drives its own registered wake onto an internal net, `w_s<s>_ip_pwakeup`. The generator then emits `assign s<s>_apb_PWAKEUP = w_s<s>_ip_pwakeup | m<i>_apb_PWAKEUP ...`, with one term for every APB5 master. With parity on, it also emits `assign s<s>_apb_PWAKEUPCHK = ~s<s>_apb_PWAKEUP`. The IP's own `m_apb_PWAKEUPCHK` is left unconnected, because it covers only the IP's term.

## 1×1 passthrough

When `num_masters == 1` and `num_slaves == 1`, the fabric reduces to simple `assign` statements between the single master-side and single slave-side cmd/rsp nets. No arbiter is instantiated.

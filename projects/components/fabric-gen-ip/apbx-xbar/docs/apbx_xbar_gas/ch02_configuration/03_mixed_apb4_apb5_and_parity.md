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

# Mixed APB4/APB5 and Parity

The generator supports mixed-version ports: any master or slave can be declared APB4 or APB5 independently. The feature is controlled entirely by the `master_versions` and `slave_versions` lists.

## Version list rules

- Each list has length `num_masters` or `num_slaves`.
- Valid values are `'apb4'` or `'apb5'`.
- APB4 ports expose the classic PSEL/PENABLE/PADDR/PWRITE/PWDATA/PSTRB/PPROT/PRDATA/PSLVERR/PREADY set.
- APB5 ports add `PAUSER`, `PWUSER`, `PWAKEUP`, `PRUSER`, and `PBUSER`.

## Mixed-port sideband behavior

The cmd/rsp fabric between boundary modules is where the protocol conversion happens. Sideband signals are carried only when **both** the source master and the target slave are APB5:

- If the source master is APB5 but the selected slave is APB4, `cmd_pauser` and `cmd_pwuser` are dropped at the slave-side APB4 master.
- If the source master is APB4 but the selected slave is APB5, the APB5 master ties `cmd_pauser` and `cmd_pwuser` to zero.
- Response sideband (`pruser`, `pbuser`) follows the same rule in reverse.

This keeps the fabric simple: there is one cmd/rsp width per direction, and the boundary modules handle expansion or zero-padding.

## Parity (`enable_parity=True`)

APB5 parity is optional and independent of the version lists. It may only be enabled when the corresponding port is APB5; the generator emits APB5 parity pins only on APB5 interfaces.

| Pin group | Checked at | Regenerated at |
|-----------|------------|----------------|
| Write data parity (`PWDATAPARITY`) | master-side `apb5_slave` | slave-side `apb5_master` |
| Address parity (`PADDRPARITY`) | master-side `apb5_slave` | slave-side `apb5_master` |
| Control parity (`PCTRLPARITY`) | master-side `apb5_slave` | slave-side `apb5_master` |
| Read data parity (`PRDATAPARITY`) | slave-side `apb5_master` | master-side `apb5_slave` |
| Ready parity (`PREADYPARITY`) | slave-side `apb5_master` | master-side `apb5_slave` |
| Slave-error parity (`PSLVERRPARITY`) | slave-side `apb5_master` | master-side `apb5_slave` |

Parity does **not** cross the cmd/rsp fabric. The boundary IP deconstructs the APB transfer, checks parity at entry, and regenerates it at exit. Each APB5 port exposes its own `parity_error_wdata` and `parity_error_ctrl` outputs so a fabric fault is distinguishable from a slave's own `PSLVERR` response.

The shipped `apbx_xbar_2to2_mixed` variant uses APB5 without parity. Parity is reserved for custom subsystems that explicitly request it.

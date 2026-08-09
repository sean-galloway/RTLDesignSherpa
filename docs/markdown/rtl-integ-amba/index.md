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


# rtl-integ-amba Modules Index

The catalogue for `rtl/integ_amba/`. For the monitoring pattern these are meant
to demonstrate -- and why the RTL currently does not build -- start at
[overview.md](overview.md).

**2 modules** in `rtl/integ_amba/examples/`. Count is from
`ls rtl/integ_amba/examples/*.sv`; regenerate rather than hand-editing.

> Both currently fail to elaborate (AMBA-INTEG-EXAMPLES). The pages below are
> baseline documentation of intent and interface, not a claim that the RTL works.

## Monitored APB fabrics

- **[apb_peripheral_subsystem](apb_peripheral_subsystem.md)** - one APB master
  fanned out to three peripherals (regfile / timer / GPIO), each with its own
  monitor, and the monitor buses arbitrated onto one 64-bit monbus output
- **[apb_xbar_monitored](apb_xbar_monitored.md)** - `apb_xbar_thin` with a
  monitor on every master and slave port, agent-ID tagged per port

## Related

- [apb4_monitor](../rtl-amba/apb4/apb4_monitor.md) - the observer both examples
  attach; takes the `cmd_*`/`rsp_*` handshake, not raw APB
- [apb4_slave](../rtl-amba/apb4/apb4_slave.md), [apb4_master](../rtl-amba/apb4/apb4_master.md)
  - the bridges that translate the wire into that handshake
- [arbiter_round_robin](../rtl-common/arbiter_round_robin.md) - fair arbitration
  over the per-port monitor buses
- `apb_xbar_thin` lives in `projects/components/apb_xbar`, so
  `apb_xbar_monitored` depends on a project area from under `rtl/` -- a backwards
  dependency, noted in its filelist

## Navigation

- **[Overview and the monitoring pattern](overview.md)**
- **[Back to Main Documentation Index](../index.md)**

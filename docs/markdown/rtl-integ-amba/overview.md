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


# rtl-integ-amba Overview

**RTL:** `rtl/integ_amba/examples/` (2 modules)
**Filelists:** `rtl/integ_amba/filelists/` -- lint the area with `integ_amba_all.f`
**Tests:** none yet

Integration examples on the AMBA side: how you attach monitoring to an APB
fabric. Neither is a library module -- each wires existing blocks together to
show a pattern.

**Full catalogue:** [index.md](index.md)

> **Both examples currently fail to elaborate -- 51 Verilator errors.** They
> instantiate `apb_monitor` with the interface it had at the initial commit
> (2025-11-01) and it has since been redesigned under them. They are its only
> consumers anywhere in the tree, they have no test, and nothing caught it for
> nine months because this area had no filelist, no registration and no
> Makefile. Tracked as AMBA-INTEG-EXAMPLES, which decides whether to rewrite or
> retire them. Read the pattern below; do not copy the RTL as it stands.

## The pattern these are meant to show

The APB family splits into two roles, and knowing which is which is the whole
lesson:

- **Bridges** -- [apb_master](../rtl-amba/apb/apb_master.md),
  [apb_slave](../rtl-amba/apb/apb_slave.md) and their `_cg` / `_cdc` / `_stub`
  variants, plus the APB5 equivalents -- carry **both** sides: raw APB
  (`s_apb_PSEL`, `m_apb_PADDR`) on the wire, and a `cmd_*` / `rsp_*` handshake
  internally.
- **Observers** -- [apb_monitor](../rtl-amba/monitor/apb_monitor.md),
  `apb5_monitor`, `apb_monitor_addr_check` -- take **only** the handshake. That
  is deliberate: it is what lets one monitor serve APB4 and APB5, because both
  bridges hand it the same shape.

So a monitor is a **sibling of a bridge, not a submodule of one** -- no bridge
instantiates a monitor. You put a bridge on the wire and tap its handshake:

```
raw APB ──> apb_slave ──cmd/rsp──> fabric
                 └── tap cmd_*/rsp_* ──> apb_monitor ──> monbus
```

Feeding raw APB pins straight into a monitor is exactly the mistake both
examples currently make.

## Navigation

- [Catalogue of every module in this area](index.md)
- [Back to the documentation index](../index.md)
- [rtl-amba](../rtl-amba/index.md) -- the bridges and monitors these compose
- [rtl-integ-common](../rtl-integ-common/index.md) -- the common-side examples

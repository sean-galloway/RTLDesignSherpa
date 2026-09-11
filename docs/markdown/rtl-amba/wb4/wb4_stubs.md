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

# wb4_master_stub / wb4_slave_stub

## Overview

The Wishbone master and slave with their FUB-side queues presented as a
single **packed vector** instead of named fields, matching what
`apb4_*_stub` and `apb5_*_stub` offer. A shim-style converter that already
carries a packed command through its own pipeline connects one bus instead
of six, and the packing lives here rather than being re-derived by every
consumer.

Nothing else differs. Each stub instantiates the ordinary block and only
splices the vector.

## Packing

Most significant field first, the same order on both stubs so a pair
connects directly:

```
cmd_data = {we, adr, dat, sel, cti, bte}     // CPW = 1 + AW + DW + SW + 3 + 2
rsp_data = {status, dat}                     // RPW = 2 + DW
```

`cti` and `bte` occupy their bits whatever `USE_BURST_HINTS` is, so the
vector width does not move with the parameter. With the hints off the inner
block ignores them and the bus reads CLASSIC/LINEAR.

## Parameters and Ports

Every parameter of the wrapped block, plus the derived `CPW` and `RPW`.
Ports are the block's Wishbone side unchanged, with `cmd_data` / `rsp_data`
in place of the named queue fields.

| Stub | Wraps | Queue direction |
|---|---|---|
| `wb4_master_stub` | [wb4_master](wb4_master.md) | `cmd_data` in, `rsp_data` out |
| `wb4_slave_stub` | [wb4_slave](wb4_slave.md) | `cmd_data` out, `rsp_data` in |

## Test

`val/amba/test_wb4_stubs.py` checks the packing directly and in both
directions: a packed command driven into the master stub must appear on the
Wishbone wires field for field, and a Wishbone transfer into the slave stub
must appear in `cmd_data` field for field, with the response vector carrying
`{status, dat}`. Run with the hints on and off, since the tie-off case must
read CLASSIC/LINEAR whatever was packed. Two mutations fail it: swapping
`dat`/`sel` in the master's unpack, and reversing the slave's response
unpack.

## Related

- [wb4_master](wb4_master.md), [wb4_slave](wb4_slave.md) - what they wrap
- [apb4_master_stub](../apb4/apb4_master.md) - the same idea over APB

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

# wb4_master_stub

## Overview

[wb4_master](wb4_master.md) with its FUB-side queues presented as a
single **packed vector** instead of named fields, matching what
`apb4_master_stub` and `apb5_master_stub` offer. A shim-style converter
that already carries a packed command through its own pipeline connects
one bus instead of six, and the packing lives here rather than being
re-derived by every consumer.

Nothing else differs: the stub instantiates the ordinary block and only
splices the vector.

## Parameters

Every parameter of [wb4_master](wb4_master.md), plus the derived widths:

| Parameter | Value | Description |
|---|---|---|
| CPW | 1 + AW + DW + SW + 3 + 2 | Packed command width |
| RPW | 2 + DW | Packed response width |

## Ports

`wb4_master`'s Wishbone side, unchanged. On the FUB side, the command
arrives packed and the response leaves packed:

| Port | Direction | Description |
|---|---|---|
| `cmd_valid` / `cmd_ready` | Input / Output | Command handshake |
| `cmd_data [CPW-1:0]` | Input | Packed command |
| `rsp_valid` / `rsp_ready` | Output / Input | Response handshake |
| `rsp_data [RPW-1:0]` | Output | Packed response |

## Functional Description

### Packing

Most significant field first. Both stubs use the same order, so a
`wb4_master_stub` and a `wb4_slave_stub` connect directly:

```
cmd_data = {we, adr, dat, sel, cti, bte}     // CPW = 1 + AW + DW + SW + 3 + 2
rsp_data = {status, dat}                     // RPW = 2 + DW
```

`cti` and `bte` hold their bits whatever `USE_BURST_HINTS` is, so the
vector width does not move with the parameter. With the hints off the
inner block ignores them and the bus reads CLASSIC/LINEAR.

## Related Modules

- [wb4_master](wb4_master.md) — the block this wraps
- [wb4_slave_stub](wb4_slave_stub.md) — the other half of a stub pair
- [wb4_pkg](wb4_pkg.md) — the status encoding inside `rsp_data`

## Testing

`val/amba/test_wb4_stubs.py` checks the packing directly, in both
directions and with the burst hints on and off. Two mutations fail it:
swapping `dat`/`sel` in the master's unpack, and reversing the slave's
response unpack.

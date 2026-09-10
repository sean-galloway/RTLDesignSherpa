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

# wb4_pkg

The response-status encoding shared by every module in the Wishbone B4
family and by the Python bus functional models. It is one enum and one width
constant, kept in a package so the value of `ERR` has exactly one definition.

## Design Notes

**This is a package, not a module.** No ports, no clock. Compile order
matters: it must be analysed before anything importing it, which is why
`rtl/amba/filelists/wb4_pkg.f` exists and every consumer `-f` includes it
rather than hand-listing the source.

**Why a status field at all.** Wishbone terminates a transfer with one of
three wires, `ACK`, `ERR` or `RTY`. The FUB-side response queue carries the
outcome as a 2-bit status instead, so a consumer reads one field rather than
decoding three mutually exclusive strobes. `WB4_STATUS_WIDTH` sizes that
field everywhere it appears.

**No test of its own, and none expected.** A package has no behaviour to
simulate. It is verified by every module that imports it failing to
elaborate if a declaration is wrong.

## Declarations

```systemverilog
package wb4_pkg;
    localparam int WB4_STATUS_WIDTH = 2;

    typedef enum logic [WB4_STATUS_WIDTH-1:0] {
        WB4_RSP_ACK = 2'd0,
        WB4_RSP_ERR = 2'd1,
        WB4_RSP_RTY = 2'd2
    } wb4_rsp_status_t;
endpackage
```

| Name | Value | Meaning |
|---|---|---|
| `WB4_STATUS_WIDTH` | 2 | Width of every `rsp_status` / `cmd`-side status field in the family |
| `WB4_RSP_ACK` | `2'd0` | Normal termination |
| `WB4_RSP_ERR` | `2'd1` | Slave signalled an error |
| `WB4_RSP_RTY` | `2'd2` | Slave asked for the transfer to be retried |
| _(unused)_ | `2'd3` | Not an encoding; treated as reserved |

**`RTY` is a status, not an action.** `wb4_master` never re-issues on its
own; it reports what the slave said and the FUB decides. Put
[`wb4_retry`](wb4_retry.md) in front of the master to absorb retries
transparently up to a budget.

## Consumers

Every module in the family imports it: [`wb4_master`](wb4_master.md),
[`wb4_slave`](wb4_slave.md), [`wb4_monitor`](wb4_monitor.md),
[`wb4_retry`](wb4_retry.md), [`wb4_master_retry`](wb4_master_retry.md), the
clock-gated and CDC variants, and the `axil4_to_wb4` bridge in
`projects/components/converters`.

The DV side mirrors the same three values in
`CocoTBFramework.components.shared.wb4_common` (`WB4_STATUS_ACK`,
`WB4_STATUS_ERR`, `WB4_STATUS_RTY`), and `monitor_wb4_pkg` carries the
separate event codes the monitor emits.

## Related

- [Wishbone B4 family README](README.md) - the protocol scope and the mode rules
- [`monitor_wb4_pkg`](../includes/monitor_wb4_pkg.md) - the monitor's event codes, a different package

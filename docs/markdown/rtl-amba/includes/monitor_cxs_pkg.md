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


# CXS Event Code Reference

The per-protocol event-code reference for CXS (`PROTOCOL_CXS`, 4'h6). Every monbus packet sourced by
[`cxs_monitor_lite`](../monitor/cxs_monitor_lite.md) takes its 8-bit `event_code` from one of the enums in
`rtl/amba/includes/ocelus_cxs_pkg.sv` (package `monitor_cxs_pkg`, not re-exported by `monitor_pkg`).
For the packet layout and the protocol and packet-type enums, see [`monitor_package_spec.md`](./monitor_package_spec.md);
for what each event means and its `event_data` layout, see the monitor page.

Slots `8'h0`-`8'hE` hold the defined codes (with `_RESERVED_*` filling the gaps) and `8'hF` is `*_USER_DEFINED`,
as in the other packages. `CXS_ERR_EVENT_DROPPED` is `8'hE`, the same value as in AXI and AXIS, so host tooling
decodes a drop report identically whatever the protocol. The tables below are generated from the SV enums; the
Python decoder (`bin/TBClasses/monbus`) is checked against the same file by `tests/test_monbus_cxs.py`.


## Error (`PktTypeError`) -- `cxs_error_code_t`

| Value | Name | Meaning |
|---|---|---|
| 8'h0 | `CXS_ERR_PROTOCOL` | the endpoint's protocol_error rose (credit/link/CXSCNTL rule broken) |
| 8'h1 | `CXS_ERR_PARITY` | the endpoint's parity_error rose (an Odd_Byte_Parity check failed) |
| 8'h2 | `CXS_ERR_ENDERROR` | a flit ended one or more packets with ENDERROR |
| 8'hE | `CXS_ERR_EVENT_DROPPED` | events lost to monbus backpressure (event_data = count) |
| 8'hF | `CXS_ERR_USER_DEFINED` |  |

## Timeout (`PktTypeTimeout`) -- `cxs_timeout_code_t`

| Value | Name | Meaning |
|---|---|---|
| 8'h0 | `CXS_TIMEOUT_CREDIT` | a flit waited for a credit (TX) / the pool stayed exhausted (RX) |
| 8'h1 | `CXS_TIMEOUT_LINK` | the link sat in ACTIVATE or DEACTIVATE (a stuck 4-phase handshake) |
| 8'h2 | `CXS_TIMEOUT_PACKET` | a packet open with no flit |
| 8'hF | `CXS_TIMEOUT_USER_DEFINED` |  |

## Completion (`PktTypeCompletion`) -- `cxs_completion_code_t`

| Value | Name | Meaning |
|---|---|---|
| 8'h0 | `CXS_COMPL_PACKET_END` | a flit ended one or more packets (CXS-Lite: every flit) |
| 8'hF | `CXS_COMPL_USER_DEFINED` |  |

## Credit (`PktTypeCredit`) -- `cxs_credit_code_t`

| Value | Name | Meaning |
|---|---|---|
| 8'h0 | `CXS_CREDIT_STARVED` | credit starvation lasted cfg_stall_threshold cycles |
| 8'h1 | `CXS_CREDIT_BACKPRESSURE` | the FUB handshake stalled cfg_stall_threshold cycles |
| 8'hF | `CXS_CREDIT_USER_DEFINED` |  |

## Channel (`PktTypeChannel`) -- `cxs_channel_code_t`

| Value | Name | Meaning |
|---|---|---|
| 8'h0 | `CXS_CHAN_STREAM_CHANGE` | CXSPRCLTYPE / CXSSRCID / CXSTGTID differ from the previous flit (2.5.2) |
| 8'hF | `CXS_CHAN_USER_DEFINED` |  |

## Stream (`PktTypeStream`) -- `cxs_stream_code_t`

| Value | Name | Meaning |
|---|---|---|
| 8'h0 | `CXS_STREAM_LINK_ACTIVATE` | STOP -> ACTIVATE (ACTIVEREQ rose) |
| 8'h1 | `CXS_STREAM_LINK_UP` | -> RUN (ACTIVEACK rose) |
| 8'h2 | `CXS_STREAM_LINK_DEACTIVATE` | RUN -> DEACTIVATE (ACTIVEREQ fell) |
| 8'h3 | `CXS_STREAM_LINK_DOWN` | -> STOP (ACTIVEACK fell, every credit home) |
| 8'hF | `CXS_STREAM_USER_DEFINED` |  |

---

## Navigation

- **[Package Spec](monitor_package_spec.md)**
- **[CXS Monitor Lite](../monitor/cxs_monitor_lite.md)**

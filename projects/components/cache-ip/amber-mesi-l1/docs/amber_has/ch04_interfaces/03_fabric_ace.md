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

# Fabric-Side ACE Masters and Coherent Issue

## Onyx-rig fabric

`amber_ace` uses the existing `rtl/amba/ace/axi4ace_master_rd` and `axi4ace_master_wr` modules toward `onyx`. These are full ACE masters with `ARSNOOP[3:0]` and `AWSNOOP[2:0]` transaction-type fields and auto-pulsed `RACK`/`WACK` outputs.

## `amber_ace_issue`

`amber_ace_issue` maps cache-side events to the onyx D2 coherent-transaction subset:

| Cache event | ACE transaction | Snoop field |
|---|---|---|
| read miss, shared intent | `ReadShared` | `fub_axi_arsnoop[3:0]` = `ReadShared` encoding |
| read miss, exclusive intent | `ReadUnique` | `fub_axi_arsnoop[3:0]` = `ReadUnique` encoding |
| write to Shared line | `CleanUnique` | `fub_axi_awsnoop[2:0]` = `CleanUnique` encoding |
| write to Invalid line (whole line) | `MakeUnique` | `fub_axi_awsnoop[2:0]` = `MakeUnique` encoding |
| dirty eviction | `WriteBack` | `fub_axi_awsnoop[2:0]` = `WriteBack` encoding |
| clean eviction | `Evict` | `fub_axi_awsnoop[2:0]` = `Evict` encoding |

: Table 4.2: Cache events to ACE transactions

## House-module pin contracts — not restated here

`axi4ace_master_rd` and `axi4ace_master_wr` are house modules: their full
`fub_axi_*`/`m_axi_*` pin contracts, widths, and parameters live in their
own sources (`rtl/amba/ace/axi4ace_master_rd.sv`,
`rtl/amba/ace/axi4ace_master_wr.sv`) and the AMBA documentation index —
this HAS does not duplicate them. What amber adds on top of those
contracts is exactly two facts:

- the `fub_axi_arsnoop[3:0]` / `fub_axi_awsnoop[2:0]` fields carry the
  Table 4.2 transaction encodings above (the standard ACE snoop values);
- `m_axi_rack` / `m_axi_wack` are **auto-pulsed inside the adapters** one
  cycle after the last R beat / the B handshake — the onyx D2 subset has
  no ordering semantics that need master-controlled acknowledges, so
  amber's `amber_ace_issue` never drives them.

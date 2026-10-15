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

`amber_ace` uses the existing `rtl/amba/ace/axi4ace_master_rd` and `axi4ace_master_wr` modules toward `onyx`. These are full ACE masters with `ARSNOOP[3:0]` and `AWSNOOP[2:0]` transaction-type fields and auto-pulsed `RACK`/`WACK` outputs (deprecated per ruling 2026-10-11 (Sean); removal tracked as amber A5).

## `amber_ace_issue`

`amber_ace_issue` maps cache-side events to the onyx D2 coherent-transaction subset:

| Cache event | ACE transaction | Snoop field |
|---|---|---|
| read miss, shared intent | `ReadNotSharedDirty` | `fub_axi_arsnoop[3:0]` = `ReadNotSharedDirty` encoding (0x3) — issue #106 |
| read miss, exclusive intent | `ReadUnique` | `fub_axi_arsnoop[3:0]` = `ReadUnique` encoding (0x7) |
| write to Shared line | `CleanUnique` | `fub_axi_arsnoop[3:0]` = `CleanUnique` encoding (0xB) — AR channel, issue #106 |
| write to Invalid line (whole line) | `MakeUnique` | `fub_axi_arsnoop[3:0]` = `MakeUnique` encoding (0xC) — AR channel, issue #106 |
| dirty eviction | `WriteBack` | `fub_axi_awsnoop[2:0]` = `WriteBack` encoding |
| clean eviction | `Evict` | `fub_axi_awsnoop[2:0]` = `Evict` encoding |

: Table 4.2: Cache events to ACE transactions (post-#106, commit 2594d73bb)

## House-module pin contracts — not restated here

`axi4ace_master_rd` and `axi4ace_master_wr` are house modules: their full
`fub_axi_*`/`m_axi_*` pin contracts, widths, and parameters live in their
own sources (`rtl/amba/ace/axi4ace_master_rd.sv`,
`rtl/amba/ace/axi4ace_master_wr.sv`) and the AMBA documentation index —
this HAS does not duplicate them. What amber adds on top of those
contracts is exactly four facts:

- the `fub_axi_arsnoop[3:0]` / `fub_axi_awsnoop[2:0]` fields carry the
  Table 4.2 transaction encodings above (the standard ACE snoop values);
- `ARDOMAIN` / `AWDOMAIN` are tied to Outer Shareable (`0b10`) and
  `ARBAR` / `AWBAR` to `0b00` (normal access): every amber transaction is
  coherent, the rig has one shareability domain, and amber issues no
  barriers (onyx D8);
- `RRESP[3:2]` (IsShared, PassDirty) is consumed since issue #106 (commit
  `2594d73bb`): a `PassDirty` response installs **M** regardless of request
  class (the fill engine forwards `fill_pass_dirty` to `l1_control`), so a
  received dirty line keeps its write-back responsibility. Default installs
  are unchanged (`ReadShared`/`ReadNotSharedDirty` -> S, `ReadUnique` -> M).
  Read misses issue `ReadNotSharedDirty` precisely so the manager may pass
  dirty legally (MAS Chapter 3.3);
- `m_axi_rack` / `m_axi_wack` are **auto-pulsed inside the adapters** one
  cycle after the last R beat / the B handshake. The family contract
  omits RACK/WACK (ruling 2026-10-11 (Sean)); the auto-pulse is retained
  in the generic house wrappers but is deprecated for onyx-rig use, with
  removal tracked as amber A5.

## Outside the onyx D2 subset

`WriteLineUnique`, `WriteUnique`, `WriteClean`, `WriteEvict`, and DVM/barrier transactions are outside the onyx D2 coherent-transaction subset that amber targets. The book treats these as scope-growing features: `WLU`/`WU` for non-temporal or partial-line writes (Chinnakonda, §7.3–7.4), `WriteClean`/`WriteEvict` for cache-maintenance and victim-cache traffic (Chinnakonda, §7.4), and address-based cache maintenance / DVM as a later coherent-system concern (Chinnakonda, §7.16). amber does not need them for v1.0; Table 4.2 is the supported subset.

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

# Module Hierarchy

## Planned hierarchy

scoria mirrors pumice's three-tier shape — FUBs under macros under a top — with
the `scoria_` prefix replacing `pumice_`. The table below is the planned module
list with its marking; it is a specification, and the RTL is expected to match
it or this document to be corrected.

### Top and macro tier

| scoria module | pumice counterpart | Marking |
|---|---|---|
| `scoria_top` | `pumice_top` | INHERITED (structure) |
| `scoria_top_geared` | `pumice_top_geared` | INHERITED — the host/DRAM width-gearing wrapper |
| `scoria_core` | `pumice_core` | INHERITED |
| `scoria_axi4_ifc` | `pumice_axi4_ifc` | INHERITED |
| `scoria_mem_cmd_scheduler` | `pumice_mem_cmd_scheduler` | MODIFIED — must admit ZQ maintenance demand |
| `scoria_dfi_layer` | `pumice_dfi_layer` | MODIFIED — v3.1 control surface |

: Table 2.1: Top and macro tier

### FUB tier, inherited unchanged

`addr_mapper`, `bank_timer`, `scoria_bank_timers`, `global_timers` (in its
fixed form — see Chapter 2.2), `scoria_cmd_arbiter`, `scoria_page_policy`,
`scoria_rd_cmd_cam`, `scoria_wr_data_cam`, `scoria_rd_intake`,
`scoria_wr_intake`, `scoria_wr_splitter`, `scoria_rd_return_ring`,
`scoria_axi_burst_chopper`, `scoria_dfi_cdc`, `scoria_dfi_cmd_path`,
`scoria_dfi_rd_aligner`, `scoria_dfi_wr_serializer`,
`scoria_cmd_history_checker`, and **`refresh_ctrl`** -- which already carries the
`REFpb` bank rotor for LPDDR2 and needs only a mode-select CSR for LPDDR3, and
**`powerdown_ctrl`** -- power-down is CKE plus `SRE`/`SRX` on this PHY family,
so only the new command encodings change, and **`dfi_signal_pack`** -- a pure
registered pipeline stage whose packed signals v3.1 does not touch.

That is 21 of the 24 FUBs carried over with no functional change. The command
history checker is worth naming explicitly: it is the verification-side block
that independently re-derives JEDEC spacing from the issued command stream, and
it must grow DDR3's parameters, but its mechanism is inherited.

### FUB tier, modified

| Module | Why it changes | Detail |
|---|---|---|
| `init_sequencer` | DDR3 adds a `RESET#` pin and a four-register MR set | Ch 3.2 |
| `mode_register` | MR0-MR3 replaces MR0-MR2 plus EMRS3 | Ch 3.2 |
| `dfi_cmd_formatter` | new command encodings: `ZQCL`, `ZQCS`, `PREA` | Ch 3.2 |

: Table 2.2: Modified FUBs

### FUB tier, new

| Module | Purpose |
|---|---|
| `scoria_zq_ctrl` | issues `ZQCS` periodically as maintenance traffic; interval a runtime CSR. `ZQCL` is init-only and belongs to the init sequencer |
| `scoria_wrlvl_ifc` | the write-leveling interface: DFI leveling handshake, MR1 write path, `tWL*` window enforcement, `*_STATS` telemetry. **No search loop** |

: Table 2.3: New FUBs

## Naming, and the package

Per decision D3, scoria gets its own `scoria_pkg` with a one-bit memtype enum
covering `{DDR3, LPDDR3}`. It does not extend `pumice_pkg`, whose `memtype_e` is
one bit wide and already spent on `{DDR2, LPDDR2}` — widening it would change a
CSR in a design that is measured and shipping, for a controller whose RTL did
not exist yet. The trade was wrong in that direction then, and scoria having
RTL now does not make it right: widening a shipping CSR costs the same today.

When the DDR4/LPDDR4 controller begins, a shared `mem_ctrl_pkg` with a two-bit
memtype becomes worth the migration, and both existing controllers move to it
together. That is the right time because the cost is paid once with three
members to amortise it, rather than twice.

**Note:** this means `scoria_pkg` and `pumice_pkg` will contain near-identical
type definitions for a period. That duplication is deliberate and time-boxed,
and it is recorded here so it is not mistaken for an oversight and "fixed" by
someone widening pumice's CSR.

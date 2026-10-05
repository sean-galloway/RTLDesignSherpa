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

andesite mirrors scoria's three-tier shape — FUBs under macros under a top —
with the `andesite_` prefix replacing `scoria_`. The tables below are the
planned module list with its marking; they are a specification, and the RTL is
expected to match them or this document to be corrected. The accounting
counts scoria's FUB files as they exist on disk — 26 of them — and the
markings sum to that number.

### Top and macro tier

| andesite module | scoria counterpart | Marking |
|---|---|---|
| `andesite_top` | `scoria_top` | INHERITED (structure) |
| `andesite_top_geared` | `scoria_top_geared` | INHERITED — the host/DRAM width-gearing wrapper |
| `andesite_core` | `scoria_core` | INHERITED |
| `andesite_axi4_layer` | `scoria_axi4_ifc` | INHERITED |
| `andesite_scheduler_layer` | `scoria_mem_cmd_scheduler` | MODIFIED — bank-group-aware L/S admission, on top of scoria's ZQ maintenance admission |
| `andesite_dfi_layer` | `scoria_dfi_layer` | MODIFIED — DFI 4.0 control surface, DBI wires |

: Table 2.1: Top and macro tier

The CSR block rides at the macro tier as scoria's does: an `andesite_csr.rdl`
generated through the same PeakRDL flow. The **flow is INHERITED**; the
**contents grow** (FGR select, ODT policy, DBI enable, gear-down, parity) —
Chapter 5 owns the parameter and CSR inventory.

### FUB tier, inherited unchanged

`bank_timer` and `bank_timers`, `page_policy`, `rd_cmd_cam`, `wr_data_cam`,
`rd_intake`, `wr_intake`, `wr_splitter`, `rd_return_ring`,
`axi_burst_chopper`, `dfi_cdc`, and `cmd_history_checker`.

That is 12 of the 26 scoria FUB files carried over with no functional change.
Two more ride along in a grey area, each with its condition named in Chapter
3.1: **`powerdown_ctrl` DORMANT** — power-down is CKE plus `SRE`/`SRX`,
unchanged in mechanism — and **`dfi_signal_pack` DORMANT**, the registered
pack stage. A thirteenth, **`zq_ctrl` INHERITED** for DDR4 exactly as scoria
built it, with a NEW submodule for LPDDR4's MPC calibration path (Chapter
3.2).

`cmd_history_checker` is worth naming explicitly: it is the verification-side
block that independently re-derives JEDEC spacing from the issued command
stream. Its mechanism is inherited; its spacing-parameter set grows DDR4's
long/short pairs, and that growth is a parameter change, not a mechanism
change — the same disposition scoria recorded for DDR3's parameters.

### FUB tier, modified

| Module | Marking | Why it changes | Detail |
|---|---|---|---|
| `addr_mapper` | MODIFIED | bank-group decode: BG0/BG1 sit between chip select, bank and row | Ch 3.1 |
| `cmd_arbiter` | MODIFIED | L/S-aware issue — same-bank-group pairs take tCCD_L/tRRD_L, cross-group take tCCD_S/tRRD_S | Ch 3.1 |
| `global_timers` | MODIFIED | the long/short pairs join the enforced timing set as first-class counters | Ch 3.1 |
| `dfi_cmd_formatter` | MODIFIED | ACT_n fifth command pin, BG0/BG1, CA parity; NEW submodule: the LPDDR4 6-bit CA path | Ch 3.2, 3.6 |
| `init_sequencer` | MODIFIED | DDR4 reset procedure, MR0-MR6 order, gear-down entry, parity enable | Ch 3.2 |
| `mode_register` | MODIFIED | MR0-MR6 field maps per memtype | Ch 3.2 |
| `refresh_ctrl` | MODIFIED | FGR 1x/2x/4x via MR3 on the inherited elastic/TCR/placement base (scoria's landed TASK-001 Modes A/B/C) | Ch 3.4 |
| `dfi_cmd_path` | MODIFIED | ACT_n, BG and parity wires ride the command path to the PHY | Ch 3.2, 4.1 |
| `dfi_rd_aligner` | MODIFIED | DBI read path passes the inversion through | Ch 3.5 |
| `dfi_wr_serializer` | MODIFIED | DBI write path passes the inversion through | Ch 3.5 |
| `wrlvl_ifc` | MODIFIED | the training-interface family grows a read-leveling sibling; still no search loop | Ch 3.3 |

: Table 2.2: Modified FUBs — every row in this table is MODIFIED, and the
marking column says so rather than leaving it to the section heading

### FUB tier, new

| Module | Marking | Purpose |
|---|---|---|
| `odt_ctrl` | NEW | dynamic ODT: RTT_NOM/WR/PARK selection, ODT latency enforcement, `ODT` telemetry. **No scoria counterpart** — scoria holds ODT static, which DDR4 makes insufficient (Ch 3.5) |
| `rdlvl_ifc` | NEW | MPR-based read-leveling interface: DFI handshake, MR3 path, timing windows, telemetry. **No search loop** (Ch 3.3) |
| `ca_train_ifc` | NEW | LPDDR4 CA/WDQ training interface over the CA bus: DFI handshake, MPC paths, telemetry. **No search loop** (Ch 3.3) |

: Table 2.3: New FUBs — every row is NEW

## Naming, and the package

Per the family doc 01, andesite carries its own `andesite_pkg` from day one,
and the three near-identical family packages (pumice's, scoria's, andesite's)
are deliberate and time-boxed: the shared `mem_ctrl_pkg` migration executes
once, when andesite RTL bring-up starts, and both shipping controllers move
together. Chapter 5 owns `andesite_pkg`'s initial contents; the family doc
owns the migration plan and its conditions. Nothing about the package
duplication is an oversight, and nobody should "fix" it by widening a
shipping CSR.

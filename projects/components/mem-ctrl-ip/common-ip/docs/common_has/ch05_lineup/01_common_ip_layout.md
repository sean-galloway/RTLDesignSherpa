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

# The common-ip Layout

common-ip holds what no single controller owns. The layout is the
architecture of Chapter 2 made into a directory tree.

```
common-ip/
├── rtl/
│   ├── includes/mc_common_pkg.sv      the family package: memtype enum,
│   │                                  shared types, opcode encodings
│   ├── fub/                           the seventeen shared FUBs
│   ├── macro/                         the eight layers
│   └── filelists/                     .f files: one per FUB/layer + mc_common_all.f
├── dv/                                shared verification collateral (grows per campaign)
└── docs/                              family docs (this book, doctrine, lineage,
                                       knobs inventories, per-block MAS)
```

## The blocks (as of 2026-10-10)

**Package.** `mc_common_pkg` — the family memtype enum (six members, one LP
bit + two-bit generation field; design owned by
[01_mem_ctrl_pkg.md](../../01_mem_ctrl_pkg.md)), shared timing-struct
inventory, shared opcodes.

**Layers (macro/).**

| Layer | State | Customers |
|---|---|---|
| `mc_axi4_layer` | landed | pumice (measured); scoria/andesite scheduled |
| `mc_storage_layer` | landed | pumice; scoria/andesite scheduled |
| `mc_scheduler_layer` | landed (merged from three rock schedulers, −3,465 lines) | all three rocks adopt via thin wrappers |
| `mc_training_layer` | shell + rock wrappers | pumice carries ZQ/DQ cal behind it |
| `mc_ras_layer` | skeleton per doctrine 9 — instantiated nowhere | none yet; that is honest |
| `mc_dfi_2p1_layer` | landed | pumice (measured on Nexys A7) |
| `mc_dfi_3p1_layer` | landed | scoria |
| `mc_dfi_4p0_layer` | landed | andesite |

**Shared FUBs (fub/).** `mc_addr_mapper`, `mc_axi_burst_chopper`,
`mc_bank_timer`, `mc_bank_timers`, `mc_cmd_arbiter`, `mc_dfi_cdc`,
`mc_dfi_cmd_path`, `mc_dfi_wr_serializer`, `mc_dfi_rd_aligner`,
`mc_dfi_3p1_cmd_path`, `mc_dfi_4p0_cmd_path`, `mc_global_timers`,
`mc_rd_cmd_cam`, `mc_rd_intake`, `mc_rd_return_ring`, `mc_wr_data_cam`,
`mc_wr_intake`, `mc_wr_splitter`. Each is owned by a layer and documented in
that layer's [common_mas](../../common_mas/common_mas_index.md) chapter; the
knobs inventories (`mc_*_knobs.md` beside this book) record the parameter
surface per block.

## The ownership rule (restated so this book is self-sufficient)

A design or doctrine that no single controller owns lives at this level; a
controller's book references these documents and never restates them. A
block enters common-ip through the two-customer rule (doctrine 11). A block
leaves only by obsolescence of all its customers.

## Documentation map

| Doc | Owns |
|---|---|
| this book (`common_has/`) | the layer-stack architecture, the seam, DFI naming, new doctrines |
| [common_mas/](../../common_mas/common_mas_index.md) | per-block microarchitecture of every block above |
| [01_mem_ctrl_pkg.md](../../01_mem_ctrl_pkg.md) | the shared package design |
| [02_family_doctrine.md](../../02_family_doctrine.md) | the original five doctrines |
| [03_dfi_boundary_lineage.md](../../03_dfi_boundary_lineage.md) | DFI clause-level lineage |
| [04_jedec_generation_deltas.md](../../04_jedec_generation_deltas.md) | JEDEC generation reuse argument |
| `mc_*_knobs.md` | parameter/knob inventories (measured, dated) |
| [phy_cal_csr_contract.md](../../phy_cal_csr_contract.md) | the training↔PHY contract surface |

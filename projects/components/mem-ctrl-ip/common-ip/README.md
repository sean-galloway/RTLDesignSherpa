# common-ip

Shared planes for the memory-controller family — the logic that was
previously duplicated across `pumice-*`/`scoria-*`/`andesite-*` now lives
here once.

**Eventually** (Phase 2 of the reorg, see
[the design spec](../../../../docs/superpowers/specs/2026-10-09-mem-ctrl-ip-reorg-design.md)):

- `mc_axi4_plane` — one parameterized source (`.MEMTYPE`, geometry knobs)
- `mc_dfi_2p1_plane` / `mc_dfi_3p0_plane` — per-DFI-revision planes
- `mc_scheduler_plane` — policy-parameterized (FR-FCFS default)
- `mc_training_plane` — training control plane (PHY mechanism stays behind
  a documented CSR contract)
- `mc_storage_plane` — CAMs/SRAMs as a pipeline drop-in

**Today** (post-Phase-2, 2026-10-10): the extraction has landed. `rtl/`
holds the package (`mc_common_pkg`), eight planes (`mc_axi4_plane`,
`mc_storage_plane`, `mc_scheduler_plane`, `mc_training_plane`,
`mc_ras_plane`, `mc_dfi_2p1_plane`, `mc_dfi_3p1_plane`,
`mc_dfi_4p0_plane`), and seventeen shared FUBs with filelists; pumice,
scoria, and andesite consume them. The architecture is specified in
[docs/common_has/](docs/common_has/common_has_index.md) and the per-block
microarchitecture in [docs/common_mas/](docs/common_mas/common_mas_index.md)
— read those first.

Boundary rule: a block moves here only when it has **two live customers**
at extraction time — speculative one-customer abstractions stay in the
research controllers.

## Further reading

The maintainer's calibre library holds the books this architecture is built
against; the subset closest to the common planes:

- *Cache and Memory Hierarchy Design* — Steven A. Przybylski (Morgan
  Kaufmann). What the schedulable-entry view and the pick machinery are for.
- *Principles and Practices of Interconnection Networks* — Dally & Towles.
  Ordering and flow control — the descriptor seam's return path is its own
  chapter in here in spirit.
- *Error Correction Coding* — Todd K. Moon. The theory the `mc_ras_plane`
  transform pair will draw on when its first feature lands.
- *Computer Architecture: A Quantitative Approach* — Hennessy & Patterson.
  The source of the measured-number-beside-the-claim habit the family's
  books follow.
- *Python for RTL Verification* — Ray Salemi. The cocotb discipline the
  shared DV collateral follows.

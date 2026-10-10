# common-ip

Shared layers for the memory-controller family — the logic that was
previously duplicated across `pumice-*`/`scoria-*`/`andesite-*` now lives
here once.

**Eventually** (Phase 2 of the reorg, see
[the design spec](../../../../docs/superpowers/specs/2026-10-09-mem-ctrl-ip-reorg-design.md)):

- `mc_axi4_layer` — one parameterized source (`.MEMTYPE`, geometry knobs)
- `mc_dfi_2p1_layer` / `mc_dfi_3p0_layer` — per-DFI-revision layers
- `mc_scheduler_layer` — policy-parameterized (FR-FCFS default)
- `mc_training_layer` — training control plane (PHY mechanism stays behind
  a documented CSR contract)
- `mc_storage_layer` — CAMs/SRAMs as a pipeline drop-in

**Today** this directory is an intentional skeleton: `docs/` holds the
family-level architectural documents (package conventions, family doctrine,
DFI boundary lineage, JEDEC generation deltas) relocated from
`mem-ctrl-ip/docs/` during Phase 1. The `rtl/` and `dv/` trees are
placeholders until layer extraction begins.

Boundary rule: a block moves here only when it has **two live customers**
at extraction time — speculative one-customer abstractions stay in the
research controllers.

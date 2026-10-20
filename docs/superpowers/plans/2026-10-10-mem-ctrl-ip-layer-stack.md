# mem-ctrl-ip Layer Stack (Phase 2b) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans (native — human partner chose native execution). Steps use checkbox (`- [ ]`) syntax.

**Goal:** Stand up the partner's layer stack in common-ip before the training-layer work resumes: storage layer extraction, RAS layer skeleton, and the pumice DFI layer extracted as a per-revision common layer (`mc_dfi_2p1_layer`).

**Architecture:** Partner rulings 2026-10-10 (ledger): pipeline = axi4_layer (done) -> storage_layer -> scheduler_layer; seams evolve toward ONE uniform request-descriptor stream (good-over-perfect: extract layers with their CURRENT concrete interfaces now, evolve the contract in the scheduler-merge task; return path keeps its own contract). RAS = transform pair on the data/return seams + scrub as a maintenance-class client, all param-gated, skeleton-first.

**Tech Stack:** SystemVerilog, Verilator/cocotb DV suites as behavior pins, NexysA7/Genesys2 Vivado builds as timing pins where relevant.

**Spec:** umbrella spec `docs/superpowers/specs/2026-10-09-mem-ctrl-ip-reorg-design.md` + partner rulings in `.superpowers/sdd/2026-10-10-mem-ctrl-ip-phase2-common-extraction/progress.md`.

## Global Constraints

- Same as Phase-2 (bit-identical behavior pins, one logical change per commit, pathspec commits, SEED=12345, PYTHONPYCACHEPREFIX per task, never touch `formal/amber/*` staged work, hooks never bypassed).
- Naming: `mc_storage_layer`, `mc_ras_layer`, `mc_dfi_2p1_layer`; children keep `mc_*` / get `mc_`-prefixed on extraction (registry `mc_` area exists).
- Each task = its own commit after its own gates (3-rock suite or scoped suite + lint + registry + hooks), same pattern as Phase-2 Tasks 2/3.
- DFI version authority: pumice docs `simplified_dfi_2_1` -> DFI 2.1. Scoria's extraction later = `mc_dfi_3p1_layer`; andesite = `mc_dfi_4p0_layer`. Do NOT rename scoria/andesite DFI layers in this phase.

## Review Focus

1. Storage-layer extraction must not change WHAT crosses to the scheduler — same vectors, same epoch semantics (the 4.5 advisory snapshot is the seam; extraction moves the registers' owners, not the timing contract).
2. RAS skeleton must be genuinely zero-cost at HAS_ECC=0 (unelaborated bypass), not disabled logic.
3. dfi_2p1 extraction: DFI-init handshake + mode-register shadow ownership stays scheduler-side; only the pack/phase/cdc path moves.
4. Filelist registry: new layers registered in bin/filelists.toml under the `mc_` area; rock filelists swap, never hand-list common sources.
5. DV TBs referencing `pumice_dfi_layer` / moved modules by name (dut_name, _FILELIST) get repointed per rock.

---

### Task A: mc_storage_layer (extract CAMs + snoop + bank image from mc_axi4_layer)

**Files:** common-ip/rtl/macro/mc_storage_layer.sv (new) + mc_storage_layer.f; modify mc_axi4_layer (children reduced), 3 rock tops, DV filelists.

- [ ] Inventory what physically moves: from Task 3, mc_axi4_layer children = mc_wr_intake, mc_rd_intake, mc_wr_data_cam, mc_rd_cmd_cam, mc_wr_splitter, mc_axi_burst_chopper. Per the seam ruling, the CAMs + the rd-snoop (wr->rd hazard) logic + bank-image presentation move to storage; intakes/splitter/chopper STAY in axi4 (they are the AXI-termination/transform side).
- [ ] Create mc_storage_layer composing mc_wr_data_cam + mc_rd_cmd_cam (+ snoop wiring exactly as today); ports = today's CAM-facing scheduler ports.
- [ ] Pumice adoption first: instantiate between axi4_layer and scheduler_layer; bit-identical; pumice suite + lint gate; commit.
- [ ] Scoria + andesite adoption; gates; commit.
- [ ] Ledger.

### Task B: mc_ras_layer (skeleton)

**Files:** common-ip/rtl/macro/mc_ras_layer.sv (new) + .f + params doc section.

- [ ] Layer boundary on the two data seams (W data forward, R return) as straight-assign bypass; one param struct (HAS_ECC enum {OFF,DETECT,CORRECT}, ECC_MODE reserved); CSR surface reserved (fields read 0 when OFF).
- [ ] NOT instantiated into rocks yet (no customer); registered + lint + doc only; commit. (Instantiation comes with the first real RAS feature.)

### Task C: mc_dfi_2p1_layer (extract pumice_dfi_layer)

**Files:** common-ip/rtl/macro/mc_dfi_2p1_layer.sv (new) + .f; rename children to mc_* where private (dfi_cmd_formatter, dfi_cmd_path, dfi_signal_pack, dfi_cdc as applicable); pumice filelists + DV repoint; scoria/andesite untouched.

- [ ] Verify DFI 2.1 claim against the pumice MAS doc + dfi-specs repo copy; record in the layer header.
- [ ] Extract with zero behavior change (pumice suite + lint gate); commit.
- [ ] Ledger; note scoria=3.1/andesite=4.0 as follow-on tasks after the training layer.

## Self-Review

1. Spec coverage: all three partner directives (storage, ras, dfi_2p1) have a task; training explicitly deferred to after the stack.
2. Steps are actions with checkable results; interfaces pinned by existing concrete signals (no new contract invented this phase).
3. Names consistent (mc_ prefix family).
4. Review Focus pins per task map to gates.
5. Proportion: plan ~ decisions; extractions follow the proven Task 2/3 playbook.

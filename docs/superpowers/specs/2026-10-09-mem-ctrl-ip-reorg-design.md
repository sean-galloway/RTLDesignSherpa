# mem-ctrl-ip Reorganization: research / common / product — Design Spec

**Date:** 2026-10-09
**Status:** Approved approach (design dialogue 2026-10-09), pending written-spec review
**IP:** `projects/components/mem-ctrl-ip/` (all three memory controllers + new common/product areas)

## 1. Goal

Split the flat `mem-ctrl-ip/` tree into three lifecycle areas so that shared
layer logic lives once, research controllers stop forking each other, and a
hardened "product" controller becomes a graduation event rather than a copy:

```
mem-ctrl-ip/
├── mem-ctrl-research-ip/           proving ground — git mv, as-is
│   ├── pumice-ddr2-lpddr2/
│   ├── scoria-ddr3-lpddr3/
│   └── andesite-ddr4-lpddr4/
├── mem-ctrl-common-ip/             shared layers — one source each
│   ├── rtl/includes/mc_common_pkg.sv
│   ├── rtl/macro/
│   │   ├── mc_axi4_layer.sv        ONE source, #(.MEMTYPE, geometry…)
│   │   ├── mc_dfi_2p1_layer.sv     per-DFI-rev, standalone
│   │   ├── mc_dfi_3p0_layer.sv     per-DFI-rev, standalone
│   │   ├── mc_scheduler_layer.sv   policy-parameterized
│   │   ├── mc_training_layer.sv    control plane only (PHY mechanism behind contract)
│   │   └── mc_storage_layer.sv     CAMs/SRAMs, pipeline drop-in
│   ├── rtl/fub/                    bank timers, refresh, init, zq, shared FUBs
│   ├── docs/                       common HAS/MAS + base architectural docs
│   │                               (relocated from mem-ctrl-ip/docs/)
│   └── dv/                         per-layer unit tests
└── mem-ctrl-product-ip/            created at first graduation — NOT before
```

## 2. Why

Today each controller carries its own `*_axi4_layer`, `*_dfi_layer`,
`*_scheduler_layer` (+ pumice/andesite `*_training_layer`). The three AXI
layers differ almost only by protocol knobs (address mapping, BL, refresh
interaction, MR set, gear ratio); the three schedulers differ by policy
(FR-FCFS vs. what LPDDR wants) while their storage (CAMs/SRAMs) is structurally
the same. Every bug fix in a shared concept currently wants three edits;
layer drift is already visible (scoria has no training layer; pumice and
andesite do).

## 3. Decisions (locked in design dialogue)

1. **AXI layer = one parameterized source.** `mc_axi4_layer` with
   `#(.MEMTYPE, geometry…)`; protocol behavior resolved at elaboration.
   No per-protocol forks.
2. **DFI layer = one module per DFI spec revision.** Ports differ enough
   between revs that a single unified DFI layer would be `generate` spaghetti.
   `mc_dfi_2p1_layer` (pumice), `mc_dfi_3p0_layer` (scoria); andesite picks up
   its rev (3.1-class) when extracted. A shared gear/CDC core is lifted out
   **only if** the second extraction shows the gear logic is byte-identical —
   evidence-driven, not assumed.
3. **Storage is policy-independent.** `mc_storage_layer` holds the CAMs/SRAMs
   as a pipeline drop-in; the scheduler layer becomes policy-parameterized
   (FR-FCFS default; an LPDDR personality is the second proof that the split
   works). Bank timers and other scheduler internals are parameterized the
   same way.
4. **Training layer = control plane in common, PHY mechanism behind a
   contract.** Common owns training FSMs, sequencing, telemetry. Delay
   taps/bitslip/phase stay a documented PHY-abstraction CSR contract — the
   interface `k7ddrphy` satisfies today, written so a future PHY satisfies it
   too.
5. **Product = graduation with config.** `mem-ctrl-product-ip/` appears when
   the first controller graduates: research RTL (on common layers) + declared
   board config + timing closure. No forked product tree. Directory is created
   at that event, not before (repo decision: no empty placeholder components).
6. **Naming:** `mc_` prefix for all common modules (avoids collisions with
   amba-family `axi4_*` names).

## 4. Migration plan (move-first, extract-second)

**Phase 1 — pure move, zero RTL edits.**
`git mv` the three controllers under `mem-ctrl-research-ip/`; relocate
`mem-ctrl-ip/docs/` base architectural content into
`mem-ctrl-common-ip/docs/`. Fix every reference: filelists, dv paths, formal
configs, doc links, `projects/fpga-systems/Genesys2/mem-ctrl-ip/*` harnesses,
and the vault task areas (`vault/Tasks/{pumice,scoria,andesite}-*`) which by
convention mirror the tree. Tree stays green throughout; no source file
content changes.

**Phase 2 — extraction, cheapest-coupling first, one layer at a time.**
Order: `mc_common_pkg` → bank-timer/storage FUBs → `mc_axi4_layer` → training
control plane (+ PHY CSR contract doc) → scheduler (storage split-out,
policy knob) → DFI layers last (pumice 2.1 + scoria 3.0 give both revs).
Each layer lands with its source MC as first customer; the other two MCs
migrating onto it is the acceptance test. Scoria's missing training layer is
split out as part of the training extraction (becomes the third data point).

**Phase 3 — product.** Deferred by definition until the first graduation
candidate (pumice is closest today).

## 5. Boundary rules

- A block enters `mem-ctrl-common-ip/` only with **two live customers** at
  extraction time. One-customer abstractions stay in the research controller
  until the second customer exists.
- Research MCs keep rock-prefixed names for their private FUBs; only the six
  macro layers + genuinely shared FUBs move to `mc_`-prefixed common.
- Core RTL stays vendor-clean through the whole reorg: zero FPGA primitives
  in anything that moves to common (verified clean today — primitive matches
  in the tree are comments, sim stubs, and build reports only).
- No RTL behavior changes in Phase 1; Phase 2 extraction must be
  diff-invisible per layer (same ports, same behavior, new home) before any
  parameterization lands.

## 6. Non-goals

- No new protocol support (no DDR5/LPDDR5 work; BG-mode items stay parked in
  the roadmap).
- No DE10-Standard (or any Intel/Quartus) bring-up. Recorded decision
  2026-10-09: DE10 is parked — its only DRAM path is the HPS hard controller,
  which caps the board at DMA/AMBA-class validation; revisit only if an
  obs-vs-real-OS-traffic campaign ever justifies it.
- No scheduler policy changes beyond making policy a parameter (FR-FCFS stays
  default; LPDDR personality designed but not tuned in this work).
- No product-IP content yet.

## 7. Risks

| Risk | Mitigation |
|---|---|
| The three axi4/scheduler sources differ more than expected | First plan step diffs all three layers and sizes the knob set before any extraction; if divergence is structural, fall back to per-protocol cores for that layer only |
| Move (Phase 1) breaks harness/filelist references silently | Reference sweep scripted + grep-verified (path literals in .f, .py, .tcl, .md, .rdl); full val suite green before Phase 1 commits |
| Common layer accretes speculative generality | Two-customer rule (§5); anything speculative stays in research |
| Extract-then-parameterize wants to happen in one step | Explicit sequencing: move → extract (diff-invisible) → parameterize, each with its own green run |

## 8. Success criteria

- Phase 1: three controllers under `mem-ctrl-research-ip/`, all suites green,
  zero stale path references.
- Phase 2: six common layers extracted, each with ≥2 MC customers; scoria
  training layer exists; PHY CSR contract doc committed; pumice + scoria
  timing/behavior unchanged (board campaigns re-run as final proof).
- Vault task areas mirror the new tree; indexes consistent
  (`bin/check_task_ids.py` clean).

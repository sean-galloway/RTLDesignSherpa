# mem-ctrl-ip Phase 2 — common-ip Layer Extraction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extract the six shared layers (`mc_common_pkg`, storage/timer FUBs, `mc_axi4_layer`, `mc_training_layer`, `mc_scheduler_layer`, `mc_storage_layer`, per-rev DFI layers) into `projects/components/mem-ctrl-ip/common-ip/`, each with ≥2 live research-MC customers, zero behavior change.

**Architecture:** Diff-invisible copy-rename first, then per-rock adoption in dependency order (pkg → FUBs → axi4 → training → scheduler → DFI). Each rock adoption is the RED→GREEN cycle: the naive common copy compiled against the next rock MUST fail at the exact divergence points; parameterize until green. Scheduler policy (FR-FCFS default; LPDDR alternative) becomes a parameter; storage (CAMs/SRAMs) lifts into a drop-in `mc_storage_layer`.

**Tech Stack:** SystemVerilog (IEEE 1800, Verilator lint + cocotb/pytest DV), repo make/pytest flow.

**Spec:** `docs/superpowers/specs/2026-10-09-mem-ctrl-ip-reorg-design.md` (§3 decisions, §4 Phase 2, §5 boundary rules, §8 success criteria). Where this plan and the spec differ on naming, the spec's §3.2 DFI naming yields to the as-built protocol rev found in the RTL (recorded in the task).

## Global Constraints

- **Zero behavior change.** Proven per rock by its own DV suite green at pre-extraction pass counts, plus `git diff -w` of the rock's RTL showing only instantiation/name changes (no logic edits inside unchanged modules).
- **Diff-invisible extraction, then parameterize — never both in one step.** The common copy must be byte-identical to its source (modulo `s/rock_/mc_/` renames) and lint-clean BEFORE any rock adopts it.
- **Adoption order is fixed:** pumice (first customer, reference logic) → scoria → andesite. Andesite's scheduler is +231 lines over scoria — see Task 5's ruling gate.
- **`mc_` prefix for all common modules; files live under `common-ip/rtl/{includes,macro,fub}/`.** Rock-prefixed module names never appear inside common RTL.
- **Two-customer rule** (spec §5): a common block ships only when the second rock compiles+passes against it. One-customer abstractions stay in the rock.
- **No duplicate module definitions:** when a rock adopts `mc_<fub>`, the rock's own `<fub>.f` filelist entry comes OUT of the rock's master filelist; the rock master `-f`s the common filelist instead. Lint closure must show exactly one definition of every module.
- **Package rule:** identifiers move to `mc_common_pkg`; rock pkgs `import mc_common_pkg::*;` and add rock-only items — never re-define a moved identifier.
- **DV environment:** `source env_python && source venv-cocotb2/bin/activate && export PYTHONPATH="$(pwd)/bin" PYTHONPYCACHEPREFIX=/tmp/pycache-<task>` (tooling BUG-018: shared-trunk pyc truncation race; private prefix mandatory).
- **Commit ritual:** `git status --porcelain` printed and eyeballed against the task's expected file list BEFORE every commit; staged foreign work is never included (Phase-1 review Critical #1). Pathspec commits listing exactly the task's files.
- **Commit with `export PATH="$(pwd)/venv/bin:$PATH"`** (hooks need venv python3.12); never `--no-verify`.

## Measured baseline (2026-10-09, drives this plan)

| Source | pumice | scoria | andesite | pum↔scor | scor↔and |
|---|---|---|---|---|---|
| `*_axi4_layer.sv` | 617 | 622 | 622 | 43 lines | 40 lines — almost all mechanical (names/pkg/comments) |
| `*_scheduler_layer.sv` | 646 | 782 | 877 | 232 lines | 477 lines — real divergence |
| `*_pkg.sv` | 151 | 140 | 145 | — | near-identical |
| training layer | yes | **NO** (blocks in scheduler: `scoria_wrlvl_ifc`) | yes (+`andesite_ca_train_ifc`, LPDDR4-only) | | |

## Review Focus

1. **Duplicate module definitions when a rock adopts an mc_* FUB** — the rock's stale `.f` entry plus the common filelist both compiling the same logic. Each adoption step's lint must prove single-definition.
2. **Package identifier collisions** — `memtype_e` and friends defined in both `mc_common_pkg` and a rock pkg silently break wildcard imports. Pinned by Task 1's lint of all three rocks.
3. **Parameter default drift** — common modules must not let a rock rely on a default that a later rock's adoption changes; every rock passes explicit parameters. Pinned by Task 3's scoria/andesite adoption diffs.
4. **cocotb TB hardcoded DUT names** — rock tbclasses that instantiate `pumice_axi4_layer` by name must follow the rock's swap to `mc_axi4_layer`. Pinned by the rock macro suites in Task 3.
5. **scoria's training split-out** — `scoria_wrlvl_ifc` currently lives in scoria's scheduler; the Task 4 split must keep scoria's `trn_cmd`/CDC contract intact with no scheduler behavior change. Pinned by scoria's scheduler + top suites.

---

### Task 1: `mc_common_pkg` + common-ip filelist/registry scaffolding

**Files:**
- Create: `projects/components/mem-ctrl-ip/common-ip/rtl/includes/mc_common_pkg.sv`
- Modify: `projects/components/mem-ctrl-ip/research-ip/{pumice-ddr2-lpddr2,scoria-ddr3-lpddr3,andesite-ddr4-lpddr4}/rtl/includes/*_pkg.sv`
- Modify: `bin/filelists.toml` (register `common-ip` filelist dirs + rtl_root)
- Create: `projects/components/mem-ctrl-ip/common-ip/rtl/filelists/includes/mc_common_pkg.f`, `common-ip/rtl/filelists/mc_all.f`; `common-ip/rtl/Makefile` (lint, mirroring any research-ip rtl/Makefile)

**Interfaces:**
- Consumes: nothing (first extraction)
- Produces: `mc_common_pkg` with `memtype_e {MEMTYPE_DDR2, MEMTYPE_LPDDR2, MEMTYPE_DDR3, MEMTYPE_LPDDR3, MEMTYPE_DDR4, MEMTYPE_LPDDR4}` (exact enumerator set verified from the union of the three rock pkgs), shared geometry/timing/DFI-rate types; all later tasks' common RTL imports this pkg. Later tasks rely on the common filelist names `mc_all.f` / per-block `.f` and the registry entry.

- [ ] **Step 1: Diff the three rock pkgs; write the knob inventory**

Run: `diff research-ip/pumice-ddr2-lpddr2/rtl/includes/pumice_pkg.sv research-ip/scoria-ddr3-lpddr3/rtl/includes/scoria_pkg.sv` and the other two pairs; classify every difference as `move-to-common` (identical shape, rock-neutral) or `rock-specific`.
Expected: an inventory in `common-ip/docs/mc_common_pkg_knobs.md` (create; 20-40 lines) listing what moves and what stays per rock.

- [ ] **Step 2: Write the failing lint** — add `mc_common_pkg.sv` (Step 3's content) is premature; instead write the adoption check first: modify `pumice_pkg.sv` to `import mc_common_pkg::*;` and delete its moved identifiers.

Run: `make -C research-ip/pumice-ddr2-lpddr2/rtl lint` — Expected: FAIL, `mc_common_pkg` not found.

- [ ] **Step 3: Implement `mc_common_pkg.sv`** — package containing exactly the `move-to-common` identifiers from Step 1, rock-neutral names. Header comment cites this plan + spec.

- [ ] **Step 4: pumice lint + suite green**

Run: `make -C research-ip/pumice-ddr2-lpddr2/rtl lint` then `make -C projects/components test-mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2`
Expected: lint PASS; suite green at pre-task counts.

- [ ] **Step 5: scoria and andesite adoption**

Same pkg edit for `scoria_pkg.sv`, `andesite_pkg.sv`; lint + `test-mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3` and `.../andesite-ddr4-lpddr4` green. Rock-specific identifiers stay in rock pkgs.

- [ ] **Step 6: Filelists + registry** — create `common-ip/rtl/filelists/includes/mc_common_pkg.f` (`+incdir+`, pkg source with `$REPO_ROOT` paths, matching the pumice filelist style); `mc_all.f` includes it; add the common-ip area to `bin/filelists.toml`; `python3 bin/filelist_registry.py --check` PASS.

- [ ] **Step 7: Commit** (pathspec: the files above; staged-set inspection first)

---

### Task 2: Timer + storage FUBs — `mc_bank_timer(s)`, `mc_global_timers`, intakes/CAMs/splitter/chopper

**Files:**
- Create: `common-ip/rtl/fub/mc_{bank_timer,bank_timers,global_timers,wr_intake,rd_intake,wr_data_cam,rd_cmd_cam,wr_splitter,axi_burst_chopper}.sv` + per-block `.f` filelists + `mc_all.f` updates
- Modify: the three rocks' `rtl/filelists/*` (swap rock entries → common `-f`) and any rock RTL that instantiates renamed children

**Interfaces:**
- Consumes: Task 1's pkg (timing/geometry types in ports stay rock-passed parameters — no pkg dependency changes in ports)
- Produces: the nine `mc_*` FUB module names that Task 3's `mc_axi4_layer` instantiates. Parameters = the union of the three rocks' parameter lists per FUB, with pumice's names as the canonical set.

- [ ] **Step 1: Parameter-union inventory** — for each of the 9 FUBs, `diff` the three rock implementations (note: pumice has unprefixed names for some, e.g. `addr_mapper`, `refresh_ctrl` — locate each rock's actual file via `ls research-ip/*/rtl/fub/`); write `common-ip/docs/mc_fub_knobs.md` listing per-FUB: canonical file, parameter union, confirmed-identical logic vs knob-requiring deltas. FUBs whose three-way diff is non-mechanical beyond knobs stay OUT (note them; two-customer rule) — `refresh_ctrl`, `addr_mapper`, `init_sequencer`, `mode_register`, `zq_ctrl`, `page_policy`, `cmd_arbiter` are candidates to DEFER to keep this task bounded; the nine listed above are the axi4/storage closure. Record deferrals in the knobs doc.

- [ ] **Step 2-4: Per-FUB extraction, adoption order pumice → scoria → andesite**, same cycle each:
  1. Create `mc_<fub>.sv` as a byte-copy of pumice's version with `s/pumice_/mc_/g` renames (module + internal refs). Verify: `git diff -w --no-index` pumice source vs mc copy shows only renamed lines; `verilator --lint-only` clean via a throwaway filelist.
  2. pumice adoption: swap the rock master filelist entry to `-f` the common block filelist; `make -C research-ip/pumice-ddr2-lpddr2/rtl lint` + pumice suite green.
  3. scoria adoption: swap scoria's entry; lint/suite. Expected RED at scoria's diff points; parameterize `mc_<fub>` (never scoria's copy) until green. If the delta is protocol behavior, not shape, see Ruling gate below.
  4. andesite adoption: same.

  **Ruling gate (per FUB, ledger it):** if the scoria or andesite delta is genuinely protocol-specific behavior that a parameter would falsify (e.g. DDR4-only command encodings inside a DDR2-shared FUB), leave that FUB OUT of common, keep both rock versions, and note it in `mc_fub_knobs.md` — two-customer rule satisfied by the other rocks.

- [ ] **Step 5: Full gates** — `python3 bin/filelist_registry.py --check` PASS; all three rock suites green; `git diff -w ea6d080..HEAD -- '*/research-ip/*'` shows no logic changes inside rock files that still exist (adoptions are filelist + instantiation edits only).

- [ ] **Step 6: Commit** (per-FUB or per-FUB-group commits welcome; pathspec-limited)

---

### Task 3: `mc_axi4_layer` (the measured-easy one: 40-43 line three-way divergence)

**Files:**
- Create: `common-ip/rtl/macro/mc_axi4_layer.sv` + `common-ip/rtl/filelists/macro/mc_axi4_layer.f`
- Modify: the three rocks' `rtl/top/*_core.sv` (instantiation swap), rocks' `rtl/macro/*_axi4_layer.sv` (**deleted** after their adoption), rock filelists, any rock tbclass that names the layer module

**Interfaces:**
- Consumes: Task 2's nine `mc_*` FUBs; Task 1's pkg
- Produces: `mc_axi4_layer` with pumice's parameter list as canonical (`AXI_ID_WIDTH`, `AXI_ADDR_WIDTH`, `DRAM_BEAT_WIDTH`, `RD_RET_DEPTH`, and the rest exactly as `pumice_axi4_layer.sv`'s header declares — copy verbatim). Task 4/5 assume cores instantiate `mc_axi4_layer`.

- [ ] **Step 1: Create `mc_axi4_layer.sv`** — byte-copy of `pumice_axi4_layer.sv`, `s/pumice_/mc_/g`, header comment updated (cites spec; notes scoria-parity provenance: `dv/tests/fub/test_scoria_pumice_logic_parity.py`). Diff-invisible verify + lint as in Task 2.
- [ ] **Step 2: pumice adoption** — `pumice_core.sv` instantiates `mc_axi4_layer`; pumice's `pumice_axi4_layer.sv` deleted; filelists updated (remove rock macro entry, add common `-f`); lint + pumice suite green (incl. `test_pumice_axi4_layer.py`).
- [ ] **Step 3: scoria adoption** — swap `scoria_core.sv`; scoria's `test_scoria_pumice_logic_parity.py` must still pass (it pins the shared-logic invariant). Parameterize the ~43-line divergence (expected: child parameter values, pkg imports already common; verify against the measured diff — anything beyond names/values gets a named parameter with both rocks passing explicit values).
- [ ] **Step 4: andesite adoption** — swap `andesite_core.sv`; andesite suite green. Same rule.
- [ ] **Step 5: Gates + commit.** Rock `*_axi4_layer.sv` files are gone from all three trees; `git grep -n '_axi4_layer' -- research-ip` shows only tb/docs references (update tbclasses to the new module name; docs references get a "renamed mc_axi4_layer" note, not a rewrite).

---

### Task 4: `mc_training_layer` + PHY calibration CSR contract doc

**Files:**
- Create: `common-ip/rtl/macro/mc_training_layer.sv`, `common-ip/docs/phy_cal_csr_contract.md`, filelists
- Modify: `research-ip/pumice-ddr2-lpddr2/rtl/macro/pumice_training_layer.sv` → deleted after adoption; `research-ip/scoria-ddr3-lpddr3/rtl/macro/scoria_scheduler_layer.sv` (**split-out ruling below**); andesite training adoption; rock cores/top filelists; rock tbclasses naming the layer

**Interfaces:**
- Consumes: Task 1 pkg; Task 2 FUBs where training references them
- Produces: `mc_training_layer` (pumice's parameter/port contract canonical); `phy_cal_csr_contract.md` — the documented PHY-mechanism abstraction later PHYs implement. Contract content (from the generated K7 PHY's CSR surface): per-group read-delay tap (rst/inc), read bitslip (rst/inc), write DQ/DQS delay (rst/inc), write bitslip, `wlevel_en`/`wlevel_strobe`, rd/wr phase, `dly_sel`, `half_sys8_taps`, command delay rst/inc; semantic requirements (monotonic taps, rst-then-inc idempotence, readback) stated behaviorally, not as vendor signals. Andesite's `ca_train_ifc` stays rock-specific (LPDDR4 CA training) — documented as the first contract non-covered mechanism.

- [ ] **Step 1: Write the contract doc skeleton first** (test-first for the interface): `phy_cal_csr_contract.md` v0 listing the K7 CSR map as the reference implementation with behavioral semantics. This doc is the acceptance target for Steps 2-4.
- [ ] **Step 2: Extract `mc_training_layer`** from pumice's (byte-copy + rename; pumice adoption; pumice suite green incl. training tests).
- [ ] **Step 3: andesite adoption** — parameterize deltas; **ca_train_ifc stays in andesite** (ruling, ledger it: LPDDR4-only mechanism, one customer). Andesite suite green.
- [ ] **Step 4: scoria split-out** — create `scoria_training_layer.sv` (new file) as scoria's training-block extraction FROM its scheduler (wrlvl_ifc usage + trn_cmd channel), then adopt `mc_training_layer` in scoria core. Scoria's scheduler suite + top suite green with **zero scheduler behavior change** (`git diff -w` on scoria scheduler shows only the extraction moves). This is Review Focus #5's pin.
- [ ] **Step 5: Contract doc final** — updated to reflect the as-built `mc_training_layer` ports/CSRs.
- [ ] **Step 6: Gates + commit.**

---

### Task 5: `mc_scheduler_layer` + `mc_storage_layer` (the hard one; ruling gates inside)

**Files:**
- Create: `common-ip/rtl/macro/mc_scheduler_layer.sv`, `common-ip/rtl/macro/mc_storage_layer.sv`, filelists
- Modify: pumice + scoria cores/schedulers (adoption); andesite (**ruling gate**); rock filelists; tbclasses

**Interfaces:**
- Consumes: Tasks 1-4 everything (scheduler sits atop all)
- Produces: `mc_scheduler_layer #(parameter memtype_e MEMTYPE, parameter policy_e SCHED_POLICY = POLICY_FR_FCFS, <timing/geometry knobs>)`; `mc_storage_layer` = the CAM/SRAM block set as a pipeline drop-in with the port contract both policies use. `policy_e {POLICY_FR_FCFS, POLICY_LP_SIMPLE}` — FR-FCFS default; the LPDDR personality proves the policy split (second policy need not be tuned, just real).

- [ ] **Step 1: Categorize the measured divergences** — `diff pumice scoria` (232 lines) and `diff scoria andesite` (477 lines) scheduler diffs, classified line-by-line into: prefix/rename, child-FUB set, timing-parameter usage, page/refresh policy, storage shape, genuine-architecture. Output: `common-ip/docs/mc_scheduler_knobs.md`. This inventory — not optimism — decides Steps 2-4.
- [ ] **Step 2: `mc_storage_layer` extraction** — the CAM/intake storage blocks (already `mc_*` from Task 2 where adopted) get their storage-facing port contract frozen as `mc_storage_layer`; pumice adoption green.
- [ ] **Step 3: pumice↔scoria scheduler merge** — `mc_scheduler_layer` from pumice's scheduler; scoria adopts; FR-FCFS parameterized; the 232-line diff's knob classes lift into parameters; storage drop-in proven by swapping `mc_storage_layer` between both without either suite noticing (test: both suites green with the other's storage parameter set where legal).
- [ ] **Step 4: andesite ruling gate** — classify per Step 1. If andesite's deltas are knob-class + policy: adopt (third customer). If architectural (e.g. its t3-scheduler structures don't map), ruling: andesite keeps a thin `andesite_scheduler_layer` composing `mc_storage_layer` + common timers + its own policy FUBs, and `mc_scheduler_layer` ships with two customers (pumice, scoria) — satisfies spec §5. Ledger the ruling with the evidence.
- [ ] **Step 5: LPDDR policy proof** — implement `POLICY_LP_SIMPLE` (minimal real policy: e.g. bank-strict FIFO without reorder) selectable per `MEMTYPE`; pumice in LPDDR2 config and andesite in LPDDR4 config both simulate init/refresh/basic traffic green through the policy path. Not tuned — proves the seam.
- [ ] **Step 6: Gates + commit.** All three rock suites green; `git grep -n '_scheduler_layer' -- research-ip` shows only docs/tb references.

---

### Task 6: Per-revision DFI layers (`mc_dfi_2p1_layer`, `mc_dfi_<scoria-rev>_layer`, andesite ruling)

**Files:**
- Create: `common-ip/rtl/macro/mc_dfi_2p1_layer.sv`, `mc_dfi_3p1_layer.sv` (name per as-built), filelists
- Modify: rock cores/top, rock `*_dfi_layer.sv` deleted post-adoption, filelists, tbclasses

**Interfaces:**
- Consumes: Task 1 pkg; per spec §3.2 DFI layers are standalone per rev (no shared core unless the second extraction proves byte-identical gear/CDC — evidence-driven, ledger it)
- Produces: version-named DFI layers; `mc_all.f` complete (the full six-layer closure: pkg, 9 FUBs + storage, axi4, training, scheduler, DFI)

- [ ] **Step 1: Protocol-rev verification** — read each rock's DFI layer header/docs; record the actual implemented rev per rock (pumice claims 2.1; scoria's docs claim 3.1; andesite claims 4.0). Name layers by AS-BUILT rev; note the naming in `mc_dfi_knobs.md` (spec §3.2's example names yield to as-built).
- [ ] **Step 2: pumice `mc_dfi_2p1_layer` extraction + adoption** (byte-copy-rename, diff-invisible, suite green).
- [ ] **Step 3: scoria DFI layer extraction + adoption** — scoria's is the second rev; IF its gear/CDC is byte-identical to pumice's underneath the rev-specific ports, lift the shared core (spec §3.2's evidence clause); else standalone. Suite green.
- [ ] **Step 4: andesite ruling gate** — andesite's DFI (4.0, more phases) either adopts with knobs (third customer) or stays rock with a documented reason (two-customer rule already satisfied). DFI 4.x signal additions that pumice/scoria can't express are the expected reason; ledger it.
- [ ] **Step 5: Final full gates** — all three rock suites green; `filelist_registry.py --check` PASS; `check_broken_links.py` 0 broken; `check_task_ids.py` clean; `git grep -n 'mem-ctrl-ip/(pumice|scoria|andesite)'` zero; `python3 bin/filelist_registry.py --blindspots` shows no new blind spots.
- [ ] **Step 6: Commit + Phase-2 completion report** (spec §8 success criteria, point by point).

---

## Self-Review Notes

- **Spec coverage:** §3.1→T3, §3.2→T6, §3.3→T2/T5, §3.4→T4, §3.5/3.6→naming+product untouched, §4 Phase-2 order→T1-T6, §5 rules→Global Constraints + per-task ruling gates, §6 non-goals→out of plan, §8→T6 Step 6.
- **Proportion:** measured baseline + ruling gates carry the risk; no RTL transcribed. Steps are adoption cycles with named verification commands.
- **Known deferrals (recorded, not silently dropped):** non-axi4 FUBs (refresh/init/mode_register/zq/page_policy/cmd_arbiter/addr_mapper) defer past Task 2 unless their three-way diff is mechanical; andesite architectural deltas ruled per-task rather than forced.

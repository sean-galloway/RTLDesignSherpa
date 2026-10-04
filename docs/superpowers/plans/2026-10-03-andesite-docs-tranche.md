# andesite-ddr4-lpddr4 documentation tranche — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Land the andesite DDR4/LPDDR4 controller's documentation tranche — family-level shared-core docs, the HAS, the MAS, and the generated kmap book — in that order, each book owner-reviewed before the next starts.

**Architecture:** Documentation only; no RTL/DV/formal changes. One DDR4-led book set with LPDDR4 per-chapter deltas, scoria as the reuse pool (markings relative to scoria: INHERITED/MODIFIED/NEW), DFI 4.0 boundary, fixed geometry (DDR4-1600 x8 = 4 BG × 4 banks; LPDDR4-1600 x16 = 8 banks/channel), sim-only. The `mem_ctrl_pkg` shared-core design lives at family level (`mem-ctrl-ip/docs/`), referenced — not owned — by the andesite HAS ch5.

**Tech Stack:** Markdown books (house documentation header + styles yaml + graphviz assets), Python generator on `bin/kmaps` (`qm_minimize`, `KmapWriter`, `contract_sheet`, `verify_citations`) producing the xlsx + markdown, vault task lanes per the tasks convention.

**Spec:** `docs/superpowers/specs/2026-10-03-andesite-bootstrap-design.md`

## Global Constraints

- **Docs only.** No file under any `rtl/`, `dv/`, or `formal/` tree is created or modified. scoria and pumice trees are read-only sources; their books are cited, never edited.
- **Evidentiary rule** (carried from scoria's HAS): every claim is (a) inherited from a named source, (b) cited to a JEDEC/DFI clause, or (c) recorded as an open question. No DFI 4.0 spec exists on disk: any DFI 4.0 claim whose clause number cannot be verified in-house is suffixed `§TBC(TASK-004)` — a grep gate enforces the suffix exists wherever `DFI 4.0` appears in ch04.
- **Exact geometry, verbatim:** DDR4-1600 x8, **4 bank groups × 4 banks = 16 banks**, MT40A1G8-class; LPDDR4-1600 x16, **8 banks per channel**, no bank groups; timings are runtime CSRs. These strings must match across ch02 and ch05 (grep gate).
- **Markings are relative to scoria** and must be identical everywhere a block appears (ch02 tables, ch03 narrative, block diagram): INHERITED / MODIFIED / NEW only.
- **No offsets in books:** registers are name-based (offsets live in the future RDL/generated docs), per house rule.
- **House style:** every `.md` carries the documentation header block; each book has an index + styles yaml; diagrams are generated from `.dot` via `regenerate_all_graphviz.sh` (never hand-edit a PNG); the kmap xlsx is generated only by `gen_andesite_kmaps.py` (never hand-edit the workbook).
- **Gates before every commit:** `python3 bin/check_task_ids.py` PASS; pre-commit hooks PASS (markdown links, emoji, doc-instantiation). Vault INDEX updates land in the same commit as the task files they touch.
- **Book boundaries are review gates:** Tasks 7, 10, 12 end a book with an owner-review step; do not start the next book until the owner approves.
- One commit per task, message prefix `docs(andesite):` / `docs(mem-ctrl-ip):` / `docs(tasks):`.

## Review Focus

1. **Marking drift between the three surfaces** — a block marked MODIFIED in ch02's table but described as inherited in ch03's prose, or colored wrong in the diagram. → Task 7's consistency grep pins every block name + marking pair across all three.
2. **Unverifiable DFI 4.0 citations** — with no 4.0 spec on disk, invented clause numbers would read as evidence. → Task 5's grep gate requires `§TBC(TASK-004)` on every DFI 4.0 mention in ch04; Task 4's gate does the same for ch04-adjacent mentions.
3. **Silent DDR4-only content** — LPDDR4 deltas must exist wherever DDR4 behavior is architecture-binding (command path, init, refresh, training, datapath). → Task 4 step greps each ch03 file for its LPDDR4 paragraph.
4. **Geometry numbers drifting between chapters** (4×4=16 vs 8-bank stated differently in ch02 vs ch05). → Task 6 greps the exact strings.
5. **Kmap workbook drift** — hand-edited xlsx or stale markdown renderings. → Task 11/12 rerun the generator and require byte-identical/regenerated outputs + the citation gate (`verify_citations`) green.

---

### Task 1: Vault lane + family docs seed

**Files:**
- Create: `vault/Tasks/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/task/{open,active,closed,dropped,deferred}/.gitkeep`
- Create: `vault/Tasks/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/task/open/TASK-000.md` (template, mirrors bch's TASK-000)
- Create: `vault/Tasks/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/task/open/TASK-001.md` (HAS + family docs seed), `TASK-002.md` (MAS), `TASK-003.md` (kmaps), `TASK-004.md` (DFI 4.0 BFM study)
- Create: `vault/Tasks/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/task/INDEX.md` (mirrors `vault/Tasks/projects/components/ecc-ip/bch/task/INDEX.md` shape; Next ID TASK-005)
- Create: `vault/Tasks/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/INDEX.md` (area rollup; Next ID TASK-005; cites the spec)
- Create: `projects/components/mem-ctrl-ip/docs/INDEX.md`
- Create: `projects/components/mem-ctrl-ip/docs/01_mem_ctrl_pkg.md`
- Create: `projects/components/mem-ctrl-ip/docs/02_family_doctrine.md`
- Create: `projects/components/mem-ctrl-ip/docs/03_dfi_boundary_lineage.md` (v0.1 stub: purpose + pointers to pumice/scoria ch04)
- Create: `projects/components/mem-ctrl-ip/docs/04_jedec_generation_deltas.md` (v0.1 stub: purpose + pointers)
- Modify: `projects/components/mem-ctrl-ip/README.md` (add a `docs/` pointer line)

**Interfaces:**
- Produces: task IDs `andesite TASK-001..004` cited in commit messages and later book ch06; family doc paths `mem-ctrl-ip/docs/01..04` cited by HAS ch1/ch4/ch5 (Tasks 2-6); the INDEX ownership rule quoted by later tasks.

- [ ] **Step 1: Mirror the bch vault lane.** Copy the lane shape from `vault/Tasks/projects/components/ecc-ip/bch/` (lanes, state dirs, INDEX.md wording, TASK-000 template). Write the four open tasks with one-paragraph scopes taken verbatim from the spec §5 Ch6 filing; TASK-004 notes the DFI 4.0 spec is not on disk.

- [ ] **Step 2: Write the family docs seed.** `01_mem_ctrl_pkg.md`: two-bit memtype enum `{DDR2,DDR3,DDR4,LPDDR2,LPDDR3,LPDDR4}` (values assigned), shared timing-struct inventory (named, not fielded), the scoria/pumice migration plan with conditions, recorded deferral to andesite RTL bring-up. `02_family_doctrine.md`: config-not-param; maintenance request/grant never-preempt; AXI4 host-side shape; marking semantics; the evidentiary rule. `INDEX.md`: the ownership rule (family docs own what no single controller owns). 03/04: purpose paragraph + pointers only (v0.1 stubs, marked as such).

- [ ] **Step 3: Verify.** Run: `python3 bin/check_task_ids.py` → PASS; `grep -c "Next ID: TASK-005" vault/Tasks/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/INDEX.md vault/Tasks/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/task/INDEX.md` → 2 matches.

- [ ] **Step 4: Commit**

```bash
git add vault/Tasks/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4 projects/components/mem-ctrl-ip/docs projects/components/mem-ctrl-ip/README.md
git commit -m "docs(tasks): file andesite TASK-001..004; docs(mem-ctrl-ip): family docs seed (mem_ctrl_pkg design, doctrine, INDEX)"
```

### Task 2: HAS skeleton + ch00 + ch01

**Files:**
- Create: `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_has/andesite_has_index.md`
- Create: `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_has/andesite_has_styles.yaml` (copy scoria's, retitle DDR4/LPDDR4)
- Create: `.../andesite_has/ch00_front_matter/00_document_info.md`
- Create: `.../andesite_has/ch01_introduction/{01_purpose,02_conventions,03_definitions}.md`

**Interfaces:**
- Consumes: Task 1's family doc paths (cited in ch01 conventions).
- Produces: document title string "andesite DDR4/LPDDR4 Family Controller — Hardware Architecture Specification"; version v0.1, date 2026-10-03; chapter numbering (ch01..ch06) that Tasks 3-7 and the MAS index reference.

- [ ] **Step 1: Write the index + styles.** Index mirrors `scoria_has_index.md` shape (title, version/date/status block, "Read this first" blockquote, provenance section); status says v0.1 written from the delta analysis before RTL exists, per the spec.

- [ ] **Step 2: Write ch00.** Document info table (Title/Version 0.1/Date/Status/Scope/Not-in-scope: "The PHY; board bring-up; the DDR5 features DFI 4.x also carries"), related-documents table (spec, scoria HAS, family docs 01-04, JESD79-4, JESD209-4, DFI 4.0 marked §TBC(TASK-004)), terminology, revision history with the single 0.1 row.

- [ ] **Step 3: Write ch01.** `01_purpose`: the inheritance sentence (scoria is the reuse pool; markings relative to scoria) + success criteria from spec §1. `02_conventions`: marking semantics; the family-docs pointer; the evidentiary rule; "config not param". `03_definitions`: bank group, tCCD_L/tCCD_S, tRRD_L/S, FGR, gear-down, CA parity, DBI, MPC, REFpb-vs-controller-directed refresh.

- [ ] **Step 4: Verify + commit.** `grep -c "§TBC(TASK-004)" ch00_front_matter/00_document_info.md` ≥ 1; pre-commit hooks via commit:

```bash
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_has
git commit -m "docs(andesite): HAS v0.1 skeleton -- index, styles, ch00 front matter, ch01 introduction"
```

### Task 3: HAS ch02 overview

**Files:**
- Create: `.../andesite_has/ch02_overview/{01_scope,02_block_diagram,03_module_hierarchy,04_design_point}.md`
- Create: `.../andesite_has/assets/graphviz/01_block_diagram.dot` and `01_block_diagram.png` (generated)

**Interfaces:**
- Consumes: spec §5 ch2 (scope, design point) and §5 ch3 table (the ten delta areas — the marking list's source of truth).
- Produces: the **marking table** (every scoria module → INHERITED/MODIFIED/NEW + cause + chapter pointer) that Task 4's prose, the diagram, and Task 7's consistency gate all use; the design-point strings.

- [ ] **Step 1: Write `03_module_hierarchy.md`.** Top/macro tier table (mirroring scoria's Table 2.1) and FUB tables (2.2 modified, 2.3 new) — the complete marking list: every scoria module from scoria's ch02/ch03 tables appears exactly once with its andesite marking per spec §5 ch3 (e.g. `addr_mapper` MODIFIED bank-group decode; `odt_ctrl` NEW; `refresh_ctrl` MODIFIED FGR; inherited-unchanged blocks listed in the inherited prose with the count "20 of the 24 FUBs" pattern recounted against scoria's actual inventory — count verified by listing scoria's rtl/fub + rtl/macro + rtl/top module set).

- [ ] **Step 2: Write `01_scope.md` + `04_design_point.md`.** Scope: DDR4-led, LPDDR4 per-chapter deltas, sim-only (7-series targets carry no DDR4; no board named). Design point: the exact geometry strings from Global Constraints; DFI 4.0 BFM boundary; timings runtime CSRs; the "one bitstream characterizes" doctrine cited to family docs 02.

- [ ] **Step 3: Write the block diagram.** `01_block_diagram.dot` modeled directly on scoria's dot (same clusters/colors: green INHERITED, amber MODIFIED, red NEW): copy scoria's topology, recolor/mark the MODIFIED set (addr_mapper, cmd_formatter, init_sequencer, mode_register, refresh_ctrl, scheduler/arbiter, global_timers, dfi datapath blocks, csr) and add red nodes for NEW (`odt_ctrl`, training blocks, parity/alert handling, LPDDR4 command path). Run `bash assets/graphviz/regenerate_all_graphviz.sh`; Read the PNG back to confirm colors/labels render.

- [ ] **Step 4: Verify + commit.** `grep -c "MODIFIED" ch02_overview/03_module_hierarchy.md` ≥ 8; `grep -c "4 bank groups" ch02_overview/04_design_point.md` = 1; commit:

```bash
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_has
git commit -m "docs(andesite): HAS ch02 -- scope, design point, module hierarchy markings, block diagram"
```

### Task 4: HAS ch03 architecture deltas

**Files:**
- Create: `.../andesite_has/ch03_architecture/01_deltas.md`
- Create: `.../andesite_has/ch03_architecture/02_init_zq.md`
- Create: `.../andesite_has/ch03_architecture/03_training.md`
- Create: `.../andesite_has/ch03_architecture/04_refresh.md`
- Create: `.../andesite_has/ch03_architecture/05_odt.md`
- Create: `.../andesite_has/ch03_architecture/06_lpddr4_deltas.md`

**Interfaces:**
- Consumes: Task 3's marking table (must not contradict it); spec §5 ch3 rows 1-10; scoria's ch03 chapters (style + what "inherited" means per block); scoria's `design-requirements.md` §6 (TASK-001 modes andesite inherits as policy base).
- Produces: per-area delta narratives the MAS (Tasks 8-10) expands; the deferred list (write CRC, LPDDR4 DVFS/DSM, self-refresh scheduling) and dormant disposition (`powerdown_ctrl`/`dfi_signal_pack` dormant with named condition) that ch06 references.

- [ ] **Step 1: Write `01_deltas.md`.** The ten-row delta table from spec §5 ch3 verbatim, then per-area paragraphs: what DDR4 changes, which scoria blocks absorb it, the marking, and the chapter pointer. Close with the full reuse table (every scoria module, marking, cause — the same content as ch02's tables, presented as the argument) and the dormant/deferred paragraphs.

- [ ] **Step 2: Write the five area chapters.** `02_init_zq.md`: reset procedure, MR0–MR6 order, gear-down entry, parity enable; ZQ carried from scoria (zq_ctrl INHERITED for DDR4; LPDDR4 MPC path NEW). `03_training.md`: inherited write leveling; NEW read leveling (MPR-based); LPDDR4 CA/WDQ training; search-in-firmware per D2 precedent. `04_refresh.md`: FGR 1x/2x/4x via MR3; LPDDR4 controller-directed per-bank refresh; the inherited elastic/TCR/placement modes cited as the policy base (scoria TASK-001). `05_odt.md`: dynamic ODT, RTT_NOM/WR/PARK, ODT latencies; NEW `odt_ctrl`; scoria's static-ODT insufficiency stated. `06_lpdrr4_deltas.md`: no bank groups (8 banks/channel), 2-channel x16, MPC command bus, DSM power states deferred with named condition.

- [ ] **Step 3: Verify (Review Focus 2 + 3).** `grep -L "LPDDR4" ch03_architecture/*.md` → must list only `01_deltas.md` (every area chapter names its LPDDR4 delta; 01 carries the pointer table). `grep -c "§TBC(TASK-004)" ch03_architecture/*.md` summed ≥ 1 if any DFI 4.0 claim appears, else 0 (record the result in the commit message).

- [ ] **Step 4: Commit**

```bash
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_has/ch03_architecture
git commit -m "docs(andesite): HAS ch03 -- DDR4/LPDDR4 architecture deltas vs scoria, ten areas + dormant/deferred"
```

### Task 5: HAS ch04 interfaces

**Files:**
- Create: `.../andesite_has/ch04_interfaces/{01_dfi_v40,02_axi4_apb}.md`

**Interfaces:**
- Consumes: scoria's `ch04_interfaces/01_dfi_v31.md` (what transfers); family doc `03_dfi_boundary_lineage.md` (Task 1); spec §5 ch4.
- Produces: the DFI 4.0 signal inventory (dfi_act_n, alert_n path, gear-down handshake, parity, dfi_dbi_*) the MAS ch03 (Task 10) pins at pin level.

- [ ] **Step 1: Write `01_dfi_v40.md`.** The 3.1→4.0 delta table (signal/behavior added, what scoria drove at 3.1, what andesite drives at 4.0, frequency ratios); what transfers unchanged (phasemultiplied buses, cdc shape). Citation discipline: named signals are public and stated plainly; clause numbers are `§TBC(TASK-004)` everywhere.

- [ ] **Step 2: Write `02_axi4_apb.md`.** Host side unchanged in shape from scoria (AXI4 + APB slave + PeakRDL name-based regmap rule); offsets-not-in-books rule restated; the regmap generation rule carried (house peakrdl wrapper when the RDL lands).

- [ ] **Step 3: Verify (Review Focus 2 gate).** `grep -n "DFI 4.0" .../01_dfi_v40.md | grep -v "§TBC(TASK-004)" | grep -v "^.*:.*|.*§TBC"` → empty (every DFI 4.0 mention carries the suffix or lives in a table cell that includes it); `grep -c "dfi_act_n" .../01_dfi_v40.md` ≥ 2.

- [ ] **Step 4: Commit**

```bash
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_has/ch04_interfaces
git commit -m "docs(andesite): HAS ch04 -- DFI 4.0 boundary deltas, AXI4/APB host side"
```

### Task 6: HAS ch05 parameters

**Files:**
- Create: `.../andesite_has/ch05_parameters/01_package_and_params.md`

**Interfaces:**
- Consumes: family doc `01_mem_ctrl_pkg.md` (Task 1; ch5 references, does not restate); Task 3's design-point strings.
- Produces: `andesite_pkg` initial-content list (memtype enum from mem_ctrl_pkg, geometry parameters, opcodes new to this tier) the MAS ch01 references.

- [ ] **Step 1: Write the chapter.** mem_ctrl_pkg reference paragraph; `andesite_pkg` initial content: geometry fixed at 4 BG × 4 banks (DDR4) / 8 banks per channel (LPDDR4), the two-bit memtype note, new opcodes (BG-aware ACT, MPC for LPDDR4, FGR refresh classes); the build-time vs runtime table (geometry build, every timing runtime CSR — including the L/S pairs); the package-duplication note (three near-identical packages deliberate and time-boxed, cited to family doc 01).

- [ ] **Step 2: Verify (Review Focus 4).** `grep -c "4 bank groups × 4 banks" ch05_parameters/01_package_and_params.md` = 1; `grep -c "8 banks per channel"` = 1; both strings byte-identical to `ch02_overview/04_design_point.md` (`diff <(grep -h "bank groups" ch0[25]*/*.md | sort -u | wc -l) <(echo 1)` → 0).

- [ ] **Step 3: Commit**

```bash
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_has/ch05_parameters
git commit -m "docs(andesite): HAS ch05 -- parameters, andesite_pkg content, mem_ctrl_pkg reference"
```

### Task 7: HAS ch06 + book assembly (OWNER REVIEW GATE)

**Files:**
- Create: `.../andesite_has/ch06_integration/01_verification_open.md`
- Modify: `.../andesite_has/andesite_has_index.md` (status → complete v0.1)
- Modify: `.../andesite_has/ch00_front_matter/00_document_info.md` (revision row if any chapter drifted)

**Interfaces:**
- Consumes: all HAS chapters (assembly + consistency gate); the vault lane (Task 1).
- Produces: the reviewed HAS v0.1 the MAS (Tasks 8-10) cites; the open-questions list feeding TASK-004 and the MAS.

- [ ] **Step 1: Write ch06.** Verification strategy: sim-only against a DFI 4.0 BFM; the BFM acquisition/study task = andesite TASK-004 (no BFM exists in-house); inherited-bring-tests argument from scoria/pumice cited. Open-questions table: write CRC, gear-down coverage scope, CA-parity scope, LPDDR4 DVFS/DSM, BFM provenance, DFI 4.0 clause confirmation — each with a named condition. "What would make this a 1.0" (block-by-block confirmation against RTL when it exists; CSR map from RDL — same posture as scoria).

- [ ] **Step 2: Consistency gate (Review Focus 1).** Extract every `module-name MARKING` pair from `ch02_overview/03_module_hierarchy.md` and `ch03_architecture/01_deltas.md`; `comm -3` of the two sorted lists must be empty. `grep -o "fillcolor=\"#[0-9a-f]*\"" assets/graphviz/01_block_diagram.dot | sort | uniq -c` sanity vs the color legend (green/amber/red all present). Fix any drift found — the gate is the point, not a formality.

- [ ] **Step 3: Assemble + gates.** Index status updated; `python3 bin/check_task_ids.py` PASS; regenerate graphviz (byte-stable); commit:

```bash
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_has vault/Tasks/projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4
git commit -m "docs(andesite): HAS ch06 + assembly -- verification strategy, open questions, v0.1 book complete"
```

- [ ] **Step 4: OWNER REVIEW.** Present the book (index + ch02/ch03 highlights) to the owner; incorporate corrections; close `andesite TASK-001` (`git mv` to closed/, INDEX counts, per the tasks convention) in a follow-up commit `docs(tasks): close andesite TASK-001 (HAS v0.1)`. Do not start Task 8 until approved.

### Task 8: MAS skeleton + ch01 overview

**Files:**
- Create: `.../andesite_mas/andesite_mas_index.md`
- Create: `.../andesite_mas/ch00_front_matter/00_document_info.md`
- Create: `.../andesite_mas/ch01_overview/{01_block_inventory,02_what_changes_vs_scoria}.md`

**Interfaces:**
- Consumes: HAS v0.1 chapter numbering and block names (must match exactly); bch_mas shape.
- Produces: MAS chapter numbering (ch02 per-block pages) and the block-inventory table Tasks 9-10 expand; the "referenced not rewritten" inheritance list.

- [ ] **Step 1: Skeleton.** Index + styles (mirroring andesite_has), ch00 (v0.1, date, status: expands the HAS's changed/new blocks; inherited-unchanged blocks referenced to scoria's books with where-and-why).

- [ ] **Step 2: ch01.** `01_block_inventory.md`: every changed/new block with its MAS ch02 page name and HAS pointer. `02_what_changes_vs_scoria.md`: one paragraph per block, same markings as the HAS (consistency gate: markings copied, not re-derived).

- [ ] **Step 3: Verify + commit.** `grep -c "ch02_blocks/" 01_block_inventory.md` = number of changed/new blocks listed (≥ 8: cmd_formatter, init_sequencer, mode_register, addr_mapper, scheduler/arbiter, refresh_ctrl, zq_ctrl, odt_ctrl, training, dfi datapath); commit:

```bash
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_mas
git commit -m "docs(andesite): MAS v0.1 skeleton -- index, ch00, ch01 block inventory"
```

### Task 9: MAS ch02 per-block chapters

**Files:**
- Create: `.../andesite_mas/ch02_blocks/<one file per changed/new block>.md` (names from Task 8's inventory; each mirrors bch_mas ch02_blocks shape: purpose, interface table, behavior/FSM policy, telemetry, what-changes-vs-scoria)

**Interfaces:**
- Consumes: HAS ch03 area chapters (the argument) — the MAS is the mechanism; scoria module headers for inherited internals; spec §6.
- Produces: the per-block expressions (exact equations, FSM state lists, encoding tables) the kmap generator's citations point at (Tasks 11-12).

- [ ] **Step 1: Write the encoding/mechanism chapters.** `01_cmd_formatter.md` (ACT_n/BG command encodings; LPDDR4 CA-bus table), `02_init_sequencer.md` (reset FSM states, MR0–6 order, gear-down entry), `03_mode_register.md` (MR0–6 field maps per memtype), `04_addr_mapper.md` (BG/channel decode equations), `05_scheduler.md` (L/S scheduling policy, tCCD_L/S gating), `06_refresh_ctrl.md` (FGR on the inherited elastic/TCR/placement base), `07_zq_ctrl.md` (MPC path), `08_odt_ctrl.md` (RTT_NOM/WR/PARK policy, ODT latencies), `09_training.md` (read leveling, CA training — firmware-search per D2), `10_dfi_datapath.md` (DBI).

- [ ] **Step 2: Verify (Review Focus 3).** Every chapter file contains its LPDDR4 paragraph: `for f in ch02_blocks/*.md; do grep -q "LPDDR4" "$f" || echo "MISSING: $f"; done` → empty (or justified in the commit message).

- [ ] **Step 3: Commit**

```bash
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_mas/ch02_blocks
git commit -m "docs(andesite): MAS ch02 -- changed/new block microarchitecture"
```

### Task 10: MAS ch03 + ch04 + assembly (OWNER REVIEW GATE)

**Files:**
- Create: `.../andesite_mas/ch03_interfaces/01_dfi40_pins.md`
- Create: `.../andesite_mas/ch04_contracts/01_core_contracts.md`
- Modify: `.../andesite_mas/andesite_mas_index.md`

**Interfaces:**
- Consumes: MAS ch02 (signals named there are the contract rows); HAS ch04 (boundary).
- Produces: the contract rows + citation anchors (file:line) the kmap generator cites.

- [ ] **Step 1: ch03.** DFI 4.0 pin-level table (name, direction, clock, reset value, source block) — every signal HAS ch04 names appears here; `§TBC(TASK-004)` discipline identical.

- [ ] **Step 2: ch04.** Core signal contracts in bch ch04 style (valid/ready shape, reset, ordering) for the changed/new blocks; each contract row cites its defining MAS ch02 file (anchor the kmap generator will verify).

- [ ] **Step 3: Assemble + gates.** Index complete; marking-consistency grep from Task 7 re-run against `ch01_overview/02_what_changes_vs_scoria.md`; `check_task_ids.py` PASS; commit `docs(andesite): MAS ch03/ch04 + assembly -- DFI 4.0 pins, contracts, v0.1 book complete`.

- [ ] **Step 4: OWNER REVIEW** (as Task 7 Step 4); close `andesite TASK-002` on approval. Do not start Task 11 until approved.

### Task 11: Kmap generator + DDR4 command table (pipeline proof)

**Files:**
- Create: `.../docs/kmaps/gen_andesite_kmaps.py`
- Create: `.../docs/kmaps/andesite_cmd_kmaps.xlsx` (generated)
- Create: `.../docs/kmaps/generated/01_ddr4_command_table.md` (generated)

**Interfaces:**
- Consumes: `bin/kmaps` (`qm_minimize`, `sop_str`, `KmapWriter`, `contract_sheet`, `verify_citations` — read the bch generator and `bin/kmaps/writer.py` first); MAS ch02 files (citation targets).
- Produces: the generator CLI (`python3 docs/kmaps/gen_andesite_kmaps.py` rerunnable/idempotent from repo root or docs/kmaps, mirroring the bch invocation) and the DDR4 command truth table both later tasks extend.

- [ ] **Step 1: Write the generator.** Mirror `gen_bch_signal_contracts_kmaps.py` structure: xlsx built from scratch via openpyxl + bin/kmaps; markdown renderings emitted under `generated/`; `CITES` list with `(file, line, text)` anchors into MAS ch02 (run `verify_citations` at end — hard fail on drift, exactly as bch does). First table only: the DDR4 command truth table (ACT_n×RAS_n×CAS_n×WE_n → op name), minimized via `qm_minimize` for the qualifier SOPs, emitted as xlsx K-MAP sheet + `generated/01_ddr4_command_table.md`.

- [ ] **Step 2: Run + verify (Review Focus 5).** Run: `cd projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4 && python3 docs/kmaps/gen_andesite_kmaps.py` → exits 0, citation gate green; rerun → byte-identical xlsx and markdown (`sha256sum` before/after). `grep -c "RD\b\|WR\b\|ACT\b" generated/01_ddr4_command_table.md` ≥ 3 (the core ops present).

- [ ] **Step 3: Commit (generated artifacts in the same commit as the generator)**

```bash
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/kmaps
git commit -m "docs(andesite): kmap generator + DDR4 command truth table (citation-gated)"
```

### Task 12: Remaining kmap tables + book integration (OWNER REVIEW GATE)

**Files:**
- Modify: `.../docs/kmaps/gen_andesite_kmaps.py` (add tables)
- Regenerate: `.../docs/kmaps/andesite_cmd_kmaps.xlsx`, `.../docs/kmaps/generated/*.md`
- Create: `.../docs/kmaps/README.md` (what's generated, how to rerun)
- Modify: `.../andesite_mas/ch04_contracts/01_core_contracts.md` + `.../andesite_has/ch03_architecture/01_deltas.md` (citation lines to the generated tables)

**Interfaces:**
- Consumes: Task 11's generator; MAS ch02 anchors.
- Produces: the complete kmap book; cross-citations from MAS/HAS.

- [ ] **Step 1: Add the remaining tables.** LPDDR4 CA-bus command table; address/bank-group decode maps (row/col/BG/channel bit fields); MR0–MR6 per-field programming maps (both memtypes); ODT truth table (RTT_NOM/WR/PARK × DRAM state); FGR refresh-mode select map. Each rendered to `generated/*.md` and the xlsx.

- [ ] **Step 2: Regenerate + idempotence.** Run the generator; `sha256sum` rerun check as Task 11; citation gate green.

- [ ] **Step 3: Integrate.** MAS ch04 and HAS ch03 cite the generated tables (one line each, citing `generated/NN_*.md`); README documents rerun. Gates: `check_task_ids.py`; hooks; commit `docs(andesite): kmaps complete -- LPDDR4 CA, decode maps, MR0-6, ODT, FGR; cited from MAS/HAS`.

- [ ] **Step 4: OWNER REVIEW** (whole tranche walkthrough); close `andesite TASK-003` on approval; final commit `docs(tasks): close andesite TASK-003 (kmaps) -- docs tranche complete`.

---

## Self-review notes (2026-10-03)

- **Spec coverage:** §4 layout → Tasks 1-2; §5 ch1-ch6 → Tasks 2-7; §6 MAS → Tasks 8-10; §7 kmaps → Tasks 11-12; §8 sequencing/gates → Global Constraints + review steps; §9 out-of-scope → Global Constraints (docs-only). The PRD rewrite stays out (spec §9).
- **Step scan:** every write-step names its file and content source; every verify-step has a command + expected output; no step writes a chapter's prose for the implementer beyond pinned strings.
- **Type/name consistency:** block file names (`01_cmd_formatter.md` … `10_dfi_datapath.md`) are fixed here and reused by Tasks 9-12; family doc names (`01_mem_ctrl_pkg.md` …) fixed in Task 1 and reused verbatim in Tasks 2/5/6; task IDs fixed in Task 1 and reused in ch06/commit messages.
- **Review Focus:** five items, each pinned to an owning task's verify step (Tasks 4, 5, 6, 7, 11/12).
- **Proportion:** plan ≈ spec length; prose authoring deliberately left to the implementer against the spec's tables.

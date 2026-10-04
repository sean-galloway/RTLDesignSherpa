# andesite-ddr4-lpddr4 bootstrap — design spec

**Date:** 2026-10-03
**Status:** brainstormed with the owner; approved to write the spec; amended 2026-10-03
(the mem_ctrl_pkg design and family doctrine move to a family-level `docs/`, per
the owner's review)
**Deliverable of this tranche:** documentation only — the andesite HAS, then the
MAS, then the kmap book. RTL bootstrap is a follow-on implementation plan, written
after this spec via superpowers:writing-plans.

## 1. Intent

Start `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/` — the DDR4/LPDDR4
family memory controller — by taking as much as possible from scoria
(`scoria-ddr3-lpddr3`), whose 24-FUB inventory, books, CSR flow, and verification
apparatus are the immediate reuse pool. The owner-set sequencing is explicit:
**write the HAS, then the MAS, then the kmap book.**

Success looks like: three committed, house-styled books under
`andesite-ddr4-lpddr4/docs/` — a Hardware Architecture Specification that a reader
can trace block-by-block to scoria's, a Microarchitecture Specification covering the
changed and new blocks in depth, and a generated kmap book pinning the DRAM command
and mode-register encodings — **plus a family-level `mem-ctrl-ip/docs/` seed** owning
the shared-core design and doctrine — and the vault tasks that make the follow-on
RTL work trackable.

## 2. Scope decisions (owner answers, 2026-10-03)

| Question | Decision |
|---|---|
| This pass's deliverable | **Docs tranche only**: HAS → MAS → kmaps. RTL bootstrap is the follow-on plan. |
| PHY boundary | **DFI 4.0** (DDR4-era interface: ACT_n, gear-down, CA parity/alert_n, DBI wires). No in-house 4.0 BFM yet — acquisition/study is a named task. |
| Design point geometry | **DDR4-1600 x8, 4 bank groups × 4 banks = 16 banks** (MT40A1G8-class) + **LPDDR4-1600 x16, 8 banks per channel** (no bank groups). Timings stay runtime CSRs. |
| Kmap book depth | **Command-encoding focused**: DRAM command truth tables (incl. LPDDR4 CA bus), address/bank-group decode, MR0–MR6 programming maps, ODT and refresh-mode selects — for the changed/new blocks. Generated with `bin/kmaps`, xlsx + markdown, mirroring the bch signal-contract flow. |

## 3. Approach

**One DDR4-led book set, LPDDR4 as per-chapter deltas** — scoria's own precedent
(one book, both memtypes, memtype enum), with the predecessor swapped: scoria
inherited from pumice; andesite inherits from scoria.

The owner chose **"shared core first" as spec-first**: `mem_ctrl_pkg` (two-bit
memtype, shared timing structs, the scoria/pumice migration plan with conditions)
is the architectural foundation. Its **design lives at family level**
(`mem-ctrl-ip/docs/`), not in any controller's book — a design that migrates two
shipping controllers is family property, and the controller that does not exist
yet must not own it. The refactor itself is **deferred** to andesite RTL bring-up —
no shipping controller is touched in this tranche. `andesite_pkg` exists from day
one; the family doc records the three near-identical packages as deliberate and
time-boxed, exactly as scoria recorded its own package duplication.

Rejected alternatives: family-split books (more writing, breaks precedent);
refactor-now (touches two measured controllers before the new one exists).

## 4. Book set and file layout

```
projects/components/mem-ctrl-ip/
├── README.md                        # exists — gains a pointer to docs/
└── docs/                            # NEW: family property; no single controller owns it
    ├── INDEX.md                     # what's here; the ownership rule
    ├── 01_mem_ctrl_pkg.md           # shared-core design + scoria/pumice migration plan
    ├── 02_family_doctrine.md        # config-not-param; request/grant never-preempt;
    │                                # AXI4 host-side shape; marking semantics; evidentiary rule
    ├── 03_dfi_boundary_lineage.md   # 2.1 → 3.1 → 4.0 delta tables (per-controller ch04 stays authoritative)
    └── 04_jedec_generation_deltas.md# DDR2→3→4 / LPDDR2→3→4 reuse argument; links the Simplified study books

projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/
├── andesite_has/                    # mirrors scoria_has chapter shape
│   ├── ch00_front_matter/00_document_info.md
│   ├── ch01_introduction/{01_purpose,02_conventions,03_definitions}.md
│   ├── ch02_overview/{01_scope,02_block_diagram,03_module_hierarchy,04_design_point}.md
│   ├── ch03_architecture/           # the deltas heart (section 5)
│   ├── ch04_interfaces/{01_dfi_v40,02_axi4_apb}.md
│   ├── ch05_parameters/01_package_and_params.md   # references mem-ctrl-ip/docs/01_mem_ctrl_pkg.md
│   ├── ch06_integration/01_verification_open.md
│   ├── assets/mermaid/01_block_diagram.mmd  # color-marked vs scoria; fence renders to PNG (spec-doc-standards)
│   └── andesite_has_index.md
├── andesite_mas/                    # mirrors bch_mas chapter shape
│   ├── ch00_front_matter/ ch01_overview/
│   ├── ch02_blocks/<changed-or-new block>.md
│   ├── ch03_interfaces/ ch04_contracts/
│   └── andesite_mas_index.md
├── kmaps/
│   ├── gen_andesite_kmaps.py        # built on bin/kmaps, mirrors gen_bch_signal_contracts_kmaps.py
│   ├── andesite_cmd_kmaps.xlsx      # generated contract workbook
│   └── generated/*.md               # markdown renderings cited by the MAS ch04 and HAS ch03
└── (existing) simplified_lpddr4/ study book — referenced, not rewritten
```

House style throughout: the documentation header block, index + styles files,
graphviz assets regenerated via `regenerate_all_graphviz.sh`, evidence-cited
claims, dated Status notes, and the evidentiary rule scoria's HAS carries
(every claim inherited, cited, or recorded as an open question).

## 5. HAS chapter plan

**Ch1 introduction** — purpose; conventions: the marking semantics now run
relative to **scoria** (INHERITED / MODIFIED / NEW), plus the mem_ctrl_pkg family
note pointing at the family docs; definitions new to this tier: bank group,
tCCD_L/tCCD_S, FGR, gear-down, CA parity, DBI, MPC.

**Ch2 overview** — scope (DDR4-led; LPDDR4 deltas per chapter; sim-only, no board —
7-series targets do not carry DDR4); the color-marked block diagram against scoria;
the module-hierarchy marking table; the design point (section 2): fixed geometry,
runtime timing CSRs, DFI 4.0 BFM boundary.

**Ch3 architecture deltas** (the heart — preliminary markings, to be confirmed
block-by-block during authoring):

| # | Delta | Blocks | Marking |
|---|---|---|---|
| 1 | Bank groups: tCCD_L/S, tRRD_L/S | `addr_mapper`, scheduler/`cmd_arbiter`, `global_timers` | MODIFIED |
| 2 | Command encoding: ACT_n 5th pin, BG0/1; LPDDR4 6-bit CA bus | `dfi_cmd_formatter` | MODIFIED / NEW (LPDDR4 path) |
| 3 | Init: reset procedure, MR0–MR6, gear-down + parity enable | `init_sequencer`, `mode_register` | MODIFIED |
| 4 | Refresh: FGR 1x/2x/4x (MR3); LPDDR4 controller-directed per-bank | `refresh_ctrl` | MODIFIED (inherits scoria's landed TASK-001 modes A/B/C as the policy base) |
| 5 | ZQ: DDR4 keeps ZQCS/ZQCL; LPDDR4 calibration via MPC | `zq_ctrl` | INHERITED / NEW (LPDDR4 path) |
| 6 | Training: read leveling (MPR), LPDDR4 CA/WDQ training | new training blocks + `wrlvl_ifc` | NEW / MODIFIED (search in firmware, per D2 precedent) |
| 7 | Datapath: DBI via DFI 4.0 `dfi_dbi_*`; write CRC excluded v0.1 with named unblock condition | dfi datapath blocks | MODIFIED |
| 8 | CA parity + `alert_n`; gear-down handshake | formatter/sequencer + new parity/alert handling | MODIFIED / NEW |
| 9 | Dynamic ODT: RTT_NOM/WR/PARK + ODT latencies (scoria holds ODT static — insufficient) | new `odt_ctrl` | NEW |
| 10 | LPDDR4 per-chapter deltas: no bank groups, 8 banks/channel, 2-channel x16, MPC bus, DSM power states (deferred, named condition) | as above | as above |

Ch3 closes with the **full reuse table** — every scoria module with marking and
cause (the andesite Table 3.1), the dormant-block disposition
(`powerdown_ctrl`/`dfi_signal_pack` carried dormant again with the condition named),
and the deferred list (write CRC, LPDDR4 DVFS/DSM, self-refresh scheduling).

**Ch4 interfaces** — `01_dfi_v40.md`: the 3.1→4.0 delta table (ACT_n, alert_n,
gear-down handshake, parity, DBI wires, frequency ratios) and what transfers from
scoria's ch04; `02_axi4_apb.md`: host side unchanged in shape, name-based regmap
rule carried over. Both cite the family DFI lineage doc rather than restating
earlier-version material.

**Ch5 parameters** — **references** `mem-ctrl-ip/docs/01_mem_ctrl_pkg.md` for the
shared-core design, two-bit memtype, shared timing struct inventory, the
scoria/pumice migration plan and its recorded deferral; owns only what is
andesite's own: `andesite_pkg` initial content, geometry fixed per the design
point, timings runtime CSRs, the build-time vs runtime table.

**Ch6 integration** — verification strategy: sim-only, DFI 4.0 BFM (acquisition and
study = named task); the open-questions table (write CRC, gear-down coverage scope,
CA-parity scope, LPDDR4 DVFS/DSM, BFM provenance); what would make the HAS a 1.0;
vault filing: **andesite TASK-002 (HAS + family docs seed), TASK-003 (MAS),
TASK-004 (kmaps), TASK-005 (DFI 4.0 BFM study)** under
`vault/Tasks/andesite-ddr4-lpddr4/task/` (the area scaffolded 2026-09-28;
TASK-001 was already taken by the advanced-modes survey, so IDs shift by one —
recorded in the SDD ledger ruling of 2026-10-04), with INDEX updates per the
tasks convention.

## 6. MAS plan

bch_mas shape. ch01 overview: block inventory with per-block "what changes vs
scoria." ch02 per-block chapters **only for changed/new blocks**: cmd_formatter
(ACT_n/BG encoding + LPDDR4 CA tables), init_sequencer (reset, MR order, gear-down
entry), mode_register (MR0–6 field maps), addr_mapper (BG/channel decode),
scheduler+arbiter (L/S scheduling policy), refresh_ctrl (FGR on top of the
inherited elastic/TCR/placement modes), zq_ctrl (MPC path), odt_ctrl (new),
training blocks (read leveling, CA training), dfi layer (DBI). ch03 interfaces:
DFI 4.0 pin-level. ch04 contracts: changed-block signal contracts in bch style.
Inherited-unchanged blocks are **referenced** to scoria's books, not rewritten —
the MAS states where and why.

## 7. Kmap book

`docs/kmaps/gen_andesite_kmaps.py` on `bin/kmaps` (minimize/writer/styles,
mirroring `gen_bch_signal_contracts_kmaps.py`). Tables: DDR4 command truth table
(ACT_n×RAS×CAS×WE + BG), LPDDR4 CA-bus command table, address/bank-group decode
maps, MR0–MR6 per-field programming maps for both memtypes, ODT truth table
(RTT_NOM/WR/PARK × DRAM state), FGR refresh-mode select map. Outputs: the xlsx
contract workbook plus markdown renderings cited from MAS ch04 and HAS ch03.

## 8. Sequencing and gates

1. **Family docs seed** — `mem-ctrl-ip/docs/`: INDEX, `01_mem_ctrl_pkg.md`,
   `02_family_doctrine.md` (03/04 may stub with pointers in v0.1) → commit.
2. **HAS v0.1** authored from the delta analysis ("no RTL exists" posture, as
   scoria v0.1), ch5 referencing the family doc → owner review → commit.
3. **MAS** → owner review → commit.
4. **Kmaps** (generator + generated artifacts) → owner review → commit.
5. Each book: documentation header, index, mermaid diagram assets per
   `vault/handbook/authoring/spec-doc-standards.md` (no graphviz, no ASCII art);
   vault INDEX/ID updates land with the book that triggers them;
   `bin/check_task_ids.py` green before every commit.
6. Handoff: superpowers:writing-plans produces the RTL-bootstrap implementation
   plan from this spec.

## 9. Out of scope

- Any RTL, DV, or formal changes; the mem_ctrl_pkg refactor (specified, not
  performed); scoria/pumice touched not at all.
- Write CRC, LPDDR4 DVFS/DSM, self-refresh scheduling (named deferred items).
- The PRD rewrite ("authored once HAS is locked") — follow-on, after HAS review.

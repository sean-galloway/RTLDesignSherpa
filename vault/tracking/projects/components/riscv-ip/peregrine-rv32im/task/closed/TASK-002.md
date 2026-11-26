# TASK-002: peregrine HAS and MAS books (PRD §7 deliverable 2)

**Priority:** P2
**Status:** CLOSED 2026-11-25
**Owner:** TBD (follows riscv-ip/peregrine-rv32im TASK-001)

## What

`peregrine_has` and `peregrine_mas` under
`projects/components/riscv-ip/peregrine-rv32im/docs/`, built like merlin's
(`merlin_has`, `merlin_mas`) and through the house PDF pipeline. Per the
[PRD](../../../../../../../../projects/components/riscv-ip/peregrine-rv32im/PRD.md), the core of both books is the predictor, trap and M-unit chapters.
They describe the RTL as built (TASK-001 stages 1-7), not the plan.

Rules: unreleased books stay at rev 0.1 (no revision rows, one PDF pair);
block diagrams follow the house style; no emoji.

## Done when

- Both books build to DOCX/PDF with the house style, and every chapter
  matches the RTL (ports, parameters, the stage-4 D$/I$ contract, the
  stage-7 hold and early-response rules, the P14 clock).
- The riscv-ip README row points at them.

## Built (2026-11-25, committed 3aa81b0e0)

Both books under `projects/components/riscv-ip/peregrine-rv32im/docs/`, at
rev 0.1, one DOCX/PDF pair each.

- **HAS** (`peregrine_has/`, 121 pages), seven chapters:
  - introduction;
  - system overview, with Figure 2.1, `peregrine_top` in context;
  - architecture: ISA scope, machine state and traps, address map;
  - interfaces: `peregrine_core` and `peregrine_top` port specifications, the memory contract, trap and interrupt behaviour;
  - performance: cycle costs, measured CPI, the predictor A/B, the P14 sweep and the 18.5 ns target;
  - integration;
  - verification summary, including the two stage-5 scope decisions.
- **MAS** (`peregrine_mas/`, 197 pages), six chapters:
  - overview, with Figure 1.1, the pipeline;
  - twelve block chapters;
  - the package records;
  - eight behaviour chapters (pipeline cycle, hazards, branch prediction with Figure 4.1, traps with Figure 4.2, the M unit, the D side with Figure 4.3, fence.i, RVFI);
  - verification hooks, including `RSP_SCRAMBLE`;
  - configuration.
- **Generated tables.** Every port and parameter table in both books is
  generated from the RTL headers by `peregrine_mas/gen_port_tables.py`,
  between `GEN` markers. A port with no source comment and no description
  entry is an error, as is a description naming a port that does not exist.
  The build scripts run it with `--check` and stop on a stale table.
- **Layout deviations from precedent.**
  - merlin's books are skeletons with no build script and no PDF, so the
    build mirrors kestrel's (`generate_*_pdf.sh`, the styles YAML, the
    graphviz assets).
  - The scripts and the PDF pairs sit inside each book directory, not in
    `docs/`, to keep the change inside the two book directories.
  - The List of Waveforms is off in both books: neither has timing diagrams
    yet. The three waveforms PRD §5 asks for belong to the book (TASK-003).

Build:
```
source env_python
python3 projects/components/riscv-ip/peregrine-rv32im/docs/peregrine_mas/gen_port_tables.py
projects/components/riscv-ip/peregrine-rv32im/docs/peregrine_has/assets/graphviz/regenerate_all_graphviz.sh
projects/components/riscv-ip/peregrine-rv32im/docs/peregrine_mas/assets/graphviz/regenerate_all_graphviz.sh
projects/components/riscv-ip/peregrine-rv32im/docs/peregrine_has/generate_has_pdf.sh
projects/components/riscv-ip/peregrine-rv32im/docs/peregrine_mas/generate_mas_pdf.sh
```

Checks:
- `bin/check_doc_examples.py` reports 0 fabricated examples. It walks the
  docs trees on disk, so it covered the untracked pages: the cacheless
  instantiation example and every port table.
- `bin/review/check_emoji.py` reports 0 emoji in the 53 new files.
- A local relative-link check found 0 broken links in the new pages and
  the README. `bin/check_broken_links.py --ratchet` passes, but it reads
  tracked files only.

## RTL versus PRD mismatches found (documented as built, nothing fixed)

1. **CSR read stage.** PRD §4.1 puts the CSR read in ID. The RTL reads the
   CSR file in EX and writes it in MEM; ID only holds a CSR instruction
   behind an older one (`stall_csr`).
2. **Access faults.** PRD §3 and §4.3 say load and store access faults
   (AXI SLVERR/DECERR) are added. None is built:
   - `peregrine_pkg` has no access-fault cause;
   - `rresp` and `bresp` are ignored by the I$ and the uncached port;
   - `peregrine_uc_axi`'s header attributes this to PRD P6.
3. **MonBus.** PRD §4.6 plans core MonBus events (mispredict, trap, M-busy)
   and `axi4_monlite` observation. Not built: the core has no MonBus port
   and amber is instantiated with `USE_MONITOR=0`.
4. **RVFI fields.** PRD §4.7 adds `rvfi_intr` and the `rvfi_csr_*` fields
   for `mepc`, `mcause` and `mtvec`. The RTL has neither; it reports
   `rvfi_trap_cause` and `rvfi_bp_*` instead. Stage 5 ran riscv-formal
   without CSR checks for this reason.
5. **riscv-formal scope.** PRD §2 says there is no full riscv-formal through
   the predictor and the traps. Stage 5 ran it with the predictor live and
   traps in. The PRD understates what was done; this is not an RTL defect.
6. **Stale RTL header comments** (not the code):
   - `peregrine_top` still says "the PRD says 0x1000_0000 and up", although
     P7 was amended on 2026-11-24.
   - `peregrine_uc_axi` says it serves the cacheable window "until amber is
     wired in", which is stale since stage 4 part 2.
   - `peregrine_hazard` says "RV32I core" and credits a port removal to
     "peregrine-rv32im TASK-002", which is this documentation task. The
     removal predates it.

**Resolved 2026-11-25** (owner: "amend the prd for now; add a task for
the future for error handling"): the PRD is amended to the RTL for every
mismatch above: access faults not built (§3, §4.3), MonBus not built
(§1, §4.6), RVFI fields as built (§4.7), CSR read in EX (§4.1, §4.3),
the §2 riscv-formal note. Error handling is TASK-005 (open). The three
stale RTL header comments (`peregrine_top`, `peregrine_uc_axi`,
`peregrine_hazard`) are corrected, comments only.

## Closed (2026-11-25)

Both books are built at v0.1 (3aa81b0e0) and the README row links them; the
PRD mismatches they found are resolved (6e04a5976).

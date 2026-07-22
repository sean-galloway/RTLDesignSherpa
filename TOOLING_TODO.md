# Tooling / process TODOs

Durable tracker (the session task MCP has dropped tasks before; files survive).
Owner-requested 2026-07-22.

## 1. Promote the K-map / signal-contracts generator to bin/

The generator currently exists per-project:
  projects/components/memory-controllers/pumice-ddr2-lpddr2/docs/gen_signal_contracts_kmaps.py
  projects/components/dmas/stream/docs/gen_signal_contracts_kmaps.py  (in flight)

That is copy-paste divergence waiting to happen (same failure mode as the
generate_*_pdf.sh x8 copies -- see the scripts-outside-bin audit). Extract the
common machinery (KmapWriter, gray-order grids, styling, the
mirror-the-exact-RTL-expression pattern) into ONE bin/ tool; per-project files
keep only their signal tables and mirrored expressions.

Methodology doc: bin/SIGNAL_CONTRACTS_KMAPS.md (written, see there).

## 2. Cohesive SKILLS strategy for this repo

Problem: methodology knowledge lives scattered across CLAUDE.md files, bin/*.md
how-tos, plan files, and (fragile) assistant memory. Agents re-derive or
re-roll instead of reusing. Wanted: repo-resident skills that every
agent/session discovers automatically.

Proposed location (to be validated): `.claude/skills/<name>/SKILL.md` in the
repo root -- Claude Code auto-discovers project-scoped skills there, and
subagents inherit the listing. That answers "where do we put them so all
agents know to look."

Candidate skills (owner's list + obvious additions):
  - doc-methods        The Sherpa doc pipeline: md_to_docx --style, caption
                       encoding for LoF/LoT/LoW, book indexes, generate_rtl_pdfs,
                       HAS/MAS vs operator guides. (Condense bin/DOC_GENERATION.md.)
  - kmaps              Signal-contract + K-map methodology (bin/SIGNAL_CONTRACTS_KMAPS.md).
  - uart-harness-sim   The cocotb-UART sim methodology: same host program in sim
                       and on the board, cocotb.function transport, PeakRDL
                       regmap-by-name, injectable driver.
  - uart-harness-fpga  The FPGA half: bitstream flows, JTAG serial selection on
                       the shared chain, the Adept/ttyUSB and no-power-cycle
                       gotchas, board-side smoke pattern.
  - hard-design        HARD design guidelines: reset macros, CDC rules, FIFO
                       depth/power-of-2, valid/ready contracts, no-FSM streaming
                       pattern, array syntax, SRAM-no-reset, signal naming audit.
  - rds-dv-bfms        USE THE FRAMEWORK BFMs -- never hand-roll drivers/monitors.
                       Map of what exists (GAXI master/slave, AXI4/AXIL/APB/AXIS
                       factories, MonbusSlave + parse(), MonbusGroupHarness,
                       register_map by name), the decision tree for BFM vs
                       embedded helper, and the known traps (Monitor.__len__
                       truthiness, signal_map required keys, ready-profile
                       delays vs drain windows, seeds must be pinned).
  - filelists          -f closure rule + bin/filelist_registry.py usage
                       (--check/--audit/--unrolled), generated-area regen rule.
  - review-rounds      The Kimi review process (KIMI_REVIEW_HOWTO.md): rebuild
                       all/send subset, serial, never overwrite a round,
                       max_tokens ladder, humanizer final round.

Open decisions:
  - Skill granularity (one hard-design skill vs several small ones).
  - How skills reference the longer bin/*.md docs (skill = entry point +
    pointers, not a duplicate of the content -- duplication rots).
  - DECIDED (owner 2026-07-22): GLOBAL_REQUIREMENTS.md STAYS authoritative;
    skills point at it and it wins on conflict. Skills are entry points, not
    duplicates.
  - Verification: a CI-ish check that skill pointers (paths, script names)
    still resolve, so skills cannot silently rot the way docs did.

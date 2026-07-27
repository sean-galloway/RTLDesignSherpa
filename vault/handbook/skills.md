---
title: Skills ↔ handbook map
summary: Every repo-resident .claude/skills signpost and the handbook note (or index) it points at. Skills are signposts only; the method lives in the note.
---

# Skills ↔ handbook map

Skills under `.claude/skills/` are **signposts** (auto-discovered by Claude
Code): each names its canonical handbook note and stops. Method detail lives in
the note, never in the skill file (see the house rule in [[INDEX]] and the
root `CLAUDE.md`). This note is the reverse index — from each skill back to the
vault note it signposts — so the linkage is navigable from inside the vault.

When you add a skill, add a row here and point it at a real note. When you add a
durable lesson, it goes in the **note**, and the skill keeps pointing at it.

| Skill | Signposts (handbook note) | What it covers |
|-------|---------------------------|----------------|
| [coverage](../../.claude/skills/coverage/SKILL.md) | [[coverage]] | Verilator line/toggle coverage, functional coverage, the monbus packet-type matrix |
| [doc-methods](../../.claude/skills/doc-methods/SKILL.md) | [[doc-pipeline]] | The Sherpa doc pipeline — `md_to_docx --style`, caption-encoded lists, RTL PDF books |
| [doc-placement](../../.claude/skills/doc-placement/SKILL.md) | [[doc-placement]] | What kind of doc lives where; a beside-code README is a link, not a copy |
| [filelists](../../.claude/skills/filelists/SKILL.md) | [[filelists]] | Every module has a `.f`, registered in `bin/filelists.toml`; consumers `-f` include |
| [formal](../../.claude/skills/formal/SKILL.md) | [[formal]] | SymbiYosys via sv2v, in-RTL `ifdef FORMAL` properties, mutation-checking |
| [fsm-discipline](../../.claude/skills/fsm-discipline/SKILL.md) | [[streaming-no-fsm]], [[minimal-fsm]] | No FSM on the data path at all; where one IS right, keep it minimal |
| [hard-design](../../.claude/skills/hard-design/SKILL.md) | [[design/INDEX\|design area]] | Reset macros, CDC, valid/ready contracts, streaming no-FSM, SRAM rules, sizing |
| [kmaps](../../.claude/skills/kmaps/SKILL.md) | [[signal-contracts-and-kmaps]] | Signal-contract sheets + K-map workbooks for engines/schedulers/arbiters |
| [module-docs](../../.claude/skills/module-docs/SKILL.md) | [[module-doc-template]] | Per-module `docs/markdown` page style + the SV header that mirrors it |
| [signal-prefixes](../../.claude/skills/signal-prefixes/SKILL.md) | [[signal-prefixes]] | `r_` = flopped, `w_` = combinational; the prefix is a latency claim |
| [rds-dv-axes](../../.claude/skills/rds-dv-axes/SKILL.md) | [[rds-dv-axes]] | The three orthogonal TB choices: BFM, sequence, randomization |
| [rds-dv-bfms](../../.claude/skills/rds-dv-bfms/SKILL.md) | [[bfm-usage]] | Use the RDS-DV framework BFMs; never hand-roll drivers/monitors/decoders |
| [rds-dv-randomization](../../.claude/skills/rds-dv-randomization/SKILL.md) | [[randomization]] | The named FlexConfigGen delay profiles; randomized traffic ≠ fairness proof |
| [regressions](../../.claude/skills/regressions/SKILL.md) | [[running-regressions]] | `make clean-all && make run-all-{gate,func,full}-parallel`, never a bare pytest |
| [review-rounds](../../.claude/skills/review-rounds/SKILL.md) | [[kimi-review-rounds]] | External doc-review rounds: bundles, dispatch, triage, humanization pass |
| [tasks](../../.claude/skills/tasks/SKILL.md) | [/vault/Tasks/INDEX.md](../Tasks/INDEX.md) | Where TODOs live — the `/vault/Tasks/<area>/` lifecycle pages |
| [uart-harness](../../.claude/skills/uart-harness/SKILL.md) | [[uart-harness]] | One host program running identically against cocotb sim and the FPGA |

The `tasks` skill points at the Tasks tree (work items), not a handbook note —
the handbook is method, `/vault/Tasks/` is live work. Keep them distinct
(see [[doc-placement]]).

# TASK-008: ch01_overview/02_port_list.md documents 86 of 300 ports, mis-structured

**Priority:** P1. This is the book's entry page for the top-level interface.
**Status:** open 2026-09-26. Measured, not estimated.

**The numbers.** `rapids_core_beats` has **300 ports**: 121 prefixed `src_`, 119
prefixed `snk_`, 60 neither. The page carries 86 rows and **82 of them name no
port of that module**.

**The structure is wrong, not the spelling.** The page presents ONE
`apb_valid`, ONE `cfg_sched_enable` and ONE "Descriptor AXI Master" section. The
module is two independent halves, so each of those is really a pair --
`src_apb_valid` / `snk_apb_valid` -- and the AXI side is three masters per half:
`snk_m_axi_desc_*`, `snk_m_axi_ctrlrd_*`, `snk_m_axi_ctrlwr_*` and the `src_`
mirrors. Renaming rows cannot fix that; the sections have to be split per half.

**Scale:** ~250-300 rows to author. This is a new chapter, not a correction, which
is why it was raised as a decision rather than folded into the table pass
(`b8c55993e`).

**Precedent to copy:** `ch03_macro_blocks/09_rapids_core_beats.md` already solves
the same 300-port problem with per-half sections (`### Descriptor AXI Master
Interfaces`, `### Sink AXI Write Master Interface`, `### Source Egress -- AXIS
Master`). Follow its shape rather than inventing one.

**Verify with:** compare every table row against the declared module's port list;
the pass criterion is 0 not-a-port AND 0 real ports undocumented.

**Related:** [[TASK-007]]

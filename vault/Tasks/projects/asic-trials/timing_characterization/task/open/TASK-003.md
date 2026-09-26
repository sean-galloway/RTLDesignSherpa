# TASK-003: Additional FUBs

> Migrated 2026-09-25 from
> `projects/asic-trials/timing_characterization/TASKS.md` as **TASK-003**
> (tooling TOOL-001), ID unchanged. That checklist recorded "9 task blocks";
> the file actually held FOUR. Classified against the tree, not the Status line.


**Confirmed still open 2026-09-25.** `rtl/fub/` holds nine FUBs
(carry_chain, clock_divider_chain, gray_counter_chain, inverter_chain,
multiplier_tree, mux_tree, nand_chain, queue_depth, xor_tree). None of the four
candidates -- barrel shifter, priority encoder, comparator chain, DSP chain --
exists.

**Status:** Planned
**Priority:** P3 (Low)
**Effort:** 1-2 days per FUB

**Description:**
Add new characterization FUBs to broaden logic family coverage.

**Candidates:**
- [ ] Barrel shifter -- Funnel shift timing
- [ ] Priority encoder -- Wide OR-tree characterization
- [ ] Comparator chain -- Magnitude comparator depth
- [ ] DSP chain -- Cascaded DSP48 slice timing (Xilinx-specific)

**Files:**
- `rtl/fub/{new_fub}.sv` (to be created per FUB)
- `dv/tests/fub/test_{new_fub}.py` (to be created per FUB)
- char_top.sv updates (new EN_* parameters)

---

# TASK-002: comparator registers are write-only
> Migrated 2026-09-25 from `projects/components/retro_legacy_blocks/TASKS.md` as **TASK-003** (tooling TOOL-001). That file numbered its own items TASK-001..006, which collide with RLB-001..017 on the frozen legacy page; per-lane IDs replace them. Body preserved as written except the Status line.

**Priority:** P3
**Status:** CLOSED 2026-09-27. Implemented, regenerated and verified; see
"Outcome" below. The earlier note ("zero hits for `comparator_readback`") was a
correct reading of an incorrect premise -- see "What this item got wrong".
**Owner:** TBD

**Description:**
Add read access to timer comparator registers. Currently comparators are write-only, preventing software from reading current comparator values.

**Current Limitation:**
- TIMER_COMPARATOR_LO/HI registers are write-only
- Software cannot read back programmed comparator values
- Debugging and diagnostics more difficult

**Enhancement Goals:**
1. Make comparator registers read/write instead of write-only
2. Return current comparator value on read
3. Support both one-shot and periodic modes
4. Maintain existing write behavior

**Design Approach:**
```systemverilog
// In hpet_regs.rdl, update comparator field properties
field comparator_lo {
    sw = rw;  // Change from sw=w to sw=rw
    hw = r;   // Hardware can read
};
```

**Impact:**
- Improved software debugging capabilities
- Better diagnostic features
- Enhanced HPET monitoring

**Verification Steps:**
1. Update hpet_regs.rdl SystemRDL specification
2. Regenerate registers: `peakrdl regblock hpet_regs.rdl --cpuif apb4`
3. Add readback test to hpet_tests_basic.py
4. Verify: Write comparator, read back, values match
5. Test: Both one-shot and periodic modes

**Related Files:**
- Modify: `rdl/hpet/hpet_regs.rdl`
- Regenerate: `rtl/hpet/hpet_regs.sv`, `rtl/hpet/hpet_regs_pkg.sv`
- Update: `dv/tbclasses/hpet/hpet_tests_basic.py`

**Dependencies:** None

**Completion Criteria:**
- [x] Comparator registers support read access -- they always did (`sw = rw`);
      what changed is WHAT a read returns
- [x] Read returns current comparator value -- `readback == internal
      r_timer_comparator`, asserted in both CDC configurations
- [x] Tests passing -- 18/18 cells at `REG_LEVEL=full` after `clean-all`
- [x] Documentation updated -- 5 doc pages, 2 RTL headers, 1 wavedrom JSON

**Notes:**
- Nice to have, not critical for operation
- Deferred until core functionality stable

---

## What this item got wrong

**The comparators were never write-only.** `sw = rw` was already set on both
halves at HEAD, and a read already returned register storage. The real defect
was that the value returned was STALE: in periodic mode `hpet_core` advances
its internal `r_timer_comparator` on every fire and nothing wrote that back
into the register, so after N fires software still read the original period P
while hardware was comparing against (N+1)*P.

**The proposed "Design Approach" was the state that caused the defect.** It
asked for `hw = r`, which is exactly what the RDL already had -- and `hw = r`
means hardware only READS the field, so hardware can never publish its live
value into it. Following the tracker literally would have changed nothing.

The owner's decision (2026-09-27) resolved the ambiguity as **read back live**:
a read returns the comparator the core is actually comparing against.

## Outcome

Both comparator fields are now `sw = rw; hw = rw; precedence = sw; swmod;` --
the same idiom `HPET_COUNTER_LO/HI` already use for live counter readback.
Hardware reads the field to carry a software write down to the core and drives
the live value in continuously so reads return it; `precedence = sw` lets a
software write win in its own cycle. The field still holds the committed value
during the aligned `timer_comp_write_*` strobe cycle, which is where
`hpet_config_regs` samples `timer_comp_wdata`, so the existing strobe write
path is untouched.

An earlier revision of this fix used `hw = rw` plus a hand-built `we` gate in
the wrapper (`we = ~(swmod | strobe)`). It worked, but it was redundant logic
diverging from an idiom already used three times in the same RDL
(`counter_lo`, `counter_hi`, `interrupt status`). Verilator caught the first
attempt outright: `hw = w` deleted `hwif_out...value`, which is the ONLY source
of `timer_comp_wdata`, severing the software-to-core write path with
`%Error: Member 'value' not found in structure`.

`hpet_core` gained `timer_comp_rdata [NUM_TIMERS]`, driven from
`r_timer_comparator` exactly as `counter_rdata` is driven from
`r_main_counter`. No synchroniser is needed in either configuration:
`hpet_config_regs` and `hpet_core` are both clocked
`CDC_ENABLE[0] ? hpet_clk : pclk`, so they share a domain and the crossing
lives upstream in `apb4_slave_cdc`.

Regenerated with `bin/peakrdl_generate.py` (CLAUDE.md Rule #0). Note that this
item's own "Verification Steps" said `peakrdl regblock hpet_regs.rdl` -- raw
peakrdl, which skips the docs and the regmap and is forbidden by Rule #0.

**Measured verification:**
- `make clean-all && make run-apb4_hpet-full-parallel`: **18/18 passed** in
  42.9s (6 RTL configs x gate/func/full).
- The new medium test `test_comparator_reads_back_live_value` executed in all
  12 func/full cells (gate does not run the medium suite) and logged
  `readback=900 internal r_timer_comparator=900 (period=300)` -- equal, and
  advanced 3x past the programmed period -- in both CDC configurations.
- Medium suite grew 17 -> 18 tests; every cell reports 18/18.
- Verilator warning profile is byte-identical to HEAD's (34 warnings, six
  classes). The 11 `MULTIDRIVEN` on `field_combo` are pre-existing PeakRDL
  output, proven by linting HEAD's regblock standalone: same 13/19 counts.
- `bin/check_rdl_regen.py` rc=0 (hpet appears twice in its manifest).

**Docs synced in the same pass:** `ch01_overview/01_overview.md` (moved out of
"Future Enhancements (Not Planned)" into "Completed Features"),
`ch01_overview/03_clocks_and_reset.md`, `ch02_blocks/03_hpet_regs.md` (its RDL
excerpt), `ch05_registers/01_register_map.md`,
`assets/wavedrom/hpet_registers.json`, plus the `apb4_hpet.sv` and
`hpet_core.sv` header comments.

**Related:** RLB/hpet TASK-004 (64-bit counter reads are two reads BY DESIGN)
was dropped on the same reasoning that the register interface is 32-bit and the
comparator is 64-bit: a 64-bit comparator read is likewise two transactions.

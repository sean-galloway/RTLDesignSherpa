# TASK-003: legacy PC/AT replacement routing (CSR exists, routing does not)
> Migrated 2026-09-25 from `projects/components/retro_legacy_blocks/TASKS.md` as **TASK-004** (tooling TOOL-001). That file numbered its own items TASK-001..006, which collide with RLB-001..017 on the frozen legacy page; per-lane IDs replace them. Body preserved as written except the Status line.

**Priority:** P3
**Status:** open, and **its original premise was wrong**. The source said
"Deferred -- implement legacy replacement mode" as if nothing existed. Measured
2026-09-25: the CSR half is already built and wired --
`hpet_regs__HPET_CONFIG__legacy_replacement__out_t` in `hpet_regs_pkg.sv`,
`w_legacy_replacement` declared at `apb4_hpet.sv:232` and connected at `:373`,
with storage in `hpet_regs.sv`. What is missing is the IRQ routing the field is
supposed to gate (timer 0 -> IRQ0, timer 1 -> IRQ8). Scope it as wiring, not
greenfield.
**Owner:** TBD

**Description:**
Implement legacy PC/AT timer replacement mode for compatibility with legacy operating systems and software.

**Features to Add:**
1. **Legacy IRQ Routing:**
   - Timer 0 → IRQ0 (PIT channel 0 replacement)
   - Timer 1 → IRQ8 (RTC replacement)

2. **Legacy Mapping:**
   - HPET_CONFIG legacy_mapping bit controls routing
   - Compatible with PC/AT timer expectations

3. **Operating Mode:**
   - Timer 0: 1ms periodic tick (IRQ0 replacement)
   - Timer 1: RTC interrupt generation (IRQ8 replacement)

**Design Approach:**
```systemverilog
// In hpet_core.sv, add legacy mode logic
logic legacy_irq0;  // PIT channel 0 replacement
logic legacy_irq8;  // RTC replacement

assign legacy_irq0 = cfg_legacy_mapping ? timer_irq[0] : 1'b0;
assign legacy_irq8 = cfg_legacy_mapping ? timer_irq[1] : 1'b0;
```

**Impact:**
- Better compatibility with legacy software
- Support for PC/AT timer emulation
- Enhanced OS compatibility

**Verification Steps:**
1. Add legacy mode logic to hpet_core.sv
2. Update hpet_regs.rdl with legacy_mapping bit
3. Create test: test_legacy_replacement_mode
4. Verify: IRQ0 and IRQ8 routing
5. Test: 1ms tick generation

**Related Files:**
- Modify: `rtl/hpet/hpet_core.sv`
- Update: `rdl/hpet/hpet_regs.rdl`
- Create: `dv/tbclasses/hpet/hpet_tests_legacy.py`

**Dependencies:** None

**Completion Criteria:**
- [ ] Legacy IRQ routing implemented
- [ ] Legacy mapping bit functional
- [ ] Tests passing
- [ ] Documentation updated

**Notes:**
- Complex feature, not needed for basic operation
- Deferred until production deployment requirements clear

---

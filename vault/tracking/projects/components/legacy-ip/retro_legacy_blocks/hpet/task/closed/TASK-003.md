# TASK-003: legacy PC/AT replacement routing (CSR exists, routing does not)
> Migrated 2026-09-25 from `projects/components/retro_legacy_blocks/TASKS.md` as **TASK-004** (tooling TOOL-001). That file numbered its own items TASK-001..006, which collide with RLB-001..017 on the frozen legacy page; per-lane IDs replace them. Body preserved as written except the Status line.

**Priority:** P3
**Status:** CLOSED 2026-09-28 -- implemented and verified (18/18 green).
The original premise was also wrong. The source said
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
- [x] Legacy IRQ routing implemented
- [x] Legacy mapping bit functional
- [x] Tests passing
- [x] Documentation updated

**Notes:**
- Complex feature, not needed for basic operation
- Deferred until production deployment requirements clear

---

## Outcome (2026-09-28)

**Implemented.** `hpet_core` gained `legacy_replacement` in and
`legacy_irq0`/`legacy_irq8` out; `apb4_hpet` exposes both and finally connects
`w_legacy_replacement`, which until now was declared and driven but consumed by
nothing; `rlb_top` brings both out as `hpet_legacy_irq0/8`.

**The spec REPLACES, it does not duplicate.** While `legacy_replacement` is set,
timers 0 and 1 are masked off `timer_irq` and leave only on the legacy outputs.
The task's own sketch (`legacy_irq0 = cfg ? timer_irq[0] : 0`) would have left
both paths live, which is not what the spec describes and would double-deliver
into whatever rlb_top eventually merges. Timers 2+ are untouched.

**`leg_rt_cap` 0 -> 1**, and that bit is load-bearing: drivers gate on it
(FreeBSD `if ((caps & HPET_CAP_LEG_RT) == 0) legacy_route = 0`), so leaving it 0
would have made the whole feature invisible. Consequence to remember: it sets
GCAP_ID[15], so every documented HPET_ID example word gained 0x8000
(`0x80862101` -> `0x8086A101`, and the other two likewise).

**`TIMER_INT_ROUTE_CAP` deliberately still reads 0.** General per-timer I/O APIC
route selection is a SEPARATE feature. The spec has the LegacyReplacement Route
OVERRIDE `timer_int_route` for timers 0/1 rather than select through it, so
legacy mode works with that mask empty -- and advertising routes we do not
implement would be a lie a driver acts on. The RDL descriptions that promised
"TASK-003 sets this" were corrected rather than honoured.

**Status is NOT masked.** Only the delivery path moves; `HPET_STATUS` behaves
identically in both modes, so software that polls rather than takes the
interrupt is unaffected.

**NOT done here, on purpose:** consuming the routes requires silencing the real
8254 PIT tick and the RTC periodic interrupt, and merging into the PIC/IOAPIC.
That is the rlb_top IRQ-fabric item. **TRAP recorded for it: timer 0 belongs on
master IRQ0 and I/O APIC pin 2 -- never PIC IRQ2, which is the 8259 cascade
input.** QEMU shipped exactly that bug.

**Verification.** 18/18 cells at REG_LEVEL=full after `clean-all`, RUN_RC=0. A
new `hpet_tests_legacy.py` suite runs in 13 cells (func and full tiers) and
passes 4/4 in every one. Each scenario asserts BOTH directions -- the legacy
output stays low with the mode off, and `timer_irq` stays low with it on --
because a one-sided test would pass against RTL that ignored the mode bit and
simply asserted both. `test_rlb_top` 3/3. Verilator 38 -> 37 warnings (-1:
`w_legacy_replacement` is no longer unused); `check_rdl_regen` rc=0.

**Sim-time budget, the one real snag.** The suite is a fourth suite inside a
single cocotb test. At 1000 comparator ticks it cost 119,360 ns and pushed the
2-timer non-CDC FULL cell -- the tightest in the grid, both multipliers 1.0 --
past its 400 us timeout. `COMPARE_TICKS = 200` cut that to 39,300 ns and the
cell STILL failed, finishing at 400,410 ns: short by 410 ns. The base budget was
raised 400 -> 500 us, measured against Full's real cost (~110,000 ns, taken from
cells where Full completed). Headroom is now 99,590 ns (~20%). Anyone adding a
fifth suite must measure again; three suites fitted 400 us with only ~30 us
spare, which is why the previous addition overran too.

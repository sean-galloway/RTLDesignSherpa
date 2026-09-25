# TASK-004: 64-bit counter read is not atomic
> Migrated 2026-09-25 from `projects/components/retro_legacy_blocks/TASKS.md` as **TASK-005** (tooling TOOL-001). That file numbered its own items TASK-001..006, which collide with RLB-001..017 on the frozen legacy page; per-lane IDs replace them. Body preserved as written except the Status line.

**Priority:** P3
**Status:** open. Confirmed against the RTL 2026-09-25: zero hits for
`atomic_counter_read`, so the LO-then-HI race described below still stands.
**Owner:** TBD

**Description:**
Implement 64-bit atomic counter read to prevent race conditions when reading counter value that's incrementing.

**Current Limitation:**
- Counter read requires two 32-bit reads (LO then HI)
- Counter may increment between reads
- Race condition: Read LO=0xFFFFFFFF, counter increments, Read HI=0x00000001
- Result: 0x00000001FFFFFFFF instead of 0x0000000100000000 or 0x00000000FFFFFFFF

**Enhancement Goals:**
1. Latch counter value on LO register read
2. Return latched HI value when HI register read
3. Atomic 64-bit read (no race condition)

**Design Approach:**
```systemverilog
// In hpet_config_regs.sv
logic [63:0] r_latched_counter;
logic r_counter_latched;

// Latch counter on LO read
always_ff @(posedge pclk) begin
    if (hwif.hpet_counter_lo.swacc && !hwif.hpet_counter_lo.swmod) begin
        // Read access to LO - latch full counter
        r_latched_counter <= counter;
        r_counter_latched <= 1'b1;
    end

    if (hwif.hpet_counter_hi.swacc) begin
        r_counter_latched <= 1'b0;  // Clear latch flag
    end
end

// Return latched value for HI read
assign hwif.hpet_counter_hi.value = r_counter_latched ?
                                    r_latched_counter[63:32] :
                                    counter[63:32];
```

**Impact:**
- Eliminates counter read race conditions
- More reliable counter value reads
- Better software compatibility

**Verification Steps:**
1. Add latching logic to hpet_config_regs.sv
2. Create test: test_atomic_counter_read
3. Verify: LO read latches full counter
4. Verify: HI read returns latched value
5. Test: Rapid counter increments during read

**Related Files:**
- Modify: `rtl/hpet/hpet_config_regs.sv`
- Create: Test in `dv/tbclasses/hpet/hpet_tests_medium.py`

**Dependencies:** None

**Completion Criteria:**
- [ ] Counter latching implemented
- [ ] Atomic read verified
- [ ] Tests passing
- [ ] Documentation updated

**Notes:**
- Nice feature but not critical
- Current two-read approach works for most use cases
- Deferred until production deployment needs clarify

---

## Documentation (P2)

# TASK-001: 8259 cascade (master/slave) support

**Priority:** P2
**Status:** open. Filed 2026-09-27 by the owner's direction while implementing
RLB/hpet TASK-003: "If more than one 8259 are needed use more."
**Owner:** in progress

**Why this exists:**
RLB/hpet TASK-003 routes HPET timer 1 to **IRQ8** when
`HPET_CONFIG.legacy_replacement` is set, because that is the PC/AT slot the RTC
occupies and HPET replaces. But `rlb_top` instantiates a SINGLE `apb4_pic_8259`
whose `pic_irq_in` is `[7:0]` -- "IRQ inputs (IRQ0-7)". **There is no IRQ8 to
route to.** A PC/AT pair (master + slave cascaded on master IR2) is what makes
IRQ8-15 exist, and IRQ8 is slave input 0.

**What is already there (measured 2026-09-27, not assumed):**
- `PIC_ICW3.cascade[7:0]` exists in `rdl/pic_8259/pic_8259_regs.rdl` as
  `sw = w; hw = r;` -- write-only to software (correct for a real part) and
  already READABLE by hardware. The storage is reachable; nothing reads it.
- `pic_8259_config_regs` already outputs `sngl` (ICW1.SNGL) and the `icw3_wr`
  strobe. It does NOT output the cascade VALUE (see its line 456: ICW3 is
  deliberately unread).
- `pic_8259_core` takes `cfg_sngl` and uses it at exactly one place (line 334)
  to skip the `INIT_WAIT_ICW3` state. Cascade itself is absent.
- `docs/pic_8259_mas/assets/wavedrom/timing/pic_cascade.json` ALREADY depicts
  the intended behaviour: `slave_ir[2]` -> `slave_int` -> `master_ir[2]` ->
  `master_int`, with `cascade_sel = slave` and `vector = slave_vec`. The
  diagram is the spec; `ch01_overview/01_overview.md:196` appends a note saying
  it is illustrative only. That note is what this task deletes.
- `rtl/pic_8259/README.md` is already self-contradictory: line 34 advertises
  "cascade support for multi-level systems" and lines 56-61 list it as a
  feature, while line 177 says "No cascade." This task resolves that.

**The design constraint that shapes everything:**
This block does not acknowledge with an INTA pulse pair -- it acknowledges by
an APB READ of `PIC_INTA` (0x02C), turned into a one-cycle `inta_ack` strobe by
`pic_8259_config_regs`. So there are no CAS[2:0] lines to broadcast a slave ID
on. The equivalent, and the only honest one for this interface, is:

- the master ORs the slave's `int_out` into its cascade IR level, and
- when the level being acknowledged is a cascade level (an `ICW3.cascade` bit),
  the master's `PIC_INTA` read must FORWARD the acknowledge to the slave and
  return the SLAVE's vector instead of its own.

`inta_valid = w_ack_valid && w_running` is the single predicate driving both the
INT pin and the acknowledge, so the diversion has to happen without breaking
that invariant -- it is what guarantees a read can never acknowledge something
the pin did not offer.

**Scope:**
1. `pic_8259_config_regs`: expose `cascade[7:0]` from
   `hwif_out.PIC_ICW3.cascade.value`. ICW3 stays `sw = w` (write-only is the
   real 8259A behaviour; do NOT make it read back).
2. `pic_8259_core`: cascade port group -- slave INT in, acknowledge forward out,
   slave vector in -- and divert `inta_vector` on a cascade level.
3. `apb4_pic_8259`: role parameter plus the cascade ports. Its ONLY port-list
   consumer is `rlb_top.sv:539`; the `rtl/lint_reports/verilator/*.f` hits are
   generated artifacts, not consumers.
4. `rlb_top`: instantiate the slave PIC. Crossbar slave 9 (`0xFEC09000`) is
   currently `Reserved`, tied to `rsvd_apb_PSLVERR = 1'b1` and wired only to
   the xbar -- so the slave PIC takes an ALREADY-DECODED window and
   `apbx_xbar_1to10` does NOT need regenerating.
5. Tests: `initialize_pic` hardcodes `SNGL=1`, so no existing test touches
   cascade and none of the 33 should change. Needs a cascade-mode init path
   plus tests for: slave INT reaching master IR2, the master returning the
   SLAVE's vector, EOI to both, and a masked cascade level blocking the slave.
6. Docs: delete the "not implemented" note under Waveform 1.4, fix the IR2
   priority row, the ICW3 passages in `ch05_registers/01_register_map.md`
   (154-159, 374-377), `ch01_overview/01_overview.md:59`, the
   `pic_8259_mas_index.md` claims (32, 42) and `README.md:177`.

**Completion Criteria:**
- [ ] `ICW3.cascade` reaches the core; ICW3 still reads back 0 to software
- [ ] Slave `int_out` raises the master on its cascade level
- [ ] A master `PIC_INTA` read on a cascade level returns the slave's vector
      and retires the level in BOTH controllers
- [ ] IRQ8-15 exist in `rlb_top`; slave PIC on crossbar slave 9, xbar NOT
      regenerated
- [ ] All 33 existing PIC tests still pass
- [ ] Docs no longer claim cascade is unimplemented

**Blocks:** RLB/hpet TASK-003 (needs IRQ8 to exist before timer 1 can replace
the RTC there).

**Dependencies:** None.

---

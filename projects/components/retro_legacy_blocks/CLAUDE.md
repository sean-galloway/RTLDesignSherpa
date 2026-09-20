<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Claude Code Guide: Retro Legacy Blocks

**Version:** 2.0
**Last Updated:** 2025-10-29
**Purpose:** AI-specific guidance for working with Retro Legacy Blocks (RLB) peripheral blocks

---

## Quick Context

**What:** Collection of production-quality retro-compatible legacy peripherals
**Status:** 🟢 Active Development - HPET Production Ready, 12 more blocks planned
**Your Role:** Help users develop new legacy blocks, integrate existing blocks, understand RLB architecture

**📖 Complete Documentation:**
- `projects/components/retro_legacy_blocks/PRD.md` ← Master requirements for all blocks
- `projects/components/retro_legacy_blocks/README.md` ← Component overview and usage guide
- `docs/hpet_mas/hpet_mas_index.md` ← HPET complete specification

**RLB Address Map:** Single APB entry point at `0x4000_0000`, 4KB windows for clean decode

---

## Critical Rules for All Blocks

### Rule #0.1: Reset Macro Standards - MANDATORY FOR ALL BLOCKS

Use `ALWAYS_FF_RST` / `RST_ASSERTED` from `reset_defs.svh`; a hand-written
`always_ff @(posedge clk or negedge rst_n)` is rejected. Enforced repo-wide --
`/GLOBAL_REQUIREMENTS.md` 1.1 is the authority, the rationale and the failures
behind it are `vault/handbook/design/reset-and-clocking.md`, and
`bin/update_resets.py` converts existing code.

---

### Rule #0.2: FPGA Synthesis Attributes - MANDATORY

Every memory array carries vendor synthesis hints (`ram_style` / `ramstyle`) or
a large memory synthesises into logic. Enforced repo-wide:
`/GLOBAL_REQUIREMENTS.md` 1.2; see `vault/handbook/design/sram-and-memories.md`.

---

### Rule #0.3: Testbench Architecture - MANDATORY SEPARATION

A TB class never lives in a test runner; `/GLOBAL_REQUIREMENTS.md` 2.1 is the
authority. What is specific to this component is the layout and the tier names:

```
projects/components/retro_legacy_blocks/dv/
├── tbclasses/{block}/             # block-specific TB classes
│   ├── {block}_tb.py
│   ├── {block}_tests_basic.py     # runs at TEST_LEVEL=gate
│   ├── {block}_tests_medium.py    # runs at TEST_LEVEL=func
│   └── {block}_tests_full.py      # runs at TEST_LEVEL=full
└── tests/                         # runners, FLAT: test_apb4_{block}.py, conftest.py
```

**The tier FILENAMES are historical; the LEVELS are gate/func/full.**
`{block}_tests_basic.py` defines `{Block}BasicTests` and runs at
`TEST_LEVEL=gate`; `_medium.py` / `{Block}MediumTests` runs at `func`. The files
and classes really are named that way on disk -- do not rename them to match the
level, and do not read the filename as the level.

---

### Rule #0.4: Test Hierarchy - 3 Levels Required

Every block carries all three levels. The gate/func/full convention is repo-wide
(`vault/handbook/dv/running-regressions.md`); the per-block targets here are:

| Level | Tests | Pass rate | Per-test duration |
|---|---|---|---|
| gate | 4-6 | 100% | <30 s |
| func | 5-8 | 100% | 30-90 s |
| full | 3-5 | >=95% | 90 s+ |

---

### Rule #0.5: Register Generation - Use PeakRDL

Registers come from SystemRDL via `bin/peakrdl_generate.py` only -- never raw
peakrdl, which skips the docs and regmap the wrapper emits in lockstep
(`vault/handbook/design/generated-rtl-discipline.md`).

Run it from the block's RDL directory and point `--copy-rtl` at the block's RTL
directory, since the two are no longer parent and child (RLB-007):

```bash
cd rdl/{block}
python $REPO_ROOT/bin/peakrdl_generate.py {block}_regs.rdl --copy-rtl ../../rtl/{block}
```

See `rdl/hpet/` for a complete example.

---

## Block Development Workflow

### Adding a New Block

**1. Directory structure:**
```bash
cd projects/components/retro_legacy_blocks
mkdir -p rdl/{block}                 # SystemRDL: the source of truth
mkdir -p rtl/{block}/filelists       # component + integration filelists
mkdir -p dv/tbclasses/{block}        # TB classes; runners stay flat in dv/tests/
mkdir -p docs/{block}_mas
```

```
rtl/{block}/
├── apb_{block}.sv          # top-level wrapper
├── {block}_core.sv         # core logic
├── {block}_config_regs.sv  # register wrapper
├── {block}_regs_pkg.sv     # PeakRDL generated
├── {block}_regs.sv         # PeakRDL generated
├── filelists/{component,integration}
└── Makefile
```

The RDL lives outside `rtl/` on purpose: every SystemRDL source in the repo
belongs in an `rdl` area rather than scattered under the RTL it generates
(RLB-007, and MISC-001 repo-wide). There is no README beside it -- a file next
to a tool restating how to run the tool is the copy nobody edits.

**2. RTL, TB classes, test suites and runner** take the standard shapes:
Pattern B (`cocotb_test_*` functions behind pytest wrappers), the three
mandatory TB methods, and the tier files named in Rule #0.3. Templates are the
`test-patterns` skill and `/GLOBAL_REQUIREMENTS.md` 2.2 / 3.2. A filelist lands
in the same commit as the module (`vault/handbook/design/filelists.md`).

**3. Documentation:** add the block to `PRD.md`, create
`docs/{block}_mas/{block}_mas_index.md`, update the `README.md` status table.

---

## HPET-Specific Guidance

### HPET Quick Reference

**Status:** ✅ Production Ready (5/6 configurations 100% passing)
**RTL Location:** `rtl/hpet/`
**Test Location:** `dv/tests/test_apb4_hpet.py`

### Critical HPET Rules

#### Rule #1: Timer Cleanup is MANDATORY

**⚠️ ALWAYS Reset Counter Between Tests ⚠️**

```python
# ✅ CORRECT: Clean up at end of test
async def test_64bit_counter(self):
    await self.tb.write_register(HPET_COUNTER_LO, 0xFFFFFFFF)
    # ... test logic ...

    # MANDATORY cleanup
    await self.tb.write_register(HPET_COUNTER_LO, 0x0)
    await self.tb.write_register(HPET_COUNTER_HI, 0x0)
    return True
```

**Why:** Test leaves counter at high value, next test expects counter at 0. Timer 2+ won't fire if counter starts high.

#### Rule #2: Timer Timeout Calculations

**Account for counter starting value when setting timeouts:**

```python
# Calculate timeout based on timer periods
timer_configs = [
    {"period": 100},  # Timer 0 fires at 100
    {"period": 200},  # Timer 1 fires at 200
    {"period": 700},  # Timer 2 fires at 700 (needs most time)
]

# 3x safety margin for latest timer
timeout_ns = max(cfg["period"] for cfg in timer_configs) * 3
timeout_us = (timeout_ns + 999) // 1000
```

#### Rule #3: HPET Register Map

```
0x000: HPET_ID              (num_tim_cap, vendor/revision fixed 0x01/0x01, RO)
0x004: HPET_CONFIG          (hpet_enable; legacy_replacement bit stores, no HW effect)
0x008: HPET_STATUS          (timer interrupt status, W1C)
0x00C: RESERVED             (reads 0)
0x010: HPET_COUNTER_LO      (main counter bits [31:0], RW)
0x014: HPET_COUNTER_HI      (main counter bits [63:32], RW)

Per-Timer Registers (i = 0 to NUM_TIMERS-1), fields at bits [6:2]:
0x100 + i*0x20: TIMER[i]_CONFIG         (enable[2], int_enable[3], type[4], size[5])
0x104 + i*0x20: TIMER[i]_COMPARATOR_LO  (bits [31:0], RW)
0x108 + i*0x20: TIMER[i]_COMPARATOR_HI  (bits [63:32], RW)
```

#### Rule #4: HPET Timer Modes

**One-Shot:**
- Timer fires once when counter >= comparator
- Does NOT automatically reload
- Must reconfigure for next fire

**Periodic:**
- Timer fires repeatedly
- Comparator auto-increments by period value
- Fires indefinitely until disabled

### HPET Common Issues

**Issue: Timer Not Firing**
1. ✅ HPET enabled? (HPET_CONFIG bit 0)
2. ✅ Timer enabled? (TIMER_CONFIG bit 2)
3. ✅ Comparator set correctly?
4. ✅ Counter incrementing?
5. ✅ Counter will reach comparator?
6. ✅ Interrupt enable set? (TIMER_CONFIG bit 3)

**Issue: Tests Failing Inconsistently**
- Most common cause: Missing test cleanup (counter not reset)
- Solution: Add cleanup at end of EVERY test

**See:** Complete HPET guidance in `docs/hpet_mas/hpet_mas_index.md`

---

## Common User Questions

### Q: "Which blocks are implemented?"

**A: Current status:**

| Block | Priority | Status | Address | Documentation |
|-------|----------|--------|---------|---------------|
| **HPET** | High | ✅ Production | 0x4000_0000-0x0FFF | ✅ Complete |
| **8259 PIC** | High | ✅ Implemented | 0x4000_1000-0x1FFF | MAS (docs/pic_8259_mas) |
| **8254 PIT** | High | ✅ Implemented | 0x4000_2000-0x2FFF | MAS (docs/pit_8254_mas) |
| **RTC** | Medium | ✅ Implemented | 0x4000_3000-0x3FFF | MAS (docs/rtc_mas) |
| **SMBus** | Medium | ✅ Implemented | 0x4000_4000-0x4FFF | MAS (docs/smbus_mas) |
| **PM/ACPI** | Medium | ✅ Implemented | 0x4000_5000-0x5FFF | MAS (docs/pm_acpi_mas) |
| **IOAPIC** | Medium | ✅ Implemented | 0x4000_6000-0x6FFF | MAS (docs/ioapic_mas) |
| GPIO | Medium | ✅ Implemented | TBD | MAS (docs/gpio_mas) |
| UART | Medium | ✅ Implemented | TBD | MAS (docs/uart_16550_mas) |
| SPI | Low | 📋 Planned | TBD | N/A |
| I2C | Low | 📋 Planned | TBD | N/A |
| Watchdog | Low | 📋 Planned | TBD | N/A |
| **Interconnect** | Low | 📋 Planned | 0x4000_F000-0xFFFF | N/A |

**📖 See:** `PRD.md` Section 3 for planned block details and Section 4.2 for complete address map

### Q: "How do I integrate a block in my design?"

**A: Each block has APB interface, example:**

```systemverilog
apb4_hpet #(
    .NUM_TIMERS(3),
    .CDC_ENABLE(0)   // VENDOR_ID/REVISION_ID exist but are unwired (fixed 0x01/0x01)
) u_hpet (
    // APB interface
    .pclk         (apb_clk),
    .presetn      (apb_rst_n),
    .s_apb_PADDR   (paddr),
    .s_apb_PSEL    (psel_hpet),
    .s_apb_PENABLE (penable),
    .s_apb_PWRITE  (pwrite),
    .s_apb_PWDATA  (pwdata),
    .s_apb_PRDATA  (prdata_hpet),
    .s_apb_PREADY  (pready_hpet),
    .s_apb_PSLVERR (pslverr_hpet),
    // Block-specific signals
    .hpet_clk     (timer_clk),
    .hpet_resetn   (timer_rst_n),
    .timer_irq    (timer_irq[2:0])
);
```

**📖 See:** `README.md` for integration examples

### Q: "What's the RLB wrapper goal?"

**A: Create unified subsystem combining all blocks with single APB entry point:**

```
RLB Wrapper Architecture:

Single APB Slave → APB Decoder/Bridge → Individual Blocks
(0x4000_0000)    (4KB window decode)   (HPET, 8259, 8254, etc.)
```

**Address Map (4KB windows):**
- `0x4000_0000-0x0FFF`: HPET
- `0x4000_1000-0x1FFF`: 8259 PIC
- `0x4000_2000-0x2FFF`: 8254 PIT
- `0x4000_3000-0x3FFF`: RTC
- `0x4000_4000-0x4FFF`: SMBus
- `0x4000_5000-0x5FFF`: PM/ACPI
- `0x4000_6000-0x6FFF`: IOAPIC
- `0x4000_F000-0xFFFF`: Interconnect/ID/Version
- All others → Error Slave (DECERR/SLVERR)

**Benefits:**
- Single APB slave port (easy integration)
- Drop-in retro-compatible peripheral subsystem
- Clean power-of-2 decode (4KB = bits [15:12])
- 32KB reserved space for expansion

**📖 See:** `PRD.md` Section 4.2 for complete RLB wrapper specification and decoder implementation

### Q: "Why 'Retro Legacy Blocks'?"

**A:**
- **Retro**: Implements proven architectures from older platforms
- **Legacy**: Based on time-tested peripheral interface specifications
- **Blocks**: Collection of independent peripherals

Not experimental - production-ready implementations of time-tested designs.

---

## Quick Commands

```bash
# Always through the area Makefile -- a bare pytest drops the level, the derived
# worker count and the reruns, and skips clean-all.
cd projects/components/retro_legacy_blocks/dv/tests
make list                          # the roots discovered by glob
make clean-all && make run-all-full-parallel
make run-apb4_hpet-gate            # one block, one level
make run-apb4_hpet-gate-waves      # same with waves (never --vcd)
```

Grammar and rationale: `vault/handbook/dv/running-regressions.md`.

---

## PDF Generation Location

**IMPORTANT: PDF files should be generated in the docs directory:**
```
$REPO_ROOT/projects/components/retro_legacy_blocks/docs/
```

**Quick Command:** Use the MAS script. The books live in `*_mas/` directories
and `generate_mas_pdf.sh` is what knows about them:
```bash
cd $REPO_ROOT/projects/components/retro_legacy_blocks/docs
./generate_mas_pdf.sh                      # every book
./generate_mas_pdf.sh --component smbus    # one book
```

`generate_pdf.sh` in the same directory is the OLDER script and targets
`*_spec/` directories that no longer exist here. It used to answer a missing
index with "generated successfully" while writing nothing; that is fixed, and
it now fails loudly, but it still has nothing to build in this component.

---

**Version:** 2.0
**Last Updated:** 2025-10-29
**Maintained By:** RTL Design Sherpa Project

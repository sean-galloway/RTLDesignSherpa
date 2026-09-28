# TASK-007: all RDL lives in an rdl area, as it does elsewhere

> Migrated 2026-09-27 from `vault/Tasks/RLB/closed.md` as **RLB-007** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** P3. Hygiene, and cheaper here than anywhere else in the repo.
**Status:** closed 2026-09-14. DONE 2026-09-11. Raised by Sean 2026-09-04 for consistency with
[[MISC-001]]: all RDL belongs in an `rdl` area rather than scattered under
`rtl/`. All nine sources now live at `rdl/<block>/<name>.rdl` and all nine
register blocks regenerate from there byte-for-byte identically.

**The "only seven references" estimate below was wrong: there were about
forty.** Most are prose in READMEs, TASKS.md and DV comments rather than path
dependencies, so none of them broke the build -- but every one of them would
have become a wrong path. They were swept mechanically. The lesson is the
same one this ledger keeps teaching: count with a script, not by hand.

**Three things the move turned up:**

- `rtl/rtc/rtc_regs.sv` was a DIRECTORY, not a file, holding `rtc_regs.sv`
  and `rtc_regs_pkg.sv`, with the filelist pointing inside it. Someone had
  once run the generator with `--copy-rtl rtc_regs.sv`. Flattened to match
  every other block, filelist fixed.
- The seven `peakrdl/README.md` files were retired rather than moved, per the
  ledger's own instruction and the handbook rule: a README beside a tool
  restating how to run the tool is the copy nobody edits. They had already
  rotted into third copies of the register map. The generation command lives
  in the component `CLAUDE.md`, which now shows the new invocation --
  `--copy-rtl` has to name the RTL directory explicitly, since the RDL and
  the RTL are no longer parent and child.
- `BLOCK_STATUS.md` was retired. It presented itself as current status while
  calling GPIO and UART "Future" and PIC and IOAPIC "In Progress", all four of
  which have shipped with MAS books. The live table is in `CLAUDE.md`.
  `STRUCTURE_SETUP_SUMMARY.md` was kept: it is explicitly a dated record of a
  one-time 2025-10-29 task, so its old paths are accurate to that date.

**Current layout.** Nine `.rdl` sources, each alone in its own
`rtl/<block>/peakrdl/` directory, and no `rdl/` directory exists in the area
at all:

| Block | Source |
|---|---|
| gpio | `rtl/gpio/peakrdl/gpio_regs.rdl` |
| hpet | `rtl/hpet/peakrdl/hpet_regs.rdl` |
| ioapic | `rtl/ioapic/peakrdl/ioapic_regs.rdl` |
| pic_8259 | `rtl/pic_8259/peakrdl/pic_8259_regs.rdl` |
| pit_8254 | `rtl/pit_8254/peakrdl/pit_regs.rdl` |
| pm_acpi | `rtl/pm_acpi/peakrdl/pm_acpi_regs.rdl` |
| rtc | `rtl/rtc/peakrdl/rtc_regs.rdl` |
| smbus | `rtl/smbus/peakrdl/smbus_regs.rdl` |
| uart_16550 | `rtl/uart_16550/peakrdl/uart_16550_regs.rdl` |

**This one is genuinely cheap, unlike MISC-001.** Only seven references exist
across the whole repo, and five are each block's own `*_regmap.py`:

- `rtc_regs.rdl` — `rtl/rtc/rtc_regmap.py`
- `hpet_regs.rdl` — `rtl/hpet/hpet_regmap.py`
- `pic_8259_regs.rdl` — `rtl/pic_8259/pic_8259_regmap.py`
- `pit_regs.rdl` — `rtl/pit_8254/pit_regmap.py`
- `gpio_regs.rdl`, `ioapic_regs.rdl`, `pm_acpi_regs.rdl`, `smbus_regs.rdl`,
  `uart_16550_regs.rdl` — **no references at all**

The remaining two hits are in `bin/peakrdl_to_regmap.py` and
`bin/peakrdl_generate.py`, and both are USAGE EXAMPLES in help text
(`%(prog)s hpet_regs.rdl -o hpet_regmap.py`), not path dependencies. They do
not need to change, though they are worth a glance for whether the example
should name the new location.

**Layout: PER BLOCK.** Decided by Sean 2026-09-04 -- `rdl/<block>/<name>.rdl`,
not a flat directory:

    rdl/gpio/gpio_regs.rdl
    rdl/hpet/hpet_regs.rdl
    rdl/ioapic/ioapic_regs.rdl
    rdl/pic_8259/pic_8259_regs.rdl
    rdl/pit_8254/pit_regs.rdl
    rdl/pm_acpi/pm_acpi_regs.rdl
    rdl/rtc/rtc_regs.rdl
    rdl/smbus/smbus_regs.rdl
    rdl/uart_16550/uart_16550_regs.rdl

Apply it uniformly. Half-application is exactly the state MISC-001 exists to
fix.

**Also worth deciding while in there:** three of the `peakrdl/` directories
carry a `README.md` (hpet, rtc, smbus). Per the handbook, methodology does not
live next to the code -- a README beside a tool restating how to use it is the
copy nobody edits. Fold anything real into the handbook or the block's MAS
rather than moving these along with the sources.

**Method.** Move, update the four `*_regmap.py` references, then REGENERATE
through `bin/peakrdl_generate.py` rather than hand-editing any generated
output -- it emits RTL, docs and regmap in lockstep, and a raw `peakrdl
regblock` desyncs the regmap. Run the RLB tests afterwards.

---

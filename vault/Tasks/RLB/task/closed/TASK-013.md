# TASK-013: the 800-line core cap is honored in the breach

> Migrated 2026-09-27 from `vault/Tasks/RLB/closed.md` as **RLB-014** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**OWNER DECISION 2026-09-14, Sean: "800 is more of a guideline. Going over is
fine."** That settles it -- nothing here was a violation, so there is no work
in this entry and it closes.

For the record, because this was raised once by an agent and will be measured
again by another: the 800 figure is not a repo requirement. It lives in the
owner's personal cross-project coding-style rules ("200-400 lines typical, 800
max", under a MANY SMALL FILES heading written for software). It appears
nowhere in GLOBAL_REQUIREMENTS.md, any CLAUDE.md, the handbook, the skills, or
any checker or hook. This entry's phrase "the repo's 800-line guidance" was
wrong on that point.

Measured across the repo while closing: 144 of 660 files under
projects/components exceed 800 lines, and 18 of 422 under rtl/. Within RLB,
FIVE of the nine files over the line are PeakRDL-generated (pm_acpi_regs 2791,
smbus_regs 1499, uart_16550_regs 1282, rtc_regs 958, pic_8259_regs 850) and
cannot be split at all -- they regenerate from the RDL.

WORTH KEEPING, and the reason this entry was not pure noise: the cores are not
hard to split because they are long, they are hard to split because the DV
WHITEBOXES them. Measured distinct internal references from dv/:
  u_rtc_core    18   r_commit_busy, r_commit_pend, r_second_tick,
                     selected_clk, plus eight sub-instances
  u_uart_core    7   the coupling this entry already documented
  u_pm_acpi_core 5
So the ordering is inverted -- the LARGEST core (rtc, 1726) is the most
coupled and the hardest to refactor, and pm_acpi is the most tractable. That
coupling, not line count, is what would block any future restructuring. It is
recorded here rather than filed as its own task; open one if it ever matters.


**Priority:** P3. Hygiene and reviewability, not a defect — every block is
green. Raised 2026-09-14 by the uart_16550 verification agent and confirmed
by measurement.
**Status:** closed 2026-09-14. open, and it is a POLICY question for the owner, not a fix an
agent should take unilaterally.

Measured `wc -l` on the nine RLB cores:

```
1706  rtc/rtc_core.sv
1328  pm_acpi/pm_acpi_core.sv
 888  smbus/smbus_core.sv
 842  uart_16550/uart_16550_core.sv     <- 759 before the RLB-013 features
 705  hpet/hpet_core.sv
 666  pic_8259/pic_8259_core.sv
 552  ioapic/ioapic_core.sv
 331  pit_8254/pit_core.sv
 227  gpio/gpio_core.sv
```

Four are over the repo's 800-line guidance. smbus is the pointed one: it was
held to exactly 800 during the #58 review and has since grown to 888.

**The obvious cut in uart is blocked by DV.** The tests whitebox
`r_tx_state`, `r_tx_wr_ptr`, `r_tx_rd_ptr`, `w_tx_fifo_count`, `w_tx_bit` and
the RX equivalents at `u_uart_core` scope, so extracting TX or RX breaks tests
that an RTL agent may not edit. That constraint is why round 2 split modem and
intr instead, and the sweep confirmed that split was DV-safe (zero references
into `u_intr` or `u_modem`). Any split here is a DV change first and an RTL
change second.

---

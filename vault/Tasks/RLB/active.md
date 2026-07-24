# RLB — Active (in progress)

---

## RLB-004 — Triage & fix the RTL bugs found by the MAS/RTL review
**Status:** active 2026-07-22 — awaiting owner design decisions, not started in RTL

The 9 `bug`-labeled issues from RLB-001. These are logic defects, not doc fixes;
each needs a design decision before any RTL change. Left in `active` (not `open`)
because they are surfaced and filed with evidence, but deliberately paused for
the owner. MAS docs currently carry factual "not implemented / deviates" notes
so they don't promise absent behavior.

Highest-impact RTL bugs (see issue bodies for RTL file:line evidence):
- **hpet #46** — any write to HPET_STATUS clears ALL irq bits (not per-bit W1C);
  second timer fire while a bit is pending sets all 8 status bits; 64-bit counter
  write drops a half.
- **ioapic #48** — every edge-triggered interrupt delivered twice (delayed
  pending-clear reopens the arbitration window).
- **pic_8259 #50** — ISR is never set (EOI/nesting/special-mask dead); edge IRR
  never clears (int_out latches high).
- **pit_8254 #52** — GATE pause/resume doesn't exist (GATE is start-enable only).
- **smbus #58** — timeout detection dead (undriven enable); master never drives
  SCL (push-pull, no clock-stretch/arbitration); PEC non-functional.
- **pm_acpi #54, gpio #44, rtc #56, uart_16550 #60** — see issue bodies.

Also open but not filed as a bug: several unpushed commits (RLB-001..002 doc
fixes) sit on branch `dmas-reorg-and-stream-perf` scoped to RLB docs; owner to
decide push/branch placement (owner's WIP shares that branch, ~234 files).

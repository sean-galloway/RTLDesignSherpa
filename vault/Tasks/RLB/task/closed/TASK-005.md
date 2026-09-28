# TASK-005: Clean up rtc wavedrom README third register-map copy

> Migrated 2026-09-27 from `vault/Tasks/RLB/closed.md` as **RLB-005** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** closed 2026-09-08

Commit `a1b76d08`. The README's third, contradictory map (TIME_LO@0x00,
REG_A/B/C, UIP, rate-select — a CMOS-style RTC this RTL never was) replaced
with the real 13-register map from rtc_regs.rdl; signal list and scenarios
rewritten to the RTL; rtc_periodic_interrupt.{json,svg,png} redrawn (it
contradicted the caption RLB-002 had already corrected);
rtc_update_in_progress.{json,svg} deleted (no UIP exists; nothing embedded
it). Verified against rtc_core.sv (irq gating at :439).

---

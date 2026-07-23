# RLB — Closed (done)

Completed retro-legacy-block work. Kept for history.

---

## RLB-001 — MAS/RTL quality review (9 blocks) via Kimi
**Status:** closed 2026-07-22

Ran a Kimi (kimi-k3) accuracy review of all 9 MAS-bearing RLB blocks (gpio,
hpet, ioapic, pic_8259, pit_8254, pm_acpi, rtc, smbus, uart_16550), each MAS
spec checked against its RTL as ground truth. No HAS docs exist — MAS only.
Pipeline + snapshots: `/mnt/data/github/rlb-doc-review/` (build_rlb_bundle.py,
RLB_REVIEWER_BRIEF.md, dispatch_rlb.py, send_rlb_round.py); reports and
`_DIGEST.md` in `results/kimi-k2/round_1/`. Findings filed as 18 GitHub issues
(#43–#60) + tracking #61: one `documentation` (MAS-wrong) and one `bug`
(RTL-BUG) issue per block. Every block had Critical findings.

---

## RLB-002 — Fix wrong-map MAS register documentation (5 blocks)
**Status:** closed 2026-07-22

The five blocks whose entire register map was wrong. Each MAS register chapter
+ ch01 summary (+ wavedrom README where it held a duplicate map) rewritten
against the RTL decode. Every offset independently re-derived from the RTL
`*_regs.sv` decode by the main session (not just agent-attested) — the check
script is `scratchpad/verify_regmap.sh` (RTL decode vs doc table offsets).

- **pic_8259** — commit `2fe735d1`, issue #49. Flat decode replaces the
  8259 A0=0/A0=1 model; documented PIC_CONFIG (pic_enable gates all operation)
  + PIC_STATUS. 11/11 offsets verified.
- **pm_acpi** — commit `5da2b442`, issue #53. Real ACPI_*/PM1_*/GPE0 map;
  documented the clock-gate/power-domain/wake/reset block at 0x50–0x6C that the
  review itself missed. 21/21 offsets verified.
- **rtc** — commit `ea724866`, issue #55. Every offset was wrong; removed
  phantom registers (century/weekday/date/alarm-date), fixed HR24 polarity,
  documented the time_set_mode protocol. 13/13 offsets verified.
- **smbus** — commit `cd415977`, issue #57. STATUS/CONTROL were swapped;
  documented INT_STATUS/PEC/BLOCK_COUNT the review stopped short of. 15/15.
- **uart_16550** — commit `871e34bc`, issue #59. DLAB remapping doesn't exist;
  flat map, all ch04 examples corrected, RBR-in-[15:8], W1C on LSR/MSR. 11/11.

RTL bugs surfaced by the review are NOT fixed here — tracked in the `bug`
issues (#50/#54/#56/#58/#60) and RLB-004 below.

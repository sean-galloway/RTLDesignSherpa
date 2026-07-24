# RLB — Retro Legacy Blocks

Task rollup for the retro legacy peripheral blocks (gpio, hpet, ioapic,
pic_8259, pit_8254, pm_acpi, rtc, smbus, uart_16550). MAS specs live under
`projects/components/retro_legacy_blocks/docs/<block>_mas/`; RTL under
`rtl/<block>/`. Kimi review pipeline + reports: `/mnt/data/github/rlb-doc-review/`.

| State | Count | Tasks |
|---|---|---|
| active | 1 | RLB-004 (RTL bugs — awaiting owner) |
| open | 2 | RLB-003 (4 remaining MAS map fixes), RLB-005 (rtc wavedrom README) |
| closed | 2 | RLB-001 (Kimi review), RLB-002 (5 wrong-map MAS fixes) |
| dropped | 0 | — |

## Shortlist

- **Next up (RLB-003):** fix gpio #43, hpet #45, ioapic #47, pit_8254 #51 MAS
  register docs against RTL — same verified method as the 5 already done.
- **Quick loose end (RLB-005):** rtc wavedrom README still has a stale third map.
- **Blocked on owner (RLB-004):** 9 RTL bugs filed (#44–#60 even) need design
  decisions before RTL changes.

## Done

5 of 9 MAS register maps corrected + verified (pic_8259 #49, pm_acpi #53, rtc
#55, smbus #57, uart_16550 #59), all committed scoped on `dmas-reorg-and-stream-perf`,
unpushed. Register-map review filed as 18 issues + tracking #61.

> Note: this area supersedes the pre-migration
> `projects/components/retro_legacy_blocks/TASKS.md` referenced from the master
> `/vault/Tasks/INDEX.md` `retro-legacy` row (still marked `pending`). Repoint that row
> to `RLB` when the remaining source TODOs are folded in.

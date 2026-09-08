# RLB — Retro Legacy Blocks

**Next ID: RLB-008** — never recycle a number, even when its task closed.

Task rollup for the retro legacy peripheral blocks (gpio, hpet, ioapic,
pic_8259, pit_8254, pm_acpi, rtc, smbus, uart_16550). MAS specs live under
`projects/components/retro_legacy_blocks/docs/<block>_mas/`; RTL under
`rtl/<block>/`. Kimi review pipeline + reports: `/mnt/data/github/rlb-doc-review/`.

| State | Count | Tasks |
|---|---|---|
| active | 1 | RLB-004 (RTL bugs — awaiting owner) |
| open | 2 | RLB-006 (test scrub, after qc/humanize), RLB-007 (RDL relocation) |
| closed | 4 | RLB-001 (Kimi review), RLB-002 (5 wrong-map MAS fixes), RLB-003 (4 targeted MAS fixes), RLB-005 (rtc wavedrom README) |
| dropped | 0 | — |

## Shortlist

- **In flight (2026-09-08):** confirming Kimi qc round_2 over the rebuilt
  9-block bundle; humanize pass follows once it comes back clean.
- **Blocked on owner (RLB-004):** 9 RTL bugs filed (#44–#60 even) need design
  decisions before RTL changes; each re-verified 2026-09-08 with a dated
  issue comment.
- **After qc/humanize (RLB-006):** test scrub. Then RLB-007 (RDL relocation).

## Done

All 9 MAS register documentation issues fixed and closed (#43–#59 odd):
RLB-002's five verified on main (their unpushed-branch limbo resolved by the
branch merge), RLB-003's four integrated 2026-09-08 from the full round_1
critiques. Review filed as 18 issues + tracking #61 (roll-up comment posted).

> Note: this area supersedes the pre-migration
> `projects/components/retro_legacy_blocks/TASKS.md`. The master
> `/vault/Tasks/INDEX.md` row now points here; the remaining rtl/*/TODO source
> items still need to be folded in.

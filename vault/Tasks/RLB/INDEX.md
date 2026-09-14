# RLB — Retro Legacy Blocks

**Next ID: RLB-016** — never recycle a number, even when its task closed.

Task rollup for the retro legacy peripheral blocks (gpio, hpet, ioapic,
pic_8259, pit_8254, pm_acpi, rtc, smbus, uart_16550). MAS specs live under
`projects/components/retro_legacy_blocks/docs/<block>_mas/`; RTL under
`rtl/<block>/`. Kimi review pipeline + reports: `/mnt/data/github/rlb-doc-review/`.

| State | Count | Tasks |
|---|---|---|
| active | 0 | — |
| open | 9 | RLB-006 (test scrub), RLB-007 (RDL relocation), RLB-008 (ioapic residual features), RLB-009 (pm_acpi residual features), RLB-010 (rtc leftovers), RLB-011 (smbus residual features), RLB-012 (regblock reset polarity), RLB-013 (uart_16550 residual features), RLB-014 (800-line core cap), RLB-015 (RESET_ACTIVE_HIGH SYNCASYNCNET, unverified) |
| closed | 5 | RLB-001 (Kimi review), RLB-002 (5 wrong-map MAS fixes), RLB-003 (4 targeted MAS fixes), RLB-004 (the 9 RTL bugs), RLB-005 (rtc wavedrom README) |
| dropped | 0 | — |

## Shortlist

- **qc + humanize arc DONE (2026-09-08):** Kimi qc round_2 and round_3
  findings integrated for all 9 blocks; humanize round_1 applied to every
  book (book pages only -- PRD/IMPLEMENTATION_STATUS/design-sketch pages
  reverted), each block committed separately with tag-survival 0 fatal,
  0 suspect, emoji 0 and its `#NN` deviation references counted before and
  after. A power outage killed the driver mid-smbus; `run_humanize_resumable.sh`
  re-sent only smbus + uart_16550 (results in
  `results/humanize-kimi-k2/round_1/`). RLB-006 is now unblocked.
- **RLB-004 CLOSED 2026-09-14.** All 9 RTL bugs (#44–#60 even) and tracking
  #61 are closed on GitHub; the fixes landed 2026-09-10/11. Verified before
  closing: clean `make clean-all && make run-all-full-parallel` over all nine
  blocks at REG_LEVEL=FULL, 63 passed / 0 failed.
- **Nothing is active.** What remains open is deliberate scope (RLB-008
  ioapic modes, RLB-010 rtc clock mux) plus the two filed 2026-09-14. The one
  genuine open work item is RLB-010's missing formal area.

## Done

All 9 MAS register documentation issues fixed and closed (#43–#59 odd):
RLB-002's five verified on main (their unpushed-branch limbo resolved by the
branch merge), RLB-003's four integrated 2026-09-08 from the full round_1
critiques. Review filed as 18 issues + tracking #61 (roll-up comment posted).

> Note: this area supersedes the pre-migration
> `projects/components/retro_legacy_blocks/TASKS.md`. The master
> `/vault/Tasks/INDEX.md` row now points here; the remaining rtl/*/TODO source
> items still need to be folded in.

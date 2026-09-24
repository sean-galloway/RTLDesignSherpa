# RLB — Retro Legacy Blocks

**Next ID: RLB-018** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each a directory with its own INDEX and
its own ID sequence. **Every item is its own file**, `<ID>.md`, filed under
the directory for its state (`open/`, `active/`, `closed/`, `dropped/`).
Pick the lane before filing:

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-001` |
| [bug/](bug/INDEX.md) | a defect with a reproduction | `BUG-001` |
| [issue/](issue/INDEX.md) | an anomaly/risk/question not yet diagnosed | `ISSUE-001` |

**The pages at this level are the LEGACY task lane.** They are frozen: close
them out where they stand, and do not add to them. New work of any kind goes in
a lane above. See [the convention](../INDEX.md) for the full definitions.


Task rollup for the retro legacy peripheral blocks (gpio, hpet, ioapic,
pic_8259, pit_8254, pm_acpi, rtc, smbus, uart_16550). MAS specs live under
`projects/components/retro_legacy_blocks/docs/<block>_mas/`; RTL under
`rtl/<block>/`. Kimi review pipeline + reports: `/mnt/data/github/rlb-doc-review/`.

| State | Count | Tasks |
|---|---|---|
| active | 0 | — |
| open | 0 | — |
| closed | 16 | RLB-001 (Kimi review), RLB-002 (5 wrong-map MAS fixes), RLB-003 (4 targeted MAS fixes), RLB-004 (the 9 RTL bugs), RLB-005 (rtc wavedrom README), RLB-006 (test scrub), RLB-007 (RDL relocation), RLB-008 (ioapic features -- four companions), RLB-009 (pm_acpi residual features), RLB-010 (rtc leftovers), RLB-011 (smbus residual features), RLB-012 (regblock reset polarity), RLB-013 (uart_16550 residual features), RLB-014 (800-line cap -- owner: a guideline, over is fine), RLB-015 (SYNCASYNCNET, measured + waived), RLB-016 (unmapped address hung the bus -- crossbar is generated now) |
| dropped | 0 | — |

## Shortlist

- **qc + humanize arc DONE (2026-09-08):** Kimi qc round_2 and round_3
  findings integrated for all 9 blocks; humanize round_1 applied to every
  book (book pages only -- PRD/IMPLEMENTATION_STATUS/design-sketch pages
  reverted), each block committed separately with tag-survival 0 fatal,
  0 suspect, emoji 0 and its `#NN` deviation references counted before and
  after. A power outage killed the driver mid-smbus; `run_humanize_resumable.sh`
  re-sent only smbus + uart_16550 (results in
  `results/humanize-kimi-k2/round_1/`). RLB-006 was unblocked by this and has
  since been DONE for retro_legacy_blocks (2026-09-11); its residual is the
  same scrub in the rtl/ areas and the testqc round, neither of which is RLB
  work. This line said "is now unblocked" for three days after it finished --
  reading it as current work cost a session's planning time on 2026-09-14.
- **RLB-004 CLOSED 2026-09-14.** All 9 RTL bugs (#44–#60 even) and tracking
  #61 are closed on GitHub; the fixes landed 2026-09-10/11. Verified before
  closing: clean `make clean-all && make run-all-full-parallel` over all nine
  blocks at REG_LEVEL=FULL, 63 passed / 0 failed.
- **RLB-010 CLOSED 2026-09-14.** Its formal area was created, and its last
  bullet -- the combinational clock mux -- was resolved by `rtc_clk_mux`
  (`ae03c6b43`), the device-specific cell the entry itself named as the real
  answer. Verified before closing: clean `make clean-all &&
  make run-all-full-parallel` over all nine blocks, 63 passed / 0 failed in
  343.50s. NOTE: the open count above read 9 while listing ten tasks, so it was
  already wrong by one; it is now 9 listing nine, corrected deliberately rather
  than made right by the removal.
- **Nothing is active and nothing is open.** SEVEN closed 2026-09-14: five
  were already carrying a DONE status of their own (006, 007, 009, 011, 013),
  RLB-014 closed on the owner's call that the 800-line figure is a
  guideline rather than a rule -- going over is fine, and it is not a repo
  requirement in any case -- and RLB-016 closed when rlb_top moved onto the
  GENERATED crossbar. The hand-rolled sibling sat outside the generator flow
  and so never received its decode-miss fix, which is why an unmapped address
  wedged the bus; the variant is now REGISTERED in generate_xbars.py, so it
  regenerates with the family instead of drifting again.

## Done

All 9 MAS register documentation issues fixed and closed (#43–#59 odd):
RLB-002's five verified on main (their unpushed-branch limbo resolved by the
branch merge), RLB-003's four integrated 2026-09-08 from the full round_1
critiques. Review filed as 18 issues + tracking #61 (roll-up comment posted).

> Note: this area supersedes the pre-migration
> `projects/components/retro_legacy_blocks/TASKS.md`. The master
> `/vault/Tasks/INDEX.md` row now points here; the remaining rtl/*/TODO source
> items still need to be folded in.

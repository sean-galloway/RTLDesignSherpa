# TASK-003: Fix remaining MAS register documentation (4 blocks)

> Migrated 2026-09-27 from `vault/Tasks/RLB/closed.md` as **RLB-003** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** closed 2026-09-08

The four targeted-fix blocks, integrated from the FULL round_1 critiques (not
just the issue-body Critical/High subset), every finding re-verified against
the current RTL first — a month of tree movement inverted one finding
(pit_8254 H4: CDC has since been implemented, 6/6 both configs on a clean
build) and healed parts of another (gpio L12 via the apb4 rename).

- **gpio** — commit `cb620291`, issue #43. CONTROL[1] INT_ENABLE documented
  at 8 surfaces (cited 4); 4 missing registers added to every map; reset
  values fixed; interrupt semantics rewritten to the RTL; atomic-write
  change-detection documented as a deviation (#44). Bonus: rtl/gpio/README.md
  had a fictional 16-bit LO/HI map.
- **hpet** — commit `368dcf83`, issue #45. HPET_ID hardcoded reality (+
  recomputed examples); dead timer_value_set (6 sites incl. the seeding RTL
  header comment); registered irq; sticky-in-both-modes; ghost
  HPET_CAPABILITIES swept 18 -> 0; wavedrom/graphviz maps redrawn (10 SVGs).
- **ioapic** — commit `1fceb370`, issue #47. Real direct decode documented
  (0x008-0x0D0 reachable without IOREGSEL/IOWIN); latency, glitch, FSM-output
  and status-page fixes; #48 deviation notes at both fire-once claims.
- **pit_8254** — commit `19c703de`, issue #51. Real interface (12-bit PADDR,
  PPROT, pit_resetn); no-SLVERR + 0x20 aliasing; PIT_STATUS reset recomputed
  0x00404040; RTOS-tick ISR fixed (readback-reload storm); count range
  1-65535.

Cross-block status surfaces reconciled in `81e09db8` (CLAUDE.md table said 8
implemented blocks were "Planned"; RLB_MODULE_AUDIT.md got the
historical-snapshot banner). Pre-commit sv-parse gate fixed en route
(`9d976529`: nested filelists were invisible to its index). All four issues
closed with commit references; RTL-bug issues #44/#46/#48/#52 re-verified
with dated comments.

---

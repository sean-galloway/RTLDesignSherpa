# pumice — task rollup

DDR2/LPDDR2 memory controller (`projects/components/memory-controllers/pumice-ddr2-lpddr2/`).

| State | Count |
|---|---|
| [active](active.md) | 1 |
| [open](open.md) | 5 |
| [closed](closed.md) | 5 |
| [dropped](dropped.md) | 1 |

## Active

- **PUMICE-001** — runtime-config axes corrupt data (#42). Two RTL fixes landed
  2026-07-23 (AP-column guard, page_policy encoding); board re-validation pending.

## Open shortlist

- **PUMICE-004** — refresh collides with an open row. The highest-value RTL
  defect: confirmed on silicon as the residual row-sized corruption, instrument
  already wired, fix not started. Gates PUMICE-006.
- **PUMICE-002** — `test_pumice_top_csr` read path returns zero beats.
  Pre-existing, bisected twice; the only red test in the suite.
- **PUMICE-003** — char-families `bank_interleave` integrity fail. Same class as
  PUMICE-001; re-check after the landed fixes before debugging further.
- **PUMICE-007** — retire the superseded deskew RTL + CSR (#39).
- **PUMICE-006** — QoS + advanced scheduling. Gated on a clean board.

## Reading order for someone picking this up

PUMICE-001 and PUMICE-004 are the live correctness work and they interact:
both are arbiter command-sequencing behaviour under a registered-feedback
picker. PUMICE-002 and PUMICE-003 are both pre-existing and both trace to the
same window when the top/char sims were compile-broken by filelist drift, so
neither is a regression from current work.

Practice and rationale live in the [handbook](../../docs/handbook/INDEX.md);
this directory tracks *work* only. `/GLOBAL_REQUIREMENTS.md` wins on conflict.

# pumice — task rollup

DDR2/LPDDR2 memory controller (`projects/components/memory-controllers/pumice-ddr2-lpddr2/`).

| State | Count |
|---|---|
| [active](active.md) | 1 |
| [open](open.md) | 8 |
| [closed](closed.md) | 6 |
| [dropped](dropped.md) | 1 |

## Active

- **PUMICE-001** — runtime-config axes corrupt data (#42). Two RTL fixes landed
  2026-07-23 (AP-column guard, page_policy encoding); board re-validation pending.

## Open shortlist

- **PUMICE-004** — refresh collides with an open row. The highest-value RTL
  defect: confirmed on silicon as the residual row-sized corruption, instrument
  already wired, fix not started. Gates PUMICE-006.
- **PUMICE-003** — char-families `bank_interleave` integrity fail. Same class as
  PUMICE-001; re-check after the landed fixes before debugging further.
- **PUMICE-007** — retire the superseded deskew RTL + CSR (#39).
- **PUMICE-010** — top-tier shared sim_build has no compile lock; clean
  parallel runs self-destruct (48/31 spurious fails). Serial = workaround.
- **PUMICE-006** — QoS + advanced scheduling. Gated on a clean board.

## Reading order for someone picking this up

PUMICE-001 and PUMICE-004 are the live correctness work and they interact:
both are arbiter command-sequencing behaviour under a registered-feedback
picker. PUMICE-003 is pre-existing from the window when the top/char sims were
compile-broken by filelist drift (PUMICE-002, closed 2026-08-24, came from the
same window — a hand-packed CSR write that rotted; check PUMICE-003 for the
same class of stale-test cause before suspecting RTL).

Practice and rationale live in the [handbook](../../handbook/INDEX.md);
this directory tracks *work* only. `/GLOBAL_REQUIREMENTS.md` wins on conflict.

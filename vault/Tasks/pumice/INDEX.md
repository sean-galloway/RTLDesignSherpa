# pumice — task rollup

DDR2/LPDDR2 memory controller (`projects/components/memory-controllers/pumice-ddr2-lpddr2/`).

| State | Count |
|---|---|
| [active](active.md) | 0 |
| [open](open.md) | 6 |
| [closed](closed.md) | 10 |
| [dropped](dropped.md) | 1 |

## Active

(none — the correctness backlog is empty)

## Open shortlist

- **PUMICE-006** — advanced modes: MECHANISMS COMPLETE 2026-08-27. All
  three axes landed (Axis 1 scheduling, Axis 2 paging, Axis 3 refresh),
  every mode OFF by default with encoding 0 = build default and each
  mechanism mutation-proven. Open only for gaps 013 reports back.
- **PUMICE-013** — characterize + tune those modes (the big one: mode
  sweeps in sim + on the board, recommended defaults per workload
  family). Wants PUMICE-008 landed first so the numbers do not carry the
  AMBA-HISTCH1 accounting error.
- **PUMICE-008** — ACTIVE: adopt the external axi4_intf_master_observer and
  retire the harness's hand-rolled meters/hists (Sean 2026-08-26: no
  monitor/perf logic inside pumice; cheap interesting counters stay).
  PUMICE-011 (root-caused: AMBA-HISTCH1 + FIFO sizing) and PUMICE-010
  (per-worker sim_builds; clean parallel now 61/61) are CLOSED.

## Reading order for someone picking this up

PUMICE-001 (board re-run) is the only live correctness item; everything else
open is cleanup or gated features. The July task cluster is fully resolved:
PUMICE-002 (stale hand-packed CSR write), PUMICE-003 (bank_lsb=0 striping,
fixed fcafc435), and PUMICE-004 (refresh collision, fixed 38c8ae63 with the
detector armed + mutation-proven 2026-08-24) all closed — the ledger had gone
stale against landed fixes FOUR times (002/003/004/007), so measure before debugging. PUMICE-006's
entry gate is now the PUMICE-001 board trip + a tiny-tREFI re-soak on the
08-16 bitstream.

Practice and rationale live in the [handbook](../../handbook/INDEX.md);
this directory tracks *work* only. `/GLOBAL_REQUIREMENTS.md` wins on conflict.

# TASK-003: give jet its hit latency back (sync-read address lead, v3 classify overlap)

**Date:** 2026-11-08
**Priority:** P2
**Status:** OPEN
**Owner:** jet

## Why

The Genesys2 pair-rig sweeps across the FPGA review bins (cache-ip/common-ip
TASK-001) show jet's resident read-hit latency at 6 cycles against the v2
baseline's 3 and amber's 4:

| step | lat_min | r4k_we0 cycles / 20k txn | disjoint64k cycles |
|---|---|---|---|
| v2 baseline (2026-11-03, 100 MHz) | 3 | 100,480 | 402,042 |
| v3 capture/classify pipeline (bin 3) | 5 | 140,464 | 407,409 |
| BRAM sync-read data array (bin 5) | 6 | 160,608 | 417,246 |
| bins 6-10 (RAM stores, snoop fix, reset tree) | 6 | 160,608 | 417,246 |

Two cycles are the v3 lookup split (ISSUE-001's fix); one is the registered
data array read. Amber paid nothing for the same array because `l1_control`
presents the data address in LOOKUP, a stage ahead of the way select.

## What

1. Present the data-array read address one stage earlier in `jet_control`
   (the amber pattern: address leads, "address last cycle was mine"
   qualifier on the data), keeping `DATA_SYNC_READ=1` and the BRAM mapping.
   Expected: lat_min 6 -> 5, r4k_we0 back to ~140k.
2. Then look at whether classify can overlap the tag read in v3 instead of
   following it, which is the remaining +2 against v2. This changes the
   accept handshake; formal (safety 64, live 176) and the pair rig are the
   gate, as for v3.

## Done when

- Jet component DV gate+func+full green; jet-g2 harness gate green; from-reset
  disjoint64k board run == the 20k cosim CRCs.
- `formal/jet/jet_control` prove, prove-live and cover PASS on the final flat.
- Genesys2 bin with lat_min <= 5 at 100 MHz, WNS >= 0, sweep err 0; the
  per-step table above extended with the new row in the task's closure.

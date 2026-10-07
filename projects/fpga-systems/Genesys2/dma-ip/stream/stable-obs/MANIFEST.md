# build-obs archive — 4 channels, 32-entry tally CAM

Archived 2026-09-07 15:30 because the previous obs bitstream was
destroyed by a `make clean-all` before anyone knew whether obs still fit. It
did not: obs had been synthesizing at 100.01% of the device's LUTs and only ever
placed by luck. Do not clean build-obs without confirming this copy exists.

| item | value |
|---|---|
| bitstream | `stream_mon_4ch_obs_obsmaster_obsslave.bit` |
| sha256 (first 16) | `6a44cdc8aa08feeb` |
| built | 2026-09-07 15:30 |
| tree HEAD at build | `d4fe53a7` (includes the round-robin tally arbiter fix 7c7d3fe4) |
| WNS | **+2.191 ns** |
| LUT (synth) | see reports/utilization_synth.txt |
| node overlaps | 0 |

## Generics

    STREAM_NUM_CHANNELS = 4        (8 does not fit; 6 does not route)
    MON_N_PROFILE       = 32       (owner decision 2026-09-07)
    USE_AXI_MONITORS    = 0
    OBS_ENABLE_MON_TAPS = 1        (this is what obs exists to exercise)
    MON_ERROR_FLAVOR    = 2        (all cones)
    VCO 1200 / CLKOUT0_DIVIDE 20 = 60 MHz

## Why 4 channels and a 32-entry CAM

obs is the only flavour building both observers with every monitor cone, and it
had outgrown the xc7k325t. The route to a fitting build, measured:

| config | LUT synth | outcome |
|---|---|---|
| 8ch, CAM 64 | 203,827 (100.01%) | placer failed |
| 6ch, CAM 64 | 196,808 (96.57%) | placer failed, 3,470 LUTs over at placement |
| 4ch, CAM 64 | 187,785 (92.14%) | placed, then **132 signals unrouted / 83 overlaps** |
| 4ch, CAM 32 | 186,426 (91.47%) | **routes clean, 0 overlaps, +0.624 ns** |

Channel count fixed capacity; it did NOT fix routability. The 64-entry profile
CAM in BOTH tallies was the congestion source, and half its entries were keyed
to packet classes nothing emits. Owner: obs validates the master/slave monitor
blocks, which is per-observer and unaffected by channel count.

## Revalidated 2026-09-07 19:26 (rebuild carrying the arbiter fix)

Board campaign on this exact bitstream, all classes keyed with 0 unexpected:
compl 13470, perf 1138653, addrmatch 13230, error 13206, threshold 13206,
debug 13212. timeout 21 -- below the campaign's 1000-packet floor, which is
TASK-083 (reporter saturation), not a defect in this build. Identical to the
pre-arbiter-fix build, i.e. the fix caused no regression here. REVALIDATED.

# Core Timing

Core parameters govern row and column command spacing within and
between banks. Values below are the spec's ns bins (fast / typical /
slow), which apply across speed grades unless noted; each parameter
also has a minimum in clocks (min tCK). RL/WL and tDQSCK are
frequency-dependent.

## Row-cycle parameters

| Symbol | Definition | Applies between | Min (typ bin) |
| --- | --- | --- | --- |
| tRCD | RAS-to-CAS delay: row open to first column command | ACT -> RD/WR to same bank | 15 / 18 / 24 ns, min 3 tCK |
| tRAS | Row active time: minimum time a row must stay open | ACT -> PRE to same bank | 42 ns, min 3 tCK; max 70 us |
| tRPpb | Precharge time, single bank | PRE (one bank) -> ACT to that bank | 15 / 18 / 24 ns, min 3 tCK |
| tRPab | Precharge time, all banks | PRE-all -> ACT to any bank | 4-bank: = tRPpb; 8-bank: 18 / 21 / 27 ns, min 3 tCK |
| tRC | Row cycle: minimum ACT-to-ACT to the same bank | ACT -> ACT, same bank | tRAS + tRPpb (or tRAS + tRPab after PRE-all) |
| tRRD | ACT-to-ACT spacing, different banks | ACT -> ACT, different banks | 10 ns, min 2 tCK |
| tFAW | Four-activate window: at most 4 ACTs in any rolling window | 1st -> 5th ACT (8-bank only) | 50 ns (60 ns slowest grade), min 8 tCK |

tRPab exceeds tRPpb only on 8-bank devices - it keeps an all-bank
precharge inside the current envelope of a 4-bank part. REFpb counts as
an activation for tFAW.

## Column-cycle parameters

| Symbol | Definition | Applies between | Min (typ bin) |
| --- | --- | --- | --- |
| tRTP | Read to precharge: last-prefetch analog delay before PRE | RD -> PRE to same bank | 7.5 ns, min 2 tCK |
| tWR | Write recovery: last write data to PRE | end of WR burst -> PRE to same bank | 15 ns, min 3 tCK |
| nWR | tWR expressed in clocks for auto-precharge | (MR1 field) | RU(tWR/tCK), 3-8 |

For tRTP the spec's clock counting starts BL/2 - 2 clocks after the RD
command on S4 (BL/2 - 1 on S2); the 7.5 ns analog floor then applies
from the last internal prefetch. With AP=1 the device enforces these
itself - the controller only has to have programmed nWR correctly.

## Latency programming (MR2) and read access time

| Speed grade | RL | WL | tCK (ns) |
| --- | --- | --- | --- |
| LPDDR2-1066 | 8 | 4 | 1.875 |
| LPDDR2-933 | 7 | 4 | 2.15 |
| LPDDR2-800 | 6 | 3 | 2.5 |
| LPDDR2-667 | 5 | 2 | 3.0 |
| LPDDR2-533 | 4 | 2 | 3.75 |
| LPDDR2-466 and slower | 3 | 1 | >= 4.3 |

| Symbol | Definition | Applies between | Value |
| --- | --- | --- | --- |
| tDQSCK | Strobe output access time from clock | RD -> DQS/DQ valid | 2500-5500 ps (may span multiple clocks) |
| tDQSQ | DQS-to-DQ skew within a beat | DQS edge -> DQ edge | 200 ps (1066) to 700 ps (200) |
| tQHS | Data hold skew factor | hold-time budgeting | 230 ps (1066) to 1000 ps (200) |

First read data arrives RL*tCK + tDQSCK + tDQSQ after the RD command's
clock edge. There is no DLL, so tDQSCK is an analog delay the
controller must absorb with a trained capture, not a fixed clock count.

## Temperature de-rating

When MR4 indicates the extended-temperature de-rating code, add
1.875 ns to tRCD, tRC, tRAS, tRP (both variants) and tRRD, and use the
de-rated tDQSCK (up to 5620/6000 ps). Clock frequency and setup/hold
timings do not change.

**Source:** JESD209-2F sections 5.1, 5.4-5.5, 5.9, 12.4 (Table 103)

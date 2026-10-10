# Core Timing Parameters

The bank-state timings: what each parameter constrains, and the command
transition it applies to. DDR4 expresses most core timings in clocks per
speed bin (nRCD/nRP track the nominal CL of the bin; see the speed-bin
tables); ns-to-clock conversion is divide by tCK and round up (RU).

## Row-cycle parameters

| Symbol | Definition | Applies between | Value |
| --- | --- | --- | --- |
| tRCD | Row-to-column delay | ACT(bank) -> RD/WR(bank) | nCK per speed bin (10 at DDR4-1600 rising to 24 at DDR4-3200) |
| tRP | Precharge recovery | PRE(bank) -> ACT(bank) | nCK per speed bin, matched to tRCD |
| tRAS | Row-open window | ACT(bank) -> PRE(bank) | 28-52 nCK by speed |
| tRC | Full row cycle | ACT(bank) -> ACT(bank) | 38-76 nCK by speed (= tRAS + tRP) |

## Activate-rate parameters (bank-group aware)

The headline change from DDR3: activate spacing and the four-activate
window come in short/long pairs keyed to whether the two banks share a
bank group.

| Symbol | Definition | Applies between | Value |
| --- | --- | --- | --- |
| tRRD_S | ACT to ACT, different bank groups | ACT(grp a) -> ACT(grp b) | 4 nCK (all bins; x16 parts pay more at high speed) |
| tRRD_L | ACT to ACT, same bank group | ACT(grp a) -> ACT(grp a) | 5-11 nCK by organization and speed |
| tFAW | Four-activate rolling window | any 4 ACTs within a sliding window | 16-48 nCK by organization and speed |

The rolling-window rule is unchanged in shape: if RU(tFAW/tCK) = 16 and
an ACT lands at clock N, at most three more ACTs may land in clocks
N+1 .. N+15. Interleaving ACTs across the two groups keeps every
adjacent pair at tRRD_S; a same-group stream pays tRRD_L per pair and
runs into tFAW sooner.

## Data-to-precharge parameters

| Symbol | Definition | Applies between | Value |
| --- | --- | --- | --- |
| tRTP | Internal analog read must finish before the row closes | internal RD(bank) -> PRE(bank) | max(4 nCK, 7.5 ns) |
| tWR | Write recovery: last write data committed before precharge | last write data(bank) -> PRE(bank) | 15 ns; programmed as nWR in MR0 |
| tWR_CRC_DM | Write recovery with both CRC and DM enabled | as tWR | tWR + max(4-5 nCK, 3.75 ns) |

Command-spacing formulas (same bank):

| Transition | Earliest spacing (clocks) |
| --- | --- |
| RD -> PRE | AL + RU(tRTP) - the spec states the external spacing as AL + tRTP, with tRAS also satisfied |
| WR -> PRE | WL + BL/2 + RU(tWR) |
| RDA -> ACT | RU(tRP) after the auto-precharge begins (AL + BL/2 + RU(tRTP) after the RDA, delayed to tRAS), and >= tRC |
| WRA -> ACT | WL + BL/2 + nWR + RU(tRP), and >= tRC |

## Why these numbers dominate

tRCD and tRP remain the row-miss penalty. The new lever is grouping:
tRRD_L and tCCD_L make same-group traffic strictly more expensive than
cross-group traffic, so the scheduler's real job is to spread column and
activate traffic across bank groups - flat-bank DDR3 scheduling
heuristics (round-robin the banks) silently become same-group-penalized
on DDR4 unless the bank-to-group map is part of the policy.

**Source:** JESD79-4D sections 4.19, 4.22-4.24, 11.1 (Table 154), 13 (AC tables)

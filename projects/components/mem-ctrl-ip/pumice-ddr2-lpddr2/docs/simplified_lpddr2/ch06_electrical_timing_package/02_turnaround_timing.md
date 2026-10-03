# Turnaround and Burst Timing

Turnaround parameters govern the shared DQ bus when direction or burst
changes. LPDDR2 has no ODT and no DLL, so these are contention and
analog-settling rules, expressed as formulas over RL, WL, BL and
tDQSCK rather than as a single named constant per transition.

## Burst-to-burst spacing

| Symbol | Definition | Applies between | Min |
| --- | --- | --- | --- |
| tCCD | Column-to-column command spacing | RD -> RD, or WR -> WR (any banks) | S4: 2 tCK; S2: 1 tCK |

Interruption rules: on S4 a BL4 burst may never be interrupted; with
BL8/BL16 a RD may interrupt a RD and a WR may interrupt a WR only on
even clock cycles after the first command, tCCD met. On S2 bursts may
be interrupted whenever tCCD is met. RD <-> WR interruption is not
allowed in either class; use BST first if a burst must be cut short.

## Write-to-read turnaround

| Symbol | Definition | Applies between | Min |
| --- | --- | --- | --- |
| tWTR | Internal write-to-read delay | end of WR burst data -> RD | 7.5 ns (1066-533) / 10 ns (466-200), min 2 tCK |

The schedulable form, from the WR command to the RD command:

```
WR -> RD  >=  WL + 1 + BL/2 + RU(tWTR/tCK)   clocks
```

(BL is the effective burst length if the write was truncated by BST.)

## Read-to-write turnaround

JESD209-2F gives the read-to-write rule as a formula without assigning it
a symbol. This book calls it tRTW because the other specifications in
this series name that parameter, and a common symbol set keeps the
timing tables comparable across books.

| Symbol | Definition | Applies between | Min |
| --- | --- | --- | --- |
| tRTW | Read-to-write turnaround (book symbol; the spec gives the rule unnamed, as a formula) | RD(any bank) -> WR(any bank) | RL + RU(tDQSCKmax/tCK) + BL/2 + 1 - WL clocks |

The terms, in words: wait out the read latency and the (possibly
multi-clock) strobe access time, let the burst finish and one bubble
clock pass, then credit back the write latency because write data is
timed from the WR command itself. With RL=3, WL=1, BL=4,
RU(tDQSCKmax/tCK)=2: 7 clocks.

## Burst terminate

BST truncates the most recent RD or WR. Effective burst length after
BST = 2 x (clocks from RD/WR to BST), and that effective BL feeds every
formula above. Issue window: up to BL/2 - 1 clocks after the RD/WR on
S4; any cycle after the command on S2. The truncation lands one full
RL (reads) or WL (writes) later.

## MRR placement

The mode-register read is a BL4 read-like operation on the DQ bus, so
it obeys the same spacing: no earlier than BL/2 after a RD, and no
earlier than WL + 1 + BL/2 + RU(tWTR/tCK) after a WR. MRR to a
following write: RL + RU(tDQSCKmax/tCK) + 4/2 + 1 - WL clocks.

## Example gap sheet (RL=3, WL=1, BL=4, S4, 3 ns tCK)

| Transition | Gap (clocks) |
| --- | --- |
| RD -> RD | 2 (tCCD) |
| WR -> WR | 2 (tCCD) |
| RD -> WR | 7 |
| WR -> RD | 1 + 1 + 2 + 3 = 7 (RU(7.5/3) = 3) |
| RD -> PRE (same bank) | BL/2 - 2 = 0 clocks + tRTP 7.5 ns analog |
| WR -> PRE (same bank) | end of data + tWR 15 ns |

**Source:** JESD209-2F sections 5.3-5.6, 5.9.1-5.9.2, 5.12, 12.4
(Table 103)

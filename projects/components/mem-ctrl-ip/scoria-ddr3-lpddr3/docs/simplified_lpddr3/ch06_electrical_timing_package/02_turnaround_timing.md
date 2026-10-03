# Turnaround and Burst Timing

Column-command spacing and bus-direction rules. These decide how full the
DQ bus can be kept.

## Latencies and CAS-to-CAS

LPDDR3 has no DLL and no additive latency: read and write latency are
programmed directly (MR0 OP6/OP7 select the WL set and the optional
RL=3/WL=1 low-latency pair) and the latencies scale with clock speed.

| Symbol | Definition | Applies between | Value |
| --- | --- | --- | --- |
| tCCD | Column command to column command, same or different banks | RD/WR -> RD/WR (same direction) | 4 clocks |
| RL | Read latency: command to first data | RD -> first DQS/DQ out | programmed: 3-16 clocks by rate (6/8/9/10/11/12/14/16 at 800-2133 MT/s) |
| WL | Write latency: command to first strobe | WR -> first DQS in | programmed set A: 1/3/4/5/6/8; set B (optional): up to 13 |

BL8 occupies 4 clocks of DQ. Seamless same-direction traffic issues a
column command every BL/2 = 4 clocks, which is exactly tCCD - back-to-back
BL8 bursts just saturate the bus. There is no burst chop: BL8 is the only
burst length, and no interleaved burst type exists.

## Direction changes

Note on tRTW: JESD209-3C never names the read-to-write parameter (the
symbol does not appear in the spec). It does specify the spacing, and the
spacing depends on tDQSCK because without a DLL the read strobe can lag
the clock by more than a clock. This book calls the parameter tRTW,
matching the other books in this series.

| Symbol | Definition | Applies between | Value |
| --- | --- | --- | --- |
| tRTW | Read-to-write turnaround: the loose read strobe (tDQSCK) plus burst must clear before the write preamble (book symbol; the spec gives the relation unnamed) | RD(any bank) -> WR(any bank) | RL + RU(tDQSCK(MAX)/tCK) + BL/2 + 1 - WL |
| tWTR | Write-to-read: last write data must clear the input path before a read reuses the array | last write data(any) -> RD(any) | max(7.5 ns, 4 nCK) |

Command-spacing forms:

| Transition | Spacing from first command (clocks) |
| --- | --- |
| RD -> WR | RL + RU(tDQSCK(MAX)/tCK) + BL/2 + 1 - WL |
| WR -> RD | WL + 1 + BL/2 + RU(tWTR/tCK) |
| RD -> RD | max(tCCD, BL/2) |
| WR -> WR | max(tCCD, BL/2) |

Worked example (the Chapter 4 configuration: RL = 6, WL = 3, BL8, tWTR =
4 clk, tDQSCK = 2 clk): RD->WR = 6 + 2 + 4 + 1 - 3 = 10 clocks, WR->RD =
3 + 1 + 4 + 4 = 12 clocks. The asymmetry is the write path's long
internal tail; reads turn into writes cheaper than writes turn into
reads. The tDQSCK term is the LPDDR3 signature: a DLL-based DRAM replaces
it with a locked value, an LPDDR3 controller must budget the whole
min/max window.

## Strobe-level timing (for completeness)

These bound the DQS/DQ relationship; the PHY must meet them. With no DLL,
several are wide windows rather than tight skews:

| Symbol | Definition | Value |
| --- | --- | --- |
| tDQSCK | Read DQS access from CK_t/CK_c: a 2.5-5.5 ns window (not a locked skew) | min 2500 ps, max 5500 ps; 5620 ps derated |
| tDQSCKDS/DM/DL | DQSCK drift across 160 ns / 1.6 us / 32 ms rolling windows (guaranteed by design, untested) | 265/593/733 ps max at 1333, shrinking with rate |
| tDQSQ | DQ skew against DQS, per group | 165 ps max at 1333, down to 100 ps at 2133 |
| tQH | DQ/DQS output hold | min(tQSH, tQSL) |
| tDQSS | Write DQS first latching edge to CK | 0.75 to 1.25 tCK (wide - no DLL) |
| tWPRE / tWPST | Write DQS preamble / postamble | 0.8 / 0.4 tCK |
| tRPRE / tRPST | Read DQS preamble / postamble | 0.9 / 0.3 tCK |
| tDS / tDH | Write DQ setup / hold against DQS | 175 ps min at 1333, down to 115 ps at 2133 |
| tDQSH / tDQSL | Write DQS input high/low pulse width | 0.4 tCK |

## Temperature derating

Above the 85 C threshold the core analog timings stretch: tRCD, tRC,
tRAS, tRP and tRRD each carry a +1.875 ns derated minimum, and tDQSCK's
max becomes 5620 ps. A controller that runs hot must add the derating on
top of the programmed values rather than discovering it on the bus.

**Source:** JESD209-3C sections 4.4, 4.5, 11.4 (Table 64)

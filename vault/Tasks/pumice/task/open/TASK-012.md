# TASK-012: REF_STATS_REF free-runs, so axis 3 is estimated rather than measured

**Status:** open 2026-09-25  **Priority:** P2 — characterization accuracy, not
a functional defect; nothing on the board misbehaves because of it

Split out of [[TASK-001]] when that umbrella closed. It was gap 2 of the three
[[TASK-002]]'s first board campaign reported back; gaps 1 (RBL epoch default)
and 3 (config-table confounds) are fixed, this one is not.

## The problem

`REF_STATS_REF` counts refreshes since reset and never stops, so a host-
bracketed delta measures the HOST's UART round trips, not the workload window.
Measured: a 186 us window returned a raw delta of 61446 — 479 ms implied,
**2584x** the window.

The command counters do not have this problem, because nothing issues DRAM
commands while the host is idle. Refresh is the exception precisely because it
is autonomous.

## Current state

Worked around host-side in 71c4fb030: `pumice_char` reports
`window_cycles / tREFI` alongside the raw delta and flags contamination, and
`refs_are_wall_clock()` tells a caller when the number is untrustworthy. That
is enough to stop a wrong number being quoted; it is not enough to measure
axis 3.

## What a fix looks like

A windowed or clearable refresh counter: either a second counter with a
host-writable clear, or a snapshot pair the host can difference atomically.
The other `*_STATS` counters are free-running by design and should stay that
way — this is specifically about the one counter that advances with no
workload.

Until then, **axis 3 (refresh) numbers are estimates.** Any table quoting them
should say so.

Related: [[TASK-002]] (the campaign that found it), [[TASK-001]] (closed
umbrella).

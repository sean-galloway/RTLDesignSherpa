# TASK-036: the tRTW model says 14 and the hardware tolerates 3

**Priority:** P2 — not a defect, but a 76% bandwidth difference on a measured
workload sits on the other side of it, and the model that forbids reaching it is
not understood.
**Status:** open 2026-09-29
**Owner:** TBD
**Found by:** [[TASK-034]]'s board campaign, once the failure detector was proven.
**Related:** [[ISSUE-018]] (the likely reason the old empirical guard is no longer
needed), [[TASK-035]] (formal coverage, if the answer turns out to be a logic
argument rather than an electrical one)

## The measurement

Nexys A7, 75 MHz, BL4 x16, ISSUE-018-fixed bitstream. Failure detector PROVEN to
fire (read tap off the levelled eye -> 4000/4000 beats mismatched, clean before
and after). tRTW swept **3 to 20 contiguous**, gap 0 (saturated) and gap 14, six
reps each:

* **Zero mismatched beats at every point.**
* gap 14: 123.2 MB/s at tRTW >= 12, **217.7 MB/s at tRTW <= 11** (+76%).
* gap 0: 285.3 MB/s flat, every tRTW.

Shipping tRTW is 20, derived as
`max(ck(CL + BL/2 + 2 - WL), phy_rd_dq_busy + 1 - t_phy_wrlat + rtw_guard)`
= `max(3, 14 + 6)`.

## The two questions, and they are separable

**1. Why does the empirical `rtw_guard = 6` no longer buy anything?**

Its comment says it covers "the arbiter's registered turnaround ok", and the
board data behind it -- tRTW=18 failing 5 of 6 reps at gap 14, tRTW=20 clean --
does not reproduce at all today. [[ISSUE-018]] repaired exactly that registered
staleness at the source, so the guard is plausibly now compensating for something
that no longer exists. Cheap to confirm: the guard is a host constant, so this is
a sweep, not a rebuild.

**2. Why does `phy_rd_dq_busy + 1 - t_phy_wrlat` = 14 forbid what the hardware
demonstrably tolerates at 3?**

This is the interesting one. That term models the read's DQ occupancy: a write
must not drive DQ while a read is still returning. Yet tRTW=3 -- a write command
three MC cycles after a read -- shows no corruption at all, saturated or gapped.

The likely resolution, and it is testable: **write data reaches DQ far sooner
after its command than read data does.** `t_phy_wrlat` is 1 while a read returns
around `t_rddata_en + rddata_delay` = 13 cycles out. A write issued 3 cycles
after a read therefore puts data on the bus at ~4, long BEFORE the read return at
~13 -- it passes underneath, it does not collide. If that is right, the collision
window is BOUNDED, not one-sided, and the model is wrong in shape rather than in
magnitude: it assumes the write must wait out the read, when a sufficiently early
write is equally safe.

**A bounded window predicts corruption somewhere in the middle, and the scan
found none** -- tRTW 11..20 and 3..10 are all clean. So either the window is
narrower than one MC cycle at this geometry, or the DFI/PHY datapath serializes
the two directions regardless of the CSR. Both are checkable.

## How to settle it

1. **ILA the DQ bus** across a RD->WR turnaround at tRTW = 3, 12 and 20. That
   answers question 2 directly by showing where write data actually lands
   relative to the read return, instead of inferring it. The design has an ILA
   build (`ddr2_char_ila.bit`).
2. If the datapath does serialize the directions, then tRTW is a PERFORMANCE
   knob on this design and not a correctness one, and the derivation should say
   so rather than deriving a floor it does not need.
3. Re-derive `rtw_guard` against question 1 independently -- it is a host
   constant and needs no rebuild.
4. Only then consider lowering tRTW toward 11. **Do not lower it on the strength
   of the sweep alone**: absence of corruption in two workloads is not a proof
   that the DQ bus cannot collide, and this is the failure mode that produces
   marginal silicon rather than failing tests.

## Why it is worth someone's time

+76% on the gap-14 concurrent workload, against a 600 MB/s theoretical peak, from
a single CSR. And the answer is likely to be a correction to a derivation that
currently constrains every read-to-write turnaround on the part.

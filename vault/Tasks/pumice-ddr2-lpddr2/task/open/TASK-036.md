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

---

## ILA campaign 2026-09-29 -- the DFI boundary is the wrong observation point

Built the ILA bitstream (17 probes, depth 4096, WNS 0.000) and captured the
RD->WR turnaround at tRTW = 3, 12 and 20 under the saturated 1+1 concurrent
workload. The historical `ila_pumice037_wrdata_into_read.csv` is the calibration
throughout: it is what a real collision looks like.

### The answer to the question as filed

**Write data DOES still overlap the read return at tRTW = 3.** Arming the ILA on
the conjunction itself -- `wrdata_en != 0 AND rddata_valid != 0`, the exact
PUMICE-037 signature -- FIRES at tRTW = 3, with three overlapping samples.

So the derivation's floor is NOT what keeps write data off the read return. The
hypothesis this task was filed to test -- that something separates them which the
model does not describe -- is **refuted**. Nothing separates them. They overlap,
at a tRTW of 3, exactly as the model warns.

**And it does not corrupt.** Mismatch count on that capture: zero.

| capture | wrdata_en | rddata_valid | overlap | mismatch |
|---|---:|---:|---:|---:|
| HISTORIC (PUMICE-037) | 96 | 1006 | **49** | **89** |
| tRTW=3, overlap-armed | 1201 | 893 | **3** | **0** |

Same signature, opposite outcome. That is the finding.

### Why, and it is the reason this measurement could not settle it

`w_dfi_rddata_valid` is the **DFI-boundary** valid: it is asserted after the PHY
has already captured the data off the DQ pins and is presenting it upstream. An
overlap at that boundary therefore does NOT mean the write is contending with the
read on the physical wires -- the read may be long since captured. The DFI
boundary is where this design's marked nets are, and it is one layer too high to
answer a DQ-contention question.

That also explains the historical capture without contradicting it: back then the
overlap coincided with corruption because the write was driving DQ early enough
to disturb the actual capture window; today the same DFI-boundary overlap is
benign because it is not the same physical event.

**What that means for lowering tRTW: do not.** At tRTW = 3 this design is
relying on a DFI-boundary overlap being harmless, which is a property of PHY
timing nobody has measured, and which demonstrably has NOT always held on this
exact board. "Benign in two workloads" is a much weaker statement than "cannot
collide", and this is the failure mode that produces marginal silicon.

### The honest state of the three sub-questions

1. **Is the empirical `rtw_guard = 6` still needed?** Still unknown. The
   historical failure does not reproduce, but the workloads available here do not
   reproduce the historical STIMULUS either -- see below.
2. **Why does the model say 14 when hardware tolerates 3?** Partly answered: the
   model is about DQ-pin contention and the available observation point is the
   DFI boundary, which is not the same thing. It is not that the model is wrong;
   it is that this measurement cannot see what the model is about.
3. **Is the +76% reachable?** Unchanged and still worth chasing, but not on this
   evidence.

### The stimulus gap, measured rather than asserted

The two captures are structurally different in a way that matters:

| capture | write bursts | read-return bursts | shape |
|---|---:|---:|---|
| HISTORIC | 96 | 152 | fine-grained interleave, single-cycle writes among read returns |
| this campaign | 2 | 2 | two long same-direction phases |

The concurrent 1+1 workload on disjoint banks produces LONG same-direction runs,
so a 4096-sample window contains about two turnarounds. The historical workload
interleaved them densely. **That is why nothing corrupts here and why the
bank_gap sweep found nothing**: the turnaround is barely being exercised, and the
board sweep in [[TASK-034]] inherited the same blindness.

### What would actually settle it

1. **Probe the PHY side, not the DFI side.** Mark the a7ddrphy DQ/DQS drive
   enables and capture those. That is where contention either happens or does
   not, and it is a one-line `mark_debug` plus an ILA rebuild.
2. **Build the interleaving stimulus** -- same-bank alternating RD/WR, which is
   what the historical capture shows and what neither the sweep nor this campaign
   produced. Validate it by reproducing the 96-write-burst / 152-read-burst shape
   before trusting any result from it.
3. Only then sweep the guard.

Steps 1 and 2 are independent and both are small. Neither was done here, and the
task stays open because of it -- but it is now open on a specific, measured
question rather than on a hypothesis.

---

## PHY campaign 2026-09-29 -- the model IS conservative, measured at the right layer

The ILA campaign above ended at the DFI boundary, which is post-capture and
therefore cannot answer a DQ-contention question. Built a second ILA that adds
the PHY's tristate controls (`fpga/tcl/build_ila_phy.tcl`, 22 probes, WNS 0.006):

    probe13  u_a7ddrphy/a7ddrphy_dq_oe_delay_tappeddelayline_tappeddelayline
    probe16  u_a7ddrphy/a7ddrphy_dqs_oe_delay_tappeddelayline_tappeddelayline

`dq_oe` is the DQ tristate control -- it is asserted exactly when the FPGA is
DRIVING the wires. Marked on the SYNTHESIZED NETLIST rather than in the RTL,
because `a7ddrphy_generated.v` is generated and a hand-edit would vanish at the
next regen.

### The measurement, at tRTW = 3

| capture | dq_oe | rddata_en | rddata_valid | COINCIDENT | closest separation |
|---|---:|---:|---:|---:|---:|
| PHY, tRTW=3 | 1120 | 818 | 810 | **0** | **28 cycles** |

**The FPGA never drives DQ while a read is in its data window, and stays 28
cycles clear of it -- at a tRTW of 3.**

### The instrument is proven, which is what makes the silence mean something

A trigger that cannot fire proves nothing, so each probe was armed alone first:

    mode=dqonly   -> FIRED        (CSV in ~2 s)
    mode=rdonly   -> FIRED        (CSV in ~2 s)
    mode=contend  -> never fired  (no capture in 180 s)

Both probes demonstrably work; only their conjunction is silent. The `rdonly`
capture is the decisive one because it contains BOTH signals in one window --
1120 dq_oe samples and 818 rddata_en samples, zero coincident.

### What this settles

**Question 2 is answered: the model is conservative, and now by how much.**
`rd_window_mc = phy_rd_dq_busy + 1 - t_phy_wrlat` = 14 models the write waiting
out the read's DQ occupancy. The PHY already separates them by 28 cycles at
tRTW=3, so that term is guarding against contention the datapath structurally
prevents. On this design tRTW is a COMMAND-SCHEDULING knob -- which is why it
moves bandwidth in the sparse regime -- not a DQ-collision guard.

**It also explains the DFI-boundary result** rather than contradicting it. The
overlap seen there at tRTW=3 was real but harmless because `dfi_rddata_valid` is
asserted after the PHY has captured off DQ; the wires were free 28 cycles
earlier. Two layers, two different events, and only one of them is contention.

### What is still NOT established, and it is the same gap as before

1. **One traffic pattern.** 1+1 concurrent, gap 0, `banks` placement. The 28
   cycles is what THAT pattern produces. A different interleave could close it.
2. **The historical interleave is still not reproduced.** `placement='same_bank'`
   was the obvious lever and is not one: it produces bandwidth identical to
   `banks` to within 0.1 MB/s at every tRTW and gap. Nor is generator count --
   4+4 gives 275 MB/s against 1+1's 285, LOWER, and both tRTW-invariant. So the
   dense RD/WR mixing in `ila_pumice037_wrdata_into_read.csv` (96 write bursts
   among 152 read returns, against 2 and 2 here) came from a configuration this
   campaign has not identified.
3. Concurrent read+write is bounded at ~47% of peak by the controller, not by
   the stimulus -- which is why tRTW is irrelevant at gap 0 and dominant at
   gap 14.

### Recommendation

The evidence is now strong enough to justify lowering tRTW **as a measured
change with board validation**, not as a config edit: the contention the floor
guards against does not occur, with 28 cycles of margin, on a proven instrument.
It is NOT strong enough to lower it blind, because point 2 means the worst-case
interleave has not been exercised.

Concrete next step, and it is small: find what produces the historical
interleave (start with the `*_batching` and `*_interleave` captures already in
`reports/`, which have the shape), reproduce it, confirm the 28-cycle margin
under it, and only then reduce `rtw_guard`.

Board restored: production bitstream, tRTW = 20, leveling re-verified.

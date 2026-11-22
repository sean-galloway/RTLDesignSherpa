# ISSUE-001: onyx's observer puts per-transaction classes on the low-bandwidth MonBus with no class knob; on the board the tally bins are lower bounds

**Priority:** P3
**Status:** closed 2026-11-22 (onyx TASK-001 step 6c)
**Owner:** TBD
**Filed:** 2026-11-22 (onyx TASK-001 step 6b)

## Observed

On the Genesys2 reference rig (`REF_CACHE_SEL` 4 and 5, bin 2 builds with the
pair block's MonBus tally chain), the `monbus_tally_axil` bins for onyx's
event classes fall far short of the exact counters in every cell with a
sustained event rate, while the resident and warm-up cells agree exactly:

| cell (dual sweep) | transactions (counter) | `TXN_START` (bin 11) | `MEM_READ` counter / bin | drop-report packets (bin 17) |
|---|---|---|---|---|
| `r4k_we0` depth 1 | 16 | 16 | 16 / 16 | 0 |
| `r16k_we64` depth 1 | 381 | 265 | 381 / 266 | 2 |
| `r64k_we64` depth 1 | 20,240 | 12,613 | 20,240 / 12,603 | 2 |
| `r64k_we64` depth 16 | 20,240 | 3,891 | 20,239 / 3,888 | 2 |
| `r128k_we64` depth 16 | 30,083 | 5,360 | 30,072 / 5,359 | 2 |

Results: `perf_sweep_onyx_bin2_dual_20261122T151054Z.json` and the three
companions (`ref/results/`). In simulation the same observer loses 0 to 9
events per full-regression cell and reports every one (the pair-rig TB
holds it to that); on the board the observer's holders overflow for the
whole run.

## Why

The MonBus is a low-bandwidth event channel by intent
(`vault/handbook/design/monbus-is-a-low-bandwidth-channel.md`, written from
this case on 2026-11-22): it carries rare events, and every per-transaction
class a monitor can emit is a knob that floods it under sustained traffic.
The pair block's channel (`monbus_arbiter`, 3 clients ->
`monbus_axil4_group_1wr` -> `monbus_tally_axil`) drains one AXI-Lite write
per packet word, several cycles a packet, shared by the two caches'
observers and onyx's; on `r64k_we64` depth 1 it delivers about 0.17 onyx
packets a cycle. onyx's observer emits four per-transaction classes
(`TXN_START`, `GATHER_DONE`, `MEM_READ`, `READ_WASTED`, about four events a
transaction at a transaction every three cycles per injector) and, unlike
the ocelus monitors, has no per-class enable mask: every class is always
on. The saturation is the channel doing what it is for; the deviation from
the house design is the missing knob. The drop-and-count idiom (inherited
from the caches' observers) is itself low-bandwidth: the report is emitted
only when nothing is waiting and its payload is 8 bits, so two reports a
cell stand for thousands of lost events and say "lost", not "how many".

## What is not affected

The six exact counters (`onyx_counters`, harness CSR 0x020-0x034) are the
D6 measurement and are unaffected: they agree with the pair-rig model in
sim and with each other on the board (reads wasted == lines supplied in
parallel mode; memory reads fall by exactly lines supplied in deferred
mode; zero wasted). All 220 bin 2 cells reproduce their bin 1 cycle counts,
so the chain costs no cycle.

## Resolves into

(a) Done 2026-11-22: the handbook note above records the rule and this
case; the HAS (ch04/04, ch06/02) and the reference comparison say the bins
are lower bounds on the board and the counters are the measurement. Raising
the channel's rate so a per-transaction stream fits is NOT a remedy: it is
against the channel's design.

(b) Open, onyx's: give `onyx_monlite` the per-class enable mask the ocelus
monitors carry (`cfg_*_pkt_mask` convention, bit set drops the class),
reset so the per-transaction classes are off and the rare ones
(`LOCK_WAIT`, the drop report) stay on; the pair-rig TB then checks the
masked classes emit nothing and the unmasked ones still meet their
counters; the reference rig's harness CSR carries the mask so the host can
open one class at a time for shape-in-time reads. Owner's call whether this
lands in TASK-001 or waits for the D1 work.

(c) Open, monitor area, not onyx's: the drop-and-count idiom's report
(wider saturating payload, or a periodic report under sustained loss) is
shared with the caches' observers and belongs with the monitors if taken.

## Resolution (2026-11-22)

(a) and (b) done the same day, in onyx TASK-001 step 6c. The handbook
note records the rule; `onyx_monlite` carries the ocelus mask layers
(observer, packet type, event class, error code, port), dropped at the
source, reset on the reference rig to the rare class only
(`ONYX_MON_CTRL` 0x038 / `ONYX_MON_MASK` 0x03C, reset `0x007D0007`), and
the sweep opens classes by name (`--onyx-mon-classes`). On the board,
MEM_READ alone equals its counter in 39 of 55 dual cells and in every
cell at depth 1 and 2 (`r64k_we64` depth 1: 20,240 = 20,240 where the
all-open bin read 12,603); the 16 short cells are the thrash cells at
depth 4 to 16, where the channel is still shared with the two caches'
unmasked observers, each with a drop report; the masked classes' bins are
zero in all 55. (c), the drop-report idiom, stays with the monitor area and
is not reopened here: with the layers set, the report is what it was
designed to be, a rare event.

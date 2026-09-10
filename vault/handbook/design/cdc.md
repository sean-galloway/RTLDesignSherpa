---
title: Clock-domain crossing
summary: Sync every crossing; Gray-code pointers; handshakes for events. Johnson is opt-in, never a default.
---

# CDC

- Never sample a foreign-domain signal raw. Multi-bit quasi-static data:
  `glitch_free_n_dff_arn` (3 flops typ). Single-cycle events: `sync_pulse`.
  Req/ack transactions: `cdc_2_phase_handshake` / `cdc_4_phase_handshake`.
  Open-loop rate crossing: `cdc_open_loop`. All in `rtl/cdc/`.
- FIFO pointers cross domains Gray-coded: `bin2gray` -> sync flops ->
  `gray2bin`. **Register the Gray value in the source domain before it
  crosses.** `bin2gray` is combinational, so on a multi-bit binary transition
  (`0111` -> `1000`) its output can momentarily show a code that is neither the
  old value nor the new one; sampling that transient defeats the point of Gray
  coding entirely. `counter_bingray` exists to do exactly this — binary count
  and registered Gray count out of one `always_ff` — and is what the async
  FIFOs instantiate. Use it rather than assembling the pair yourself.
- These modules live in `rtl/cdc/`, not `rtl/common/` and not `rtl/amba/`.
  Everything that crosses a clock domain was consolidated there; a doc or
  comment still saying otherwise is stale.

## USE_JOHNSON: hoist it, default it to 0

**Whenever `gaxi_fifo_async` is instantiated, bring `USE_JOHNSON` up to the
instantiating module's parameter list and default it to 0.** Not left to the
FIFO's own default, not hardcoded at the instantiation, not hidden behind an
auto-select.

Two independent reasons:

- **Gray must be the default, and Johnson a conscious choice.** Johnson
  pointers are `DEPTH` bits wide against Gray's `$clog2(DEPTH)+1` — and that
  width is duplicated per domain and again per synchronizer stage. At depth 32
  that is 32-bit pointers where Gray needs 6. Nobody should pay that without
  having decided to.
- **A non-power-of-2 depth should fail loudly, not silently cost flops.** With
  the default at 0, a bad depth trips `gaxi_fifo_async`'s elaboration `$error`
  and the designer picks deliberately. With an auto-select default, the same
  mistake elaborates quietly and the cost only shows up in the flop count.

The parameter must still be *reachable*: expose it so a caller who genuinely
needs an odd depth can pass 1. The rule is about the default and the visibility,
not about removing the capability.

*Applied 2026-07-27 across `rtl/`: `apb4_slave_cdc`, `apb4_slave_cdc_cg`,
`apb5_slave_cdc_cg` and both testcode multi-wrappers had no `USE_JOHNSON`
parameter at all; `apb5_slave_cdc` defaulted to `-1` (auto-select);
`gaxi_fifo_async_multi` hardcoded `1` and defaulted `DEPTH` to 10, so Johnson
was forced on and invisible. `gaxi_skid_buffer_async` already complied.*

- Async FIFO depth: powers of 2 under Gray (pointer wrap correctness). Johnson
  accepts **any** depth, odd included — "even only" is stale language from the
  retired `fifo_async_div2` and it took four review rounds to clear out of the
  docs. See `docs/markdown/rtl-cdc/cdc.md` for the depth-36 ASIC case study.
- The full-flag lag is `N_FLOP_CROSS + 1` write clocks, not `N_FLOP_CROSS` —
  the synchronizer stages plus the registered flag in `fifo_control`. Size the
  margin accordingly.
- One-sided resets are NOT safe on these FIFOs. The crossed pointer copy is a
  live synchronizer that re-converges within two clocks of deassertion, leaving
  the reset side at pointer 0 against an advanced remote pointer: the write
  side alone swallows entries, the read side alone replays them. Quiesce the
  bus first.
- In XDC: async clock groups for unrelated clocks. But see
  [[timing-closure]] - a giant negative WNS is usually NOT a missing clock
  group; check clock interaction before touching constraints.

Related: [[signal-prefixes]], [[reset-and-clocking]], [[sizing-invariants]].

## A handshake across independently reset domains: four-phase, and never a one-sided cancel

Two rules from the rtc time-set commit (issue #56, 2026-09-09), each learned
from a review finding after the fix looked done.

*Rule 1: if the two domains can be reset independently, the transfer must be
a four-phase request/acknowledge, not a two-phase toggle.* A toggle stores
its state as parity, and parity cannot survive a reset on one side: the
first rtc fix used `cdc_2_phase_handshake`, and a pclk-only reset then
fabricated a commit of all-zero data (day 0, month 0, `time_valid` set),
while an rtc_resetn-only reset replayed the last commit into the freshly
reset counters. `docs/markdown/rtl-cdc/cdc.md` already states this rule; the
fix was written without reading it.

*Rule 2: a transfer that has timed out cannot be cancelled from one side.*
The second rtc fix reset only the source of the four-phase on timeout, to
"withdraw the request so a late-returning clock cannot deliver it". It made
two new defects. The destination's copy of the request was already inside its
synchronizer and the reset had zeroed the data-hold register, so when the
clock returned the destination delivered zeros. And the destination's
acknowledge is a level that only its own reset clears, so the source's next
request completed against the stale acknowledge in one cycle and was never
delivered at all. The honest design leaves the transfer pending with its data
held, reports the timeout as "not acknowledged within the window; verify by
reading back", and lets it land whenever the far clock returns. Cancelling
needs both sides to agree, which is another handshake.

*Rule 3: the source of a cross-domain handshake is reset by the FAR domain's
reset, never by the near (bus) reset alone.* The third rtc review found the
same zero-delivery through `presetn`: a bus-only reset cleared the source's
data hold while the request was already inside the destination's
synchronizer, and the destination then loaded zeros. Feed the source's reset
port with the far reset synchronized into the near domain (`reset_sync`,
async assert, sync deassert) and nothing else; the near reset clears the
near-side bookkeeping (pending/busy) but not the transfer. A bus-only reset
then leaves an in-flight commit to land intact, and a far-only reset resets
both ends so the link is idle, which is what "the domains reset
independently" has to mean. ("Reset when both are asserted" is the same
thing said badly: written as an AND of active-low signals it resets on
either, which is the defect.)

*Rule 4: every flop that tracks the handshake's state must share the
handshake's reset.* The fourth rtc review found the pending/busy flags and
the timeout edge detector still on the bus reset after the source side had
moved to the far reset. Two flops in one clock domain under different resets
is a reset-domain crossing: a commit staged while the far domain was in
reset hung busy forever (the primitive holds ready low, so nothing ever
completed or timed out) and then loaded on release, undoing the reset; and
an edge detector whose two flops reset on different signals manufactures an
edge at release. Reset the bookkeeping with the OR of the near reset and the
synchronized far reset, the same term the source side uses.

*Rule 4, second half: the COMPLETION EVIDENCE shares that reset too.* The
fifth rtc review found the bookkeeping correctly on the far reset while the
snapshot pulse synchronizer that tells it "the load happened" still reset
its destination side on the bus reset. A toggle synchronizer with one side
reset is parity: a bus reset covering the load either destroyed the pulse
(busy stuck forever, register file presenting reset defaults with
time_valid=0) or fabricated one (the pre-commit time published as the
commit's answer). Every synchronizer whose output clears or sets a
bookkeeping flop is part of that bookkeeping and takes its reset.

*Rule 5: a block that keeps state across a bus reset must not let the reset
defaults of its register file cross into the kept domain.* An RTC keeps
counting through `presetn`; but `rtc_enable` and `clock_select` live in the
register file, reset to 0, and cross into the counter domain as levels, so a
bus reset stopped the clock (a stale time with time_valid=1 after the reboot)
and flipped the clock mux under a running domain. Cross the configuration
together with a config-valid flag that every RTC_CONFIG write sets and
`presetn` clears; the kept domain applies the crossed values only while the
flag is set and otherwise holds its last state. Hold the clock-source select
in a flop on the far reset for the same reason.

*Rule 6: hold only quasi-static configuration; a transient control crosses
live.* The same RTC latched `time_set_mode` into the configuration hold.
It is a transient (software sets it, stages six bytes, clears it), so a
`presetn` in the middle of that sequence cleared the register file's copy
and the config-valid flag but not the hold's copy, and the divider stayed
pinned at zero until software happened to write RTC_CONFIG again. The
kept domain takes a transient from the synchronized crossing, masked by the
crossed valid bit for the held copy, so the far side's reset clears it at
the source and the pause releases on its own.

*Rule 7: the valid bit crosses inside the bundle, behind the full
synchronizer, and nothing consumes the first stage.* A valid flag that
crosses in its own synchronizer resolves independently of the data it
qualifies, so one destination clock can see valid=1 against the pre-write
values; the first RTC_CONFIG write after a bus reset presented rtc_enable=0
for a clock and zeroed the divider mid-second. Put the valid bit in the
bundle and accept a word only when two consecutive samples of the FULL
synchronizer output agree (a transition is caught by at most one sample).
The fix as first landed shortened the chain to one flop "so the capture
register is the second" and used that stage-1 output in the compare, the
hold's data and a live control into the divider: a metastable stage-1 bit
can read as equal to the comparator and as the other value at the hold's
D input in the same cycle, so the filter proves nothing there. Depth is
the house SYNC_STAGES on every crossing in the module; a test that needs
the crossing one clock faster is the thing to fix.

*How to check the fix:* the acceptance tests for a crossing must include a
reset of each side alone with a transfer in flight, and a stop-then-restart
of the far clock with the request already inside the destination's
synchronizer. Tests that reset both sides together, or stop the clock before
the request is issued, pass on both broken designs.

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

*Applied 2026-07-27 across `rtl/`: `apb_slave_cdc`, `apb_slave_cdc_cg`,
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

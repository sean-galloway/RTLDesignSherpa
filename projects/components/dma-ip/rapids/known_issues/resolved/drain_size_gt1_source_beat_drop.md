<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

## DRAIN_SIZE > 1 drops SOURCE beats (short delivery + CRC mismatch)

**Status**: RESOLVED 2026-09-26 in bdf4e0dff (verified at DRAIN_SIZE 1, 2, 4 and 8)

### Description

With `AXI_XFER_CONFIG.DRAIN_SIZE > 1`, the SOURCE path delivers **fewer beats than
requested** to the AXIS egress, then reports the channel idle. The checker sees a
short beat count and a CRC mismatch against the golden model.

Reproduced in the RAPIDS beats characterization harness (`rapids_char_harness`)
with a multi-channel source transfer:

- Config: `RD_XFER_BEATS=8, WR_XFER_BEATS=8, ALLOC_SIZE=16, DRAIN_SIZE=8`,
  4 active channels x 512 beats/channel (2048 total).
- Observed: `o_chk_beat_count_total = 1844` (expected 2048); `ch0/ch2/ch3`
  SOURCE CRC mismatch (`chk != golden`); `src_system_idle = 1` (DUT believes the
  transfer completed). The external egress bus meter corroborates: `sout`
  productive beats froze at 1844.
- With `DRAIN_SIZE=1` the same transfer delivers all 2048 beats, golden-clean.

Roughly ~10% of beats are dropped; the loss is not a clean multiple of
`DRAIN_SIZE`, so this is not a simple final-partial-chunk fencepost.

### Location

Source drain path: `rtl/macro_beats/src_data_path_axis_beats.sv` /
`src_sram_controller*` drain-control + `beats_drain_ctrl`. The drain granularity
(`cfg_drain_size`) governs how many beats are released per drain operation; a
value > 1 loses beats near buffer/transfer boundaries.

### Impact

- SOURCE data loss whenever `DRAIN_SIZE > 1`. SINK path was not observed to drop
  (its `DRAIN_SIZE=8` sim run completed), but should be re-verified.
- No impact at the shipped/characterization setting: both the cocotb harness TB
  (`rapids_char_harness_tb`) and the board campaign (`run_characterization.py`)
  use `DRAIN_SIZE=1`.

### Workaround

Use `DRAIN_SIZE=1` (current default in all RAPIDS char collateral). This does
**not** cost utilization: a `DRAIN_SIZE=8` A/B in sim showed identical AXI/AXIS
utilization, so there is no throughput reason to raise it until the drain-path
boundary handling is fixed.

### Next Steps

1. Trace `beats_drain_ctrl` / `src_sram_controller` drain accounting at
   `DRAIN_SIZE>1` around SRAM wrap and end-of-transfer.
2. Add a directed DV test sweeping `DRAIN_SIZE ∈ {1,2,4,8}` x non-aligned
   transfer sizes to pin the boundary condition.
3. Re-verify the SINK drain path at `DRAIN_SIZE>1`.

### Discovered

2026-07-14, during RAPIDS beats external bus-meter characterization (Nexys A7).

---

## Mechanism identified (2026-09-25)

Established by building the RAPIDS signal-contract workbook for this target
(`docs/gen_rapids_signal_contracts_kmaps.py`, sheet "K-maps src drain",
TASK-002 item 3). Every line below is a verified citation -- the generator
fails loudly if any of them moves.

**The drain path has two independent readers of one FIFO, and nothing
reconciles them.**

1. A block RESERVATION: `drain_req` / `drain_size` go to `drain_ctrl_beats` as
   `rd_valid` / `rd_size` (`src_sram_controller_unit_beats.sv:157-158`). That
   controller advances its read pointer by the FULL `rd_size` in one cycle,
   gated only on `!r_rd_empty` -- a bare not-empty test, not a test that
   `rd_size` entries are present (`drain_ctrl_beats.sv:101-102`, `:142`, and
   the module's own comment at `:156`).
2. A per-beat POP: `drain_valid` / `drain_ready` through the latency bridge
   (`src_data_path_axis_beats.sv:229`).

**The qualifying comparison uses an inflated view.** The arbiter grants on
`drain_data_avail[check_ch] >= cfg_drain_size` (`src_data_path_axis_beats.sv:197`)
and commits `r_drain_remaining <= cfg_drain_size` (`:200`). But
`drain_data_avail` is built as

```systemverilog
assign drain_data_avail = drain_data_available + SCW'(bridge_occupancy);
```

(`src_sram_controller_unit_beats.sv:229`). A beat that has moved out of the
FIFO into the latency bridge's skid is STILL counted in `drain_data_available`
-- that counter's read pointer moves only on a RESERVATION, never on the FIFO
read port -- so adding `bridge_occupancy` counts it a second time. The
over-count is 0..4 (`latency_bridge_beats.sv:185`) and is largest exactly when
the FIFO runs near-empty with the bridge holding its prefetch.

So the arbiter can see `avail >= cfg_drain_size` when the drain controller
holds less than that, reserve the full size anyway, and `!r_rd_empty` still
passes -- `rd_ptr` overshoots `wr_ptr`. At `cfg_drain_size == 1` the
`!r_rd_empty` gate absorbs the entire discrepancy, which is exactly why
`DRAIN_SIZE=1` is clean and is the shipped workaround.

**A second, compounding term.** `w_arb_should_advance`
(`src_data_path_axis_beats.sv:180-182`) lets the arbiter abandon a grant
mid-block when the channel's view reads empty, while `r_drain_remaining` is
still non-zero. The reservation already advanced the pointer by the full
`cfg_drain_size`, so beats between what was reserved and what was actually
moved are skipped. This is why the shortfall is **not** a clean multiple of
`DRAIN_SIZE`, which the original report correctly flagged as not a simple
fencepost. Note also that the `r_drain_remaining` decrement sits in the ELSE of
that condition (`:204`), so on an advancing cycle a beat can leave without
being counted against the block.

### This is a STREAM defect that RAPIDS inherited and STREAM already fixed

STREAM carried the identical line. It is present at `13607ca07` (2025-11-11)
and `fcfac0be0` (2025-11-24) as
`assign wr_drain_data_avail = drain_data_available + SCW'(bridge_occupancy);`.
RAPIDS-beats was forked from STREAM at `3c308050b` (2026-01-11) and inherited
it verbatim, at the same relative position.

STREAM removed it in `e8908eebf` (2026-07-21), replacing it with
`assign axi_wr_drain_data_avail = drain_data_available;` plus a 26-line
prohibition (`stream/rtl/fub/sram_controller_unit.sv:282-307`) that describes
this exact failure -- including that the corruption is PERMANENT (both pointers
then advance in lockstep, the channel reports a nearly-full FIFO forever) and
that it manifested as a deadlock freezing all 8 channels.

That fix was never back-ported. Two things made it easy to miss: it landed
inside a commit labelled `chore(components): convert component filelists to -f`,
and it landed 2026-07-21 -- one week AFTER this bug was found on the Nexys A7
(2026-07-14), so the two were never connected.

STREAM also guards it a second time on the caller side with
`w_effective_avail` = registered avail minus in-flight drains
(`stream/rtl/fub/axi_write_engine.sv:387`, applied at `:427`). RAPIDS has no
equivalent: `src_data_path_axis_beats.sv:197` compares the raw view directly.

### The SINK path has the identical defect

The original report left this open ("SINK path ... should be re-verified").
It is the same line, unfixed:
`snk_sram_controller_unit_beats.sv:229`. Both source and sink instantiate the
same `drain_ctrl_beats` and the same `latency_bridge_beats`. The sink not
having been observed to drop is an absence of evidence -- its `DRAIN_SIZE=8`
run completing does not clear it.

### Candidate fix

One line per path, matching what STREAM already ships:

```systemverilog
// src_sram_controller_unit_beats.sv:229  and  snk_sram_controller_unit_beats.sv:229
assign drain_data_avail = drain_data_available;   // NOT + bridge_occupancy
```

Excluding reserved-but-not-yet-transmitted beats is conservative in the safe
direction -- it can only delay a drain, never over-issue one. Whether the
abandonment term (`:180-182`) also needs work should be judged after this is
in, since the inflated view is what drives the channel's avail to zero
mid-block in the first place.

**Not applied here** -- this entry records the mechanism; the RTL change is the
owner's call.

### Cheapest confirmation available

`drain_ctrl_beats.sv:176` already contains a `$error` for exactly this
condition (`rd_size > data_available`), inside `translate_off`. No
`DRAIN_SIZE>1` config is checked into RAPIDS collateral and no over-drain
report exists in the tree, but this issue records a `DRAIN_SIZE=8` A/B run in
sim. Re-running that A/B and grepping the log for `over-drain` would confirm
or refute the whole mechanism without touching RTL.


---

## Resolved 2026-09-26 -- bdf4e0dff

`beat_conservation` now measures **0 beats lost at cfg_drain_size 1, 2, 4 and 8**
(9/9 cells at each size, 0 over-drain `$error`). The `DRAIN_SIZE=1` workaround is
no longer needed.

### The candidate fix above was necessary but NOT sufficient

This entry proposed a one-line change (`drain_data_avail = drain_data_available`,
without `bridge_occupancy`) and left the RTL to the owner. That line is correct
and is now in place -- RAPIDS wraps STREAM's `sram_controller`, whose unit exposes
`data_available` only -- but applying it **alone made things worse**, measured:
at `cfg_drain_size == 1` the source path went from 84-in/84-out to losing 24 of
84 beats. Three mechanisms were in play, and all three had to be fixed:

1. **The `bridge_occupancy` double-count** -- this entry's mechanism, correct.

2. **A registered-valid dry window.** STREAM's SRAM *registers* `drain_valid` for
   timing closure. RAPIDS' src previously had neither the register nor the
   combinational tap, so it was self-consistent; taking STREAM's SRAM without
   also taking the tap let the unit pop a beat while `m_axis_tvalid` was
   suppressed -- consumed, never transmitted. STREAM documents this exact failure
   at `stream/rtl/fub/axi_write_engine.sv:694-702`. Fixed by gating
   `m_axis_tvalid` on the registered **and** combinational valid.

3. **Stale-availability over-reservation.** `drain_data_avail` is registered at
   the SRAM boundary, so a reservation fired this cycle is not yet reflected in
   the view the arbiter sizes against. The arbiter over-reserved;
   `drain_ctrl_beats` then **silently dropped** the excess `rd_ptr` advance
   (gated `!r_rd_empty` at `drain_ctrl_beats.sv:101` -- no `$error`, which is why
   the over-drain check never fired), and the surplus beats were orphaned at the
   latency-bridge output where `drain_data_avail` can no longer see them. Fixed
   by porting STREAM's in-flight-reservation compensation
   (`axi_write_engine.sv:366-410`): arbitrate and size reservations on
   `w_effective_avail` = availability minus reservations still in flight.

The arbiter also moved to STREAM's consumer model -- take a grant once, reserve
`min(cfg_drain_size, avail)`, pulse `drain_req` for exactly one cycle
(`drain_ctrl_beats` has no edge detect), drain that many beats, retire on the
last, and never re-consult availability mid-drain. The old FSM abandoned a live
grant on `drain_data_avail[grant] == 0`, which at `cfg_drain_size == 1` fired on
the first accepted beat, so it dropped and re-arbitrated every beat.

`cfg_drain_size` is honoured as a **threshold**: grant once that many beats are
available, or drain a short final batch when nothing further is coming for the
channel. That final-partial path is what the `DRAIN_SIZE=8` result exercises --
with 7 beats per descriptor the threshold is never reached, so every beat leaves
via that clause.

### Loss trajectory, measured at cfg_drain_size == 1 (84 beats in)

| tree state | beats lost |
|---|---|
| HEAD (before any change) | 0 |
| wrapper alone | 15..65 |
| + dry-window valid gate | 13..47 |
| + STREAM consumer model | 7..28 |
| + in-flight compensation | **0** |

### Other evidence

- full src datapath suite 63/63 (all 7 testcases 9/9), snk 54/54
- both SRAM macro tests 15/15 after the filelist change altered their closure
- the same 27 egress cells measured against HEAD are also 27/27, so this restores
  HEAD's behaviour rather than merely improving on the broken intermediates

### Still open, and unaffected by this

The SINK AXIS ingress defect candidate is separate and untouched:
`s_axis_tready` can assert while the channel FIFO backpressures, because the
`fill_alloc_req` term carries no `fill_ready` conjunct
(`snk_data_path_axis_beats.sv:204-205`). That is a different path from this issue
and remains open.

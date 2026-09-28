# TASK-027: the four axi4 *_mon_cg formal proofs

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-090** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** P3. **Status:** CLOSED 2026-09-11 -- all four written, proved
and mutation-tested.

`axi4_master_rd_mon_cg`, `axi4_master_wr_mon_cg`, `axi4_slave_rd_mon_cg` and
`axi4_slave_wr_mon_cg` were the only AXI4 wrappers with no proof at all. Each
directory held nothing but a `KNOWN_LIMITATION.md` claiming the proof was
blocked by a multi-driver issue in `axi_monitor_trans_mgr` and by two
clock-gating bugs in the wrapper. All three were fixed long ago; the pages
outlived the block and have been deleted.

**It was far smaller than the page implied.** The page said the harness would
have to carry the monitor's whole config and monbus port set on top of the
AXI channels. It does not have to be written: the non-gated `*_mon` proofs
already carry it. The port delta from `*_mon` to `*_mon_cg` is FOUR ports --
`cfg_cg_enable`, `cfg_cg_idle_count`, `cg_gating`, `cg_idle` -- with
`debug_block_ready` dropped. Each harness is its `*_mon` sibling plus those
four, the gate properties, and a clock-enable `icg` model.

**Flow.** sv2v flatten (the direct flow cannot read the monitor's
package-typed ports), with `rtl/common/icg.sv` deliberately left out of the
closure so the harness can model the gated clock as the free clock -- the
same arrangement as `formal/amba/wb4_slave_cdc_cg`. `clock_gate_ctrl`
instantiates `icg` (line 277), so that model is load-bearing, not decorative.

**Properties**, per task: reset leaves no gating; every request-side ready is
masked to zero while gated; never gated with `cfg_cg_enable` low; bounded
wake (two registered stages, so gating may survive two clocks of activity but
not three -- the shape TASK-091 corrected on the APB masters); and
`ap_no_gate_while_active`, the bug-hunt property, since `|active_transactions`
is a term in the wrapper's `user_valid` and dropping it would let a monitor
be gated with transactions in flight.

**Verified, not just green.** 11-12 assertions and 6 covers each; all six
covers reached by name in every task, including `cp_gating` and
`cp_gated_with_req`, so the gated-state properties are not vacuous. Five
mutations, each failing its own named property: dropping
`|active_transactions` fails `ap_no_gate_while_active`; unmasking a gated
ready fails `ap_gated_<port>_zero` on all four wrappers. Every mutation was
restored by absolute path and verified byte-identical with a clean re-prove.

The slave wrappers name their upstream side `s_axi_*`, not `fub_axi_*`; the
harness generator derives each variant's masked readys and wake valid from
the wrapper's own assigns rather than assuming the master naming.

---

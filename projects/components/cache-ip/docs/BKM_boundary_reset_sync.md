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

<!-- End Header -->

# BKM — Boundary Reset Synchronization for Cache-IP Tops

**Version:** 1.0 (2026-10-14)
**Status:** BKM (best-known method). DECIDED 2026-10-14 (sean): amber_top
and amber_ace_top carry the reference implementation (commit `003773645`);
jet, onyx, and basalt adopt this BKM at their boundary when they come up.

## Requirement

Every cache-ip top-level block (`amber_top`, `amber_ace_top`, `jet_*_top`,
`onyx_*_top`, `basalt_*_top`) shall synchronize its reset input at the
boundary before any internal logic sees it:

- Instantiate the house `reset_sync` (`rtl/cdc/reset_sync.sv`, formally
  proven) with `N=3`, `ASYNC_ASSERT=1`, both polarities active-low.
- Every internal block consumes the synchronized net (`w_aresetn`), never
  the port.
- The top's filelist pulls the closure via
  `-f $REPO_ROOT/rtl/cdc/filelists/reset_sync.f`.
- The port is documented as *async assert, any-quality deassert* in the
  module header and in the block's MAS clocks-and-reset section.

## Rationale

The integrator's deassert quality cannot be trusted: board-level resets
come from pushbuttons, PLL lock logic, and power managers, released
asynchronously and with unknown skew across the die. A single sync point
at the IP boundary converts that untrusted input into a clean,
synchronous release for all internal state — async assert is preserved end
to end. An upstream board top (e.g. the Genesys2 `r_rst_sync` chain) may
hold its own synchronizer; cascading is harmless and adds only N cycles of
release latency.

This BKM came out of the amber Genesys2 bring-up (2026-10), where reset
hygiene was audited while chasing silicon-only wedges. The boundary sync
is **not** a fix for runtime state corruption (droop/SEU); it protects the
boot boundary so the design always starts from a known, consistent state
before any traffic arrives.

## What does NOT get a synchronizer

- **Sub-IP cores consumed by a top** (e.g. `l1_core` inside amber) — the
  boundary belongs at the integration surface. Per-FUB sync would add
  latency per consumer and fragment the reset tree.
- **Downstream FUBs** — one sync per top, distributed by net.
- **Multi-clock logic** — this BKM covers single-clock tops; per-domain
  reset distribution inside a multi-clock IP is a separate concern.

## Reference implementation (amber, 2026-10-14)

`amber_top.sv` / `amber_ace_top.sv`, commit `003773645`:

```systemverilog
logic w_aresetn;
reset_sync #(
    .N(3), .KEEP_ATTRS(1'b1),
    .IN_ACTIVE_LOW(1'b1), .OUT_ACTIVE_LOW(1'b1),
    .ASYNC_ASSERT(1'b1)
) u_reset_sync (
    .clk(aclk), .rst_n(aresetn), .sync_rst_n(w_aresetn)
);
```

All internal taps repoint to `w_aresetn`; the port appears only on the
synchronizer. Verification: directed test
`amber-mesi-l1/dv/tests/test_amber_top_reset_sync.py`, full DV grid
275/275, G2 harness cosim clean, MAS ch01/03 updated.

## Verification recipe (per top)

Reuse the amber directed-test pattern; do not invent a new one:

1. **Pin a small geometry** so the post-reset observable is short.
2. **Deassert aresetn mid-cycle** (async, off every clock boundary) and
   count clocks to a reset-release-gated observable — amber uses init-walk
   completion (`init_busy` fall; the control FSM resets into its init
   state, so the walk is the first post-release event). Assert completion
   `>= measured_unsynced + N`. Measure the unsynced baseline first by
   watching the test fail; the bound encodes exactly `+N`.
3. **Functional smoke**: after the observable, present a request mid-cycle
   — ready must respond combinationally while idle and the request must be
   consumed at the next edge.
4. **Async-assert guard**: assert reset mid-cycle (even mid-transaction)
   and require the init state to re-enter without waiting for a clock
   edge.

If a future top has no init walk, substitute any output that transitions a
bounded number of cycles after reset release.

## Rollout

| Block | Status | Notes |
|-------|--------|-------|
| `amber_top` | Done (2026-10-14, `003773645`) | reference implementation + directed test + MAS note |
| `amber_ace_top` | Done (2026-10-14, `003773645`) | twin, identical pattern |
| `jet-mesi-l1` top | Pending | apply at first RTL landing |
| `onyx-ace-ccu` top | Pending | apply at first RTL landing |
| `basalt-moesi-l2` top | Pending | apply at first RTL landing |

---

**Last Updated:** 2026-10-14

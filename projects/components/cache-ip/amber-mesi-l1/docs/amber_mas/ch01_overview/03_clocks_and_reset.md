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

# Clocks and Reset

## Clock Domains

| Clock | Frequency | Usage |
|-------|-----------|-------|
| `aclk` | 50–200 MHz | Primary — all amber logic, AXI4/ACE/GAXI interfaces, MonBus |

: Table 1.3.1: Clock domains

amber is a single-clock IP. The GAXI slave, AXI4/ACE masters, snoop responder, and MonBus all run on `aclk`.

## Reset

| Signal | Polarity | Type | Usage |
|--------|----------|------|-------|
| `aresetn` | Active-low | Async assert, **synchronized internally** | Primary reset input for all amber logic and memories |

: Table 1.3.2: Reset signals

`aresetn` is an asynchronous-assert input whose deassertion quality is
not trusted: `amber_top` runs it through the house `reset_sync`
(`rtl/cdc`, N=3, `ASYNC_REG`) before any internal block sees it — as does
`amber_ace_top`, the ACE-rig twin — so
integrators may deassert it at any phase — including asynchronously or
mid-cycle — and the release the core sees is synchronous. Assertion
remains asynchronous end to end. The Genesys2 pair-rig top carries its
own synchronizer upstream; cascading is harmless (adds N cycles of
release latency).

`aresetn` resets all flops. The `sdpram_core` instances inside `l1_tag_array` and `l1_data_array` are not reset; their contents are invalidated by clearing valid bits or by the first access after reset, depending on the implementation choice recorded in Chapter 2.3.

All sequential logic uses the house `ALWAYS_FF_RST` macro with `RST_ASSERTED` on the synchronized internal reset. This is the same pattern used in the AMBA wrappers and STREAM.

The internal synchronization is verified by the directed test
`dv/tests/test_amber_top_reset_sync.py`: an asynchronous (mid-cycle)
deassert must delay the post-reset init walk by exactly N cycles, and a
mid-cycle assertion must re-enter the init state without waiting for a
clock edge.

---

**Last Updated:** 2026-10-14

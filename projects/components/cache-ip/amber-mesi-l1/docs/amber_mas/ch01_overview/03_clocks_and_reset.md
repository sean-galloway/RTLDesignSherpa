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
| `aresetn` | Active-low | Async assert, sync deassert | Primary reset for all amber logic and memories |

: Table 1.3.2: Reset signals

`aresetn` resets all flops. The `sdpram_core` instances inside `amber_tag_array` and `amber_data_array` are not reset; their contents are invalidated by clearing valid bits or by the first access after reset, depending on the implementation choice recorded in Chapter 2.3.

All sequential logic uses the house `ALWAYS_FF_RST` macro with `RST_ASSERTED(aresetn)`. This is the same pattern used in the AMBA wrappers and STREAM.

---

**Last Updated:** 2026-10-06

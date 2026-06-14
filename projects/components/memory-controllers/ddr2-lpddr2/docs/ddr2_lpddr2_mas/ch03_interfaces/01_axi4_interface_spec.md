<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> &middot; <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# AXI4 Slave Protocol

**Status:** Skeleton — to be authored during MAS week


The AXI4 slave port carries host requests into the controller.

## Scope of This Section

This section is the **wire-level** AXI4 contract specific to this controller — what's supported, what's relaxed, what's omitted. It is not an AXI4 tutorial; refer to ARM IHI 0022 for the full protocol.

## Supported Features (v1)

- AW/W/B/AR/R 5-channel handshake
- INCR burst type (mandatory)
- ID-aware OoO completion (when `AXI_OOO_ACROSS_IDS = true`)
- 64 / 128 / 256-bit data widths
- 1–16-bit ID widths
- Per-ID in-order completion

## Optional Features (build-time)

- FIXED burst (`SUPPORT_FIXED_BURST`)
- WRAP burst (`SUPPORT_WRAP_BURST`)

## Unsupported Features

- AXI exclusive accesses
- AXI4 user signals (no `USER_*` widths)
- AXI4 cache-coherent extensions

## TODO

- Per-channel timing diagrams (wavedrom)
- Backpressure semantics in detail
- Response-ordering examples for OoO-across-IDs
- Burst-boundary corner cases (4 KB boundary, address-alignment)


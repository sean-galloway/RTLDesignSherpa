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

# What Moved to Common (Phase-2 extraction)

On 2026-10-09 → 2026-10-10 the shared logic of the three research controllers —
pumice (DDR2/LPDDR2), scoria (DDR3/LPDDR3), andesite (DDR4/LPDDR4) — was
extracted into `mem-ctrl-ip/common-ip/`, and pumice was re-integrated onto it
the same weekend. This chapter records what moved, what stayed, and where
each is documented now. The family architecture the extraction implements —
the layer stack and the descriptor seam — is owned by the family HAS
([common_has](../../../../../common-ip/docs/common_has/common_has_index.md));
this chapter is pumice's delta against it, and it is the only place in this
book that tells the move story.

## What pumice consumes from common-ip

pumice_core instantiates four common blocks directly:

| Common block | Role in pumice | Microarchitecture |
|---|---|---|
| `mc_axi4_layer` | AXI4 slave intakes, burst chop/split, coalescing, read-return ring | [common_mas ch02](../../../../../common-ip/docs/common_mas/ch02_axi4_layer/01_mc_axi4_layer.md) |
| `mc_storage_layer` | rd/wr CAMs, read snooping, bank image | [common_mas ch03](../../../../../common-ip/docs/common_mas/ch03_storage_layer/01_mc_storage_layer.md) |
| `mc_scheduler_layer` | pick machinery, timers, generic maintenance slot (inside the `pumice_scheduler_layer` wrapper) | [common_mas ch04](../../../../../common-ip/docs/common_mas/ch04_scheduler_layer/01_mc_scheduler_layer.md) |
| `mc_dfi_2p1_layer` | DFI 2.1 command/data pipeline + the single aclk↔dfi_clk CDC | [common_mas ch07](../../../../../common-ip/docs/common_mas/ch07_dfi_2p1_layer/01_mc_dfi_2p1_layer.md) |

The package is the family's `mc_common_pkg`; `pumice_pkg` remains and
re-exports it (the shipping-CSR widening argument for not migrating the
package itself is unchanged — see the family package design).

## What stayed pumice-side

Everything generation-specific stayed, by the family's two-customer rule:
the init sequencer, mode register, refresh controller, page-policy engine,
power-down controller, the DFI command formatter/signal pack, ZQ calibration
(`pumice_zq_ctrl`), DQ calibration (`pumice_lp_cal`), and the local
`addr_mapper` (the common `mc_addr_mapper` is extracted but pumice has not
switched to it; adoption is scheduled with the scoria/andesite wrapper
thinning). Two thin wrappers hold the rock-specific wiring:
`pumice_scheduler_layer` (rock scheduler children + training-channel mapping
onto the common maintenance slot) and `pumice_training_layer` (ZQ + DQ cal
behind the common training shell).

## What this book does with the moved blocks

Chapters whose subject moved carry a **"lives in common-ip now"** banner
under their header, pointing at the owning common_mas chapter; their pumice
provenance and measured history are kept — that history is invariant, and
the numbers in it (bandwidth, timing margins, bug regressions) are pumice's
own measurements, not the common block's. Chapters whose subject stayed are
unaffected except where names changed.

## The measured record survives the move

The Phase-2 re-integration was gated on pumice's full suite passing on the
common stack (top/FUB/macro/phy, SEED=12345) and on the Nexys A7 timing
closures being re-established at 66.67 MHz and 75 MHz after the
`rd_crc_check` popcount fix. Those numbers — and every pre-extraction
measurement in this book — describe pumice as it runs today; the extraction
changed where the logic lives, not what it does.

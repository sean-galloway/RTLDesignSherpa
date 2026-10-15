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
the plane stack and the descriptor seam — is owned by the family HAS
([common_has](../../../../../common-ip/docs/common_has/common_has_index.md));
this chapter is pumice's delta against it, and it is the only place in this
book that tells the move story.

## What pumice consumes from common-ip

pumice_core instantiates six common planes directly, and every leaf FUB beneath them is common-ip as well:

| Common block | Role in pumice | Microarchitecture |
|---|---|---|
| `mc_axi4_plane` | AXI4 slave intakes, burst chop/split, coalescing, read-return ring | [common_mas ch02](../../../../../common-ip/docs/common_mas/ch02_axi4_plane/01_mc_axi4_plane.md) |
| `mc_storage_plane` | rd/wr CAMs, read snooping, bank image | [common_mas ch03](../../../../../common-ip/docs/common_mas/ch03_storage_plane/01_mc_storage_plane.md) |
| `mc_init_plane` | JEDEC init sequencing, mode-register shadow + CL/CWL/BL decode, DFI PHY init handshake, `init_state_o` telemetry (extracted from the scheduler plane 2026-10-15; granite instantiates the identical plane) | [common_mas ch10](../../../../../common-ip/docs/common_mas/ch10_init_plane/01_mc_init_plane.md) |
| `mc_scheduler_plane` | pick machinery, timers, generic maintenance slot, in external-init mode (`HAS_INIT_SEQUENCER=0`, `HAS_MODE_REGISTER=0`), plus its DDR2/LPDDR2 children `mc_xddr2_refresh_ctrl` and `mc_page_policy` | [common_mas ch04](../../../../../common-ip/docs/common_mas/ch04_scheduler_plane/01_mc_scheduler_plane.md) |
| `mc_training_plane` | LPDDR2 ZQ (`mc_lpddr2_zq_ctrl`) and DQ calibration (`mc_lpddr2_dq_cal`) behind the two-slot arbiter and `mc_training_shell` CDC | [common_mas ch05](../../../../../common-ip/docs/common_mas/ch05_training_plane/01_mc_training_plane.md) |
| `mc_dfi_2p1_plane` | DFI 2.1 command/data pipeline (`mc_xddr2_cmd_formatter` inside `mc_dfi_cmd_path`) + the single aclk↔dfi_clk CDC | [common_mas ch07](../../../../../common-ip/docs/common_mas/ch07_dfi_2p1_plane/01_mc_dfi_2p1_plane.md) |

The package is the family's `mc_common_pkg`; `pumice_pkg` remains and
re-exports it (the shipping-CSR widening argument for not migrating the
package itself is unchanged — see the family package design).

## What stayed pumice-side

At the 2026-10-10 extraction everything generation-specific stayed, by the
family's two-customer rule: the init sequencer, mode register, refresh
controller, page-policy engine, power-down controller, the DFI command
formatter and signal pack, ZQ calibration (`pumice_zq_ctrl`), DQ calibration
(`pumice_lp_cal`), and a local `addr_mapper`, held together by two thin
wrappers, `pumice_scheduler_plane` and `pumice_training_plane`.

That state lasted one day. On 2026-10-11 the DDR2/LPDDR2 children moved into
common-ip as the `xddr2` / `lpddr2` generation FUBs (`mc_xddr2_init_sequencer`,
`mc_xddr2_mode_register`, `mc_xddr2_refresh_ctrl`, `mc_xddr2_cmd_formatter`,
`mc_page_policy`, `mc_lpddr2_zq_ctrl`, `mc_lpddr2_dq_cal`), the common planes
gained `HAS_*` parameters to compose them, and both wrappers were removed.
`powerdown_ctrl`, `dfi_signal_pack`, and the unused local `addr_mapper` were
removed outright. What stays pumice-side now is only the tops
(`pumice_top_geared`, `pumice_top`, `pumice_core`), `pumice_pkg`, the
`pumice_csr` register description, and the parameter choices on the common
planes ([FUB Breakdown](05_fub_breakdown.md)).

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

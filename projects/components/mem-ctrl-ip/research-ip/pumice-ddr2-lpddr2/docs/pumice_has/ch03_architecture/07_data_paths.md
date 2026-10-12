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

# Write and Read Data Paths

The write/read data path in pumice is the common storage plane, `mc_storage_plane`, instantiated in `pumice_core` between `mc_axi4_plane` and the scheduler. It holds the write-data CAM (write buffer plus snarf source) and the read-command CAM (read scheduling window), presents the scheduler-facing bank/row/col image, and accepts the read-snoop probe from the upstream AXI4 plane. The descriptor seam it exposes to the scheduler is the same contract documented in the family architecture specification ([`common_has` chapter 2](../../../../../common-ip/docs/common_has/ch02_architecture/02_descriptor_seam.md)); the plane's internals are documented in the family microarchitecture specification ([`common_mas` chapter 3](../../../../../common-ip/docs/common_mas/ch03_storage_plane/01_mc_storage_plane.md)).

Until 2026-10-09 these CAMs lived in the pumice-local `pumice_axi4_plane` as `pumice_wr_data_cam` and `pumice_rd_cmd_cam`; they were extracted into `mc_storage_plane` during the Phase-2 common-stack campaign.

## What pumice consumes from the common stack

`mc_storage_plane` provides:

- `mc_wr_data_cam` — the write-command/write-data CAM with fill, commit-drain, and snarf (read-your-write) movers;
- `mc_rd_cmd_cam` — the read-command scheduling window;
- read snooping (snarf) against unscheduled writes;
- per-entry scheduling vectors (validity, bank, row, column, age, age-order matrix, QoS) across the descriptor seam.

Pumice instantiates the plane with `AXI_BEATS_PER_BURST = BURST_WORDS` and wires it to the pumice-local scheduler. Legacy `oldest_*` and `sched_lu_*` CAM ports are tied off inside `mc_storage_plane`.

## What remains pumice-specific

### Observed status registers

`pumice_top` captures storage-plane-adjacent telemetry from the scheduler and training plane into the CSR. Observable registers relevant to the data path include:

- `PAGE_STATS_HIT` — every column command issued (READ/WRITE, with or without AP); this is a lower-bound hit count, not a true hit count (do not derive hits as `PAGE_STATS_HIT - SCHED_STATS_ACT`; see pumice ISSUE-014);
- `PAGE_STATS_MISS`, `PAGE_STATS_EMPTY` — page-state counters;
- `OBS_ROW_HIT[0..7]` — per-bank row-hit counts (the only sound row-hit count; pumice BUG-020);
- `SCHED_STATS_ACT`, `SCHED_STATS_PRE` — activate/precharge counts;
- `REF_STATS_REF`, `REF_STATS_REF_BUSY` — refresh commands issued and refresh commands that deferred useful work (TASK-012);
- `STALL_BP`, `STALL_REFRESH`, `STALL_TURNAROUND`, `STALL_TCCD`, `STALL_ACTLIMIT`, `STALL_BANKTIMER`, `STALL_NOREQ` — scheduler stall attribution.

These counters are free-running and clear only on `aresetn`; software brackets a workload and reads deltas.

### DFI-side data movement

The controller-side CAMs are only half of the end-to-end data path. The DFI-side write serialization and read alignment are delegated to the common `mc_dfi_2p1_plane` ([`common_mas` chapter 7](../../../../../common-ip/docs/common_mas/ch07_dfi_2p1_plane/01_mc_dfi_2p1_plane.md)); the pumice-local `mc_dfi_wr_serializer` and `mc_dfi_rd_aligner` blocks are no longer instantiated in the active build. Pumice passes runtime PHY timing offsets (`t_phy_wrlat`, `t_rddata_en`) and DFI phase selects (`rd_phase`, `wr_phase`) from the `PHY_TIMING` and `DFI_PHASE` CSRs into that plane.

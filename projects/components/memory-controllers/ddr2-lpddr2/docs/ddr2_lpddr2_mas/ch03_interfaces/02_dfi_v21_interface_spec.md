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

# DFI v2.1 Master Protocol

> Per HAS §2.4 §2 for the full per-phase signal list and HAS §3.6 for the architectural view. This chapter is the wire-level contract specific to this controller — what's driven, what's tied, what's sampled, what's deferred.
>
> For the FUBs that implement this interface, see §2.14 (`cmd_encoder`), §2.15 (`gear_dfi`), §2.16 (`odt_ctrl`), §2.17 (`wr_data_path`), §2.18 (`rd_data_path`).

---

## DFI Spec Reference

Canonical: DFI 2.1 specification (Denali cleartext copy at `/home/seang/github/cold_storage/MemorySpecs/`). The controller's implementation deliberately covers the subset of DFI 2.1 sub-interfaces needed for DDR2/LPDDR2 operation; higher-version sub-interfaces are not driven.

## Sub-Interface Support Summary

| Sub-Interface       | Direction       | Supported in v1? | Notes                                                 |
|---------------------|-----------------|------------------|-------------------------------------------------------|
| Command             | Controller → PHY | Yes              | Per-phase, see HAS §2.4 §2                            |
| Write-Data          | Controller → PHY | Yes              | `WRPHASE` slot per MC cycle                            |
| Read-Data           | PHY → Controller | Yes              | `RDPHASE` slot capture                                 |
| Status              | PHY → Controller | Yes (limited)    | `dfi_init_complete` only                              |
| Update              | Bidirectional   | Yes              | `ctrlupd_*` and `phyupd_*` per spec                    |
| Training            | Bidirectional   | No               | Not required for DDR2/LPDDR2 v2.1; deferred           |
| Frequency Change    | Bidirectional   | No               | No use case in v1                                      |
| Low-Power           | Controller → PHY | No               | CKE is used directly; no PHY-side coordination needed |
| Error               | PHY → Controller | No (placeholder) | `dfi_error` is sampled but ignored in v1               |
| CRC                 | Both             | No               | Not in DDR2/LPDDR2                                     |

## Command Sub-Interface

### Phase Topology

Per HAS §2.4 §2, the command bus is replicated `N_PHASES` times. Per HAS §3.6 and MAS §2.15, phase 0 always carries the actual command; phases 1..N-1 drive NOP-equivalent idle.

### Per-Rank Chip-Select

`dfi_cs_n[NP][NR]` is two-dimensionally indexed in SystemVerilog — `NP` outer (phase), `NR` inner (rank). Concretely at `N_PHASES=4, NUM_RANKS=2`:

```systemverilog
output logic [3:0][1:0] dfi_cs_n;   // [phase][rank]
```

The controller drives exactly one rank's CS_n low per single-rank command, except for init-time REF (which broadcasts) and DDR2 multi-rank REFab (which uses round-robin per HAS §3.4 v0.2). See §2.14 for the per-rank drive logic.

### DDR2 Strobes in LPDDR2 Builds

`dfi_ras_n`, `dfi_cas_n`, `dfi_we_n` are present in the port list in all builds (per HAS §2.4 — same top-level port set for both memtypes). In LPDDR2 builds they tie high; the PHY ignores them.

## Write-Data Sub-Interface

The controller drives `dfi_wrdata_en` exactly `tCWL` PHY cycles after the corresponding WR/WRA command. CWL alignment is handled by `wr_data_path_fub` (§2.17) via its CWL-align shift register — the FUB does not need to know the absolute PHY cycle.

### Per-Phase Mask

`dfi_wrdata_mask[p]` is wide enough to address each byte lane of `dfi_wrdata[p]`. A mask bit of 1 means "do not write this byte" (per DFI convention, matches AXI `wstrb = 0`).

### Per-Rank `dfi_wrdata_cs_n`

DFI 2.1 includes a per-rank chip-select on the write-data path. The controller drives it from the same source as the command-side `dfi_cs_n` for the cycle the write data is presented on (i.e., one phase, post-CWL alignment).

## Read-Data Sub-Interface

The controller asserts `dfi_rddata_en` exactly `tCL` PHY cycles after the corresponding RD/RDA command. The PHY's `dfi_rddata` and `dfi_rddata_valid` arrive shortly thereafter; `rd_data_path_fub` (§2.18) captures them through its CL-aware shift register.

### Per-Rank `dfi_rddata_cs_n`

Symmetric to the write side. Drives which rank is being read.

### Read-Data Error Handling

`dfi_rddata` carries no error bit in DFI 2.1. If the PHY indicates a corrupted read, it does so via `dfi_error` (currently sampled but not acted upon) or via `dfi_rddata_valid` not asserting. The controller treats a missing valid as a soft error and propagates `SLVERR` on the corresponding AXI R response.

## Status Sub-Interface

`dfi_init_complete` is the only status signal sampled in v1. It's used by `init_engine_fub` (§2.12) during the cold-boot sequence — the `WAIT_FOR_BIT dfi_init_complete` step polls this until the PHY signals init complete or the timeout fires.

`dfi_dram_clk_disable` is driven during power-down to enable PHY clock gating; this is the PHY-side companion to `dfi_cke`.

## Update Sub-Interface

The controller and PHY can each request a "controller-update" or "phy-update" window. Currently:

- **`dfi_ctrlupd_req`/`dfi_ctrlupd_ack`** — driven by `power_state_fub` (§2.13) at quiet points. The controller request is rare (mostly during init for PHY calibration handoff).
- **`dfi_phyupd_req`/`dfi_phyupd_ack`** — accepted at any quiet point. The controller grants by stalling new traffic until ack is dropped.

The `dfi_phyupd_type` is observed but not currently used to gate behavior.

## CDC Topology

There is **no CDC** in the DFI interface — the controller drives DFI on `mc_clk`, and the PHY is responsible for any CDC to the DRAM clock. This is the canonical DFI architecture and is what `a7ddrphy` (LiteDRAM's Xilinx 7-series PHY) does.

## Pin Tie-Offs

| Pin                          | Tie-off (when applicable)                         |
|------------------------------|---------------------------------------------------|
| `dfi_ras_n`, `dfi_cas_n`, `dfi_we_n` | Tied high in LPDDR2 builds                |
| `dfi_bank` (LPDDR2 builds)   | Tied 0 (bank is in CA bus)                        |
| `dfi_freq_*`                 | Tied (no frequency change support)                |
| `dfi_lp_*`                   | Tied (no low-power sub-interface)                 |

## Open Questions / Future Work

- **`dfi_error` handling.** Currently sampled and ignored. A v2 enhancement would wire it to `irq_overflow` and propagate `SLVERR` on the affected burst.
- **DFI Training Sub-Interface.** Required for DDR3+ at higher data rates. The v1 controller defers this entirely to the PHY (`a7ddrphy` handles its own training at startup, before init).
- **Per-rank `dfi_*_cs_n` width sanity check.** Some PHYs expect `dfi_cs_n` as a flat NR-bit vector per phase, others as a per-phase array. The controller produces the per-phase array form; a wrapper may be needed at the controller↔PHY boundary for specific PHYs.
- **DFI 3+ migration.** When the DDR3-LPDDR3 family controller arrives, sub-interfaces grew from 6 → 14 (per memory `project_dfi_v6_scope_changes.md`). This MAS will need a new dedicated DFI section. Track in DDR3-LPDDR3 MAS, not here.

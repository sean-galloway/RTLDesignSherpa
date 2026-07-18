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

# Family Config Knobs (DDR2 / LPDDR2)

> Per HAS §5.4 for the family-wide config philosophy. This MAS chapter is the **implementation-level** detail for **this controller** specifically: which CSR fields select DDR2-vs-LPDDR2 behavior and which fields are present-but-inert on this generation.
>
> The controller is a two-family design (DDR2 + LPDDR2). The single most important family selector is `PHY_TIMING.memtype` (0 = DDR2, 1 = LPDDR2), which `pumice_top` maps to the core's `memtype_i` and which the init sequencer and DFI command formatter branch on. There is **no** separate family capability vector register; `ID` @ 0xFF0 echoes the build's memtype and phase count.

---

## The Family Selector: `PHY_TIMING.memtype`

| memtype | Family | What it changes                                                                 |
|---------|--------|---------------------------------------------------------------------------------|
| 0       | DDR2   | `init_sequencer` runs the DDR2 MRS/precharge/refresh chain; `dfi_cmd_formatter` drives the DDR2 RAS/CAS/WE command bus |
| 1       | LPDDR2 | `init_sequencer` runs the LPDDR2 MRW chain (MR63/MR10/MR1/MR2/MR3); `dfi_cmd_formatter` packs the JESD209-2F CA-bus word onto `dfi_address` |

`memtype` is set before init and left fixed (see §4.3). DDR2 is the board target; LPDDR2 is the family-reuse path. Both pass the full sim suite.

## Field-by-Field Applicability

Fields below are the real CSR fields in `rtl/macro/pumice_csr.rdl` (see §4.2). "DDR2 / LPDDR2" notes whether the field is meaningful on each family in this build.

### SCHED_TUNING (0x040)

| Field                  | Applicability                                                        |
|------------------------|----------------------------------------------------------------------|
| `lookahead_active`     | Both; scheduler lookahead window (0 disables)                        |
| `force_inorder`        | Both; forces first-ready FIFO ordering                               |
| `happy_enable`         | Both, only meaningful when the HAPPY predictor is synthesized/selected |
| `age_max_runtime`      | Both; anti-starvation AGE_MAX override                               |
| `txn_queue_high_water` | Both; backpressure threshold                                        |
| `lookahead_max_obs`    | RO echo of build-time LOOKAHEAD_DEPTH_MAX                            |

### REFRESH_TUNING (0x048)

| Field                  | Applicability                                                        |
|------------------------|----------------------------------------------------------------------|
| `page_policy_or`       | Both; drives `page_policy_i` (00 build-time, 01 OPEN, 10 CLOSE, 11 HAPPY_HYBRID) |
| `refresh_defer_active` | Both; refresh deferral / batching count                             |
| `zqcs_freq_hz`         | Both; periodic ZQCS interval (DDR2 has no ZQCL, but ZQCS calibration short is JEDEC) |
| `refpb_policy_or`      | **LPDDR2-relevant** (per-bank refresh); DDR2 uses all-bank REFab only |

### ADDR_MAP (0x04C) — family-agnostic

| Field       | Applicability                                                               |
|-------------|-----------------------------------------------------------------------------|
| `bank_lsb`  | Both; the single address-map knob. `= COL_WIDTH` -> ROW_MAJOR; smaller -> interleave. No scheme selector exists. |
| `hash_en`   | Both; enables the bank XOR-hash (the old XOR_HASH "scheme")                  |
| `hash_seed` | Both; XOR-hash seed                                                         |

DDR2/LPDDR2 have no bank groups, so there is no bank-group field. The retired `ADDR_MAP_TUNING` register (with `scheme_or` / `synth_mask_obs` / `xor_seed_runtime`) does not exist; all address mapping is the `ADDR_MAP` register above.

### INIT_TUNING (0x050) / INIT_TIMING0/1 (0x058/0x05C)

| Field                                     | Applicability                                                |
|-------------------------------------------|--------------------------------------------------------------|
| `zq_retries`, `init_timeout_ms`           | Both                                                         |
| `t_init_wait`, `t_dll_wait`               | Both; on LPDDR2 the sequencer reuses `t_init_wait` for tINIT4 and `t_dll_wait` for tZQINIT (see §5.1) |
| `t_mrd_wait`, `t_rp_wait`, `t_rfc_wait`   | DDR2 uses all three; LPDDR2 reuses `t_mrd_wait` for post-MRW (`t_rp_wait`/`t_rfc_wait` are inert on the LPDDR2 chain) |

### PHY_TIMING (0x064)

| Field           | Applicability                                                             |
|-----------------|---------------------------------------------------------------------------|
| `memtype`       | The family selector (above)                                              |
| `t_phy_wrlat`   | Both; WR cmd -> dfi_wrdata_en (0 = a7ddrphy pre-pull)                     |
| `t_rddata_en`   | Both; RD cmd -> dfi_rddata_en window                                     |
| `refresh_burst` | Both; REFs drained per request                                           |

### LPDDR2-only registers

| Register                          | Applicability                                             |
|-----------------------------------|-----------------------------------------------------------|
| `PASR_BANK_MASK_RANK0` (0x030)    | LPDDR2 partial-array self-refresh (MR16); inert on DDR2   |
| `PASR_SEG_MASK_RANK0` (0x034)     | LPDDR2 PASR segment mask; inert on DDR2                    |
| `TEMP_DERATE_RANK0` (0x038)       | LPDDR2 MR4 temperature class (RO); inert on DDR2          |
| `TIMINGS_CL_CWL_WR.tRFCpb`        | LPDDR2 per-bank tRFC; unused by DDR2                      |
| `CTRL.pwr_req_dpd`                | LPDDR2 Deep Power Down request; inert on DDR2             |

## Feature Discovery

There is no `0xFF8` capability vector in this RDL. Software identifies the build via the `ID` register at 0xFF0:

| Bits  | Field       | Meaning                            |
|-------|-------------|------------------------------------|
| 7:0   | `version`   | Build version (0x01)               |
| 15:8  | `memtype`   | Build memtype echo (0 DDR2 / 1 LPDDR2) |
| 23:16 | `n_phases`  | Gear ratio (1 / 2 / 4)             |
| 31:24 | `module_id` | Fixed 0xD2                         |

Note the `ID.memtype` field is a build-time echo (default reflects the DDR2 build); the **runtime** family select is `PHY_TIMING.memtype`, which software programs before init.

## Not Present in This Generation

The following belong to higher DDR/LPDDR generations and have **no** field in this controller's CSR map: fine-granularity refresh (FGR), write-leveling, MPR, CA training, command-bus training (CBT), bank groups, and inline ECC. They were speculative entries in an earlier family registry and are omitted here rather than tied off.

## Open Questions / Future Work

- **Multi-rank family fields.** PASR/temperature registers are declared for rank 0 only; a `NUM_RANKS` loop in the RDL would add `*_RANK{N}`.
- **Capability register.** If a family capability vector proves useful for a generic SoC driver, it can be re-added as an RO register; for now `ID` carries the essentials.
- **DPD power-state path.** `CTRL.pwr_req_dpd` is defined; the LPDDR2 DPD entry/exit datapath is a follow-up (see §5.2).

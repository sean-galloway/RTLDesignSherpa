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

# Family-Wide Config-Bit Applicability

> Per HAS §5.4 for the family-wide config-bit registry, applicability matrix, and capability vector at 0xFF8. This MAS chapter is the **implementation-level** detail for **this controller** specifically.

---

## Implementation Status in This Controller

The HAS-side registry enumerates 25+ bits that span DDR2/3/4 and LPDDR2/3/4 controllers. This controller implements the subset relevant to DDR2/LPDDR2. Bits flagged for higher generations are present in the CSR map at the documented offsets but **read as 0 and silently ignore writes**.

## Bit-by-Bit Implementation Notes (DDR2 / LPDDR2)

### SCHED_TUNING family

| Bit                     | This controller                                              |
|-------------------------|--------------------------------------------------------------|
| `lookahead_active`      | Live; drives `scheduler_fub.cfg_lookahead_active_i` (§2.7)    |
| `force_inorder`         | Live; drives `scheduler_fub.cfg_force_inorder_i`              |
| `happy_enable`          | Live when `PAGE_POLICY == HAPPY_HYBRID`; reads as 0 otherwise (the FUB isn't synthesized) |
| `age_max_runtime`       | Live; clipped to `≤ AGE_MAX` build-time parameter             |
| `txn_queue_high_water`  | Live; drives backpressure threshold                           |
| `lookahead_max_obs`     | RO echo of build-time `LOOKAHEAD_DEPTH_MAX`                   |
| `qos_high_priority`     | **Sampled but no behavior in v1**; reserved for v2 QoS feature |
| `bank_group_balance`    | **Reads as 0**; DDR2/LPDDR2 has no bank groups                |

### REFRESH_TUNING family

| Bit                       | This controller                                                |
|---------------------------|----------------------------------------------------------------|
| `refpb_policy_or`         | Live for LPDDR2 builds; reads as 0 in DDR2 builds (no REFpb)   |
| `page_policy_or`          | Live; drives `scheduler` page-policy fallback                  |
| `refresh_defer_active`    | Live; clipped to `≤ REFRESH_DEFER_MAX` build-time              |
| `zqcs_freq_hz`            | Live; drives periodic ZQCS timer                                |
| `fgr_mode`                | **Reads as 0**; FGR is DDR3+ feature                            |
| `refresh_per_rank`        | Tied to 1 when `NUM_RANKS > 1`; reads as 0 at NR=1              |

### ADDR_MAP_TUNING family

| Bit                       | This controller                                                |
|---------------------------|----------------------------------------------------------------|
| `scheme_or`               | Live; drives `addr_mapper_fub.scheme_active_i` (§2.3)           |
| `synth_mask_obs`          | RO echo of build-time `ADDR_MAP_SCHEMES_SYNTH`                 |
| `bg_field_position`       | **Reads as 0**; bank groups are DDR4+ feature                  |
| `xor_seed_runtime`        | Live when XOR_HASH scheme is synthesized                        |

### INIT_TUNING family

| Bit                       | This controller                                                |
|---------------------------|----------------------------------------------------------------|
| `zq_retries`              | Live; drives `init_engine.cfg_zq_retries_i` (§2.12)             |
| `init_timeout_ms`         | Live; drives per-step timeout                                  |
| `wl_retries`              | **Reads as 0**; write-leveling is DDR3+ feature                |
| `mpr_enable`              | **Reads as 0**; MPR is DDR3+ feature                            |
| `ca_train_enable`         | **Reads as 0**; CA training is LPDDR3+ feature                  |
| `cbt_enable`              | **Reads as 0**; CBT is LPDDR4-only feature                      |

### POWER_TUNING family

| Bit                       | This controller                                                |
|---------------------------|----------------------------------------------------------------|
| `apd_idle_threshold`      | Live; drives `power_state_fub.cfg_apd_idle_threshold_i`         |
| `srf_idle_threshold`      | Live; drives `power_state_fub.cfg_srf_idle_threshold_i`         |
| `dpd_enable`              | Live for LPDDR2 builds; reads as 0 in DDR2 builds              |
| `pasr_active`             | RO; OR over per-rank PASR masks (LPDDR2 only)                   |
| `ckedis_after_sr`         | **Reads as 0**; DDR3+ feature                                   |
| `low_freq_mode`           | **Reads as 0**; DDR3+ feature                                   |

### RANK_TUNING family

| Bit                       | This controller                                                |
|---------------------------|----------------------------------------------------------------|
| `rank_enable_mask`        | Live; drives per-rank scheduler enable                          |
| `odt_rule_or`             | Live; drives `odt_ctrl_fub.cfg_odt_rule_or_i` (§2.16)            |
| `num_ranks_obs`           | RO echo of build-time `NUM_RANKS`                              |
| `cs_assert_cycles`        | Live; drives per-command CS_n hold cycles in `cmd_encoder`      |

### ECC_TUNING family (reserved)

| Bit                       | This controller                                                |
|---------------------------|----------------------------------------------------------------|
| `ecc_enable`              | **Reads as 0**; inline ECC out of scope for v1                  |
| `ecc_correct_mode`        | **Reads as 0**                                                  |

## Capability Vector at 0xFF8 (This Build)

The capability vector advertises what this controller supports:

| Bits  | Field             | Value (DDR2 single-rank build)         | Value (LPDDR2 4-rank build)     |
|-------|-------------------|----------------------------------------|---------------------------------|
| 0     | `cap_happy`       | 1 if `PAGE_POLICY == HAPPY_HYBRID`     | 1 if `PAGE_POLICY == HAPPY_HYBRID` |
| 1     | `cap_bg_balance`  | 0 (DDR2 has no bank groups)            | 0 (LPDDR2 has no bank groups)   |
| 2     | `cap_fgr`         | 0                                       | 0                                |
| 3     | `cap_pasr`        | 0                                       | 1                                |
| 4     | `cap_dpd`         | 0                                       | 1                                |
| 5     | `cap_wl`          | 0                                       | 0                                |
| 6     | `cap_cbt`         | 0                                       | 0                                |
| 7     | `cap_xor_hash`    | 1 if XOR_HASH is in `ADDR_MAP_SCHEMES_SYNTH` | same                       |
| 11:8  | `cap_max_ranks`   | 1                                       | 4                                |
| 15:12 | `cap_n_phases`    | 4 (default)                            | 4                                |
| 19:16 | `cap_memtype`     | 0 (DDR2)                                | 4 (LPDDR2)                       |

Software queries this once at boot to know what to write — writing un-capable bits is silently ignored (reads as 0).

## Soft-N/A Behavior Summary

The "soft-N/A" mechanism — writes to un-capable bits silently ignored, no `pslverr` — is deliberate. It lets the same SoC software (e.g., a Linux kernel driver) write the family-wide config word on any flavor and have the un-applicable bits drop without error. This is the same approach taken by family-wide config registers in commercial controllers.

Exceptions (where `pslverr` IS returned, per §4.1):

- Writes to rank N where `N >= NUM_RANKS` (per-rank registers)
- Writes to address-map scheme not in `ADDR_MAP_SCHEMES_SYNTH`
- Writes to `RANK_TUNING.odt_rule_or` with un-synthesized rule

These are caught at decode time because they reference resources that don't exist at all in the build.

## Open Questions / Future Work

- **`cap_qos`.** v2 QoS feature would add a `cap_qos` bit. Reserve bit 23 of `0xFF8` for it.
- **Capability discovery vs. memory-mapped probe.** Some SoCs prefer to probe memory-mapped capabilities; others trust a single capability word. The current single-word approach is the documented pattern; we keep it.
- **Per-family vs. per-component capability.** Currently the capability vector tells software what THIS controller supports. A finer-grained per-component vector would let software check, e.g., "does the scheduler have a specific feature." Punt — current granularity is sufficient.

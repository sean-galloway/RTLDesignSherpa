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

# Family-Wide Config Bits

This section is the **family-wide config-bit registry** — a catalog of runtime configuration bits used across the DDR2 / LPDDR2, DDR3 / LPDDR3, and DDR4 / LPDDR4 memory controllers. Some bits apply to all generations; some are introduced in one generation and absent in earlier ones; some are *defined* across the family but ignored in flavors where the underlying mechanism does not exist. **That last case is intentional.** Allocating the bit family-wide — even when unused — keeps the CSR map mechanically compatible across controllers and lets software treat the family as a single product line.

## Why a Family-Wide Registry

Each controller in the family has its own CSR map (per §6.3 of each generation's HAS). But the field encodings, bit positions within shared registers, and the *names* are aligned across the family. The intent:

- **Software portability**: a single device driver template understands the bit layout and only needs per-flavor capability checks.
- **Bring-up portability**: bring-up software written for DDR3 should mostly work on DDR2 with the same register reads.
- **Verification portability**: the cocotb test suite's CSR-poke helpers can be reused.
- **Debug consistency**: the same "config dump" script produces a parseable output regardless of which flavor is running.

A bit may be marked **N/A** in a flavor; reads return 0 and writes are ignored (no `pslverr`, just silently ignored — because software portability requires that writing a fully-portable config word does not error on flavors that don't implement every bit).

## Applicability Notation

The Apply column uses this shorthand:

- **all** — applies to every flavor in the family
- **DDR-only** — applies to DDR2/3/4 only; LPDDR variants ignore
- **LP-only** — applies to LPDDR2/3/4 only; DDR variants ignore
- **DDR3+** — applies to DDR3, DDR4, and forward; DDR2 ignores
- **DDR4+** — applies to DDR4 only (introduced for bank groups); earlier ignore
- **LPDDR3+** — LPDDR3 and LPDDR4 only
- **LPDDR4-only** — LPDDR4 only

## SCHED_TUNING (Scheduling Family Bits)

Register block at the same offset (0x040) in every controller. These bits govern the FR-FCFS scheduler's runtime behavior.

| Bit Field             | Width | Apply        | Description                                                                 |
|-----------------------|-------|--------------|-----------------------------------------------------------------------------|
| `lookahead_active`    | 4     | all          | Runtime lookahead window (0 .. build-time MAX). 0 disables lookahead.       |
| `force_inorder`       | 1     | all          | Forces FR-FCFS into first-ready FIFO mode for debug / real-time.            |
| `happy_enable`        | 1     | all          | Runtime kill-switch for the HAPPY page predictor. Reads as 0 in flavors built without HAPPY. |
| `age_max_runtime`     | 8     | all          | Anti-starvation age cap; runtime override of `AGE_MAX`.                     |
| `txn_queue_high_water`| 8     | all          | Backpressure threshold; AXI `awready` deasserts when queue ≥ threshold.     |
| `lookahead_max_obs`   | 4     | all (R only) | Echo of build-time `LOOKAHEAD_DEPTH_MAX`. Software discovery.               |
| `qos_high_priority`   | 1     | all          | When 1, scheduler boosts requests with `awqos`/`arqos` ≥ 8.                 |
| `bank_group_balance`  | 1     | DDR4+        | Round-robin across bank groups in scheduler tie-break (DDR4/LPDDR4 only); N/A elsewhere. |

## REFRESH_TUNING (Refresh Family Bits)

| Bit Field             | Width | Apply       | Description                                                          |
|-----------------------|-------|-------------|----------------------------------------------------------------------|
| `refpb_policy_or`     | 2     | LP-only     | REFpb selection-policy override (LPDDR2/3/4); N/A for DDR-only flavors |
| `page_policy_or`      | 2     | all         | Runtime override for fallback page policy                            |
| `refresh_defer_active`| 4     | all         | Active deferral count (1 .. build-time MAX). 1 = no batching.        |
| `zqcs_freq_hz`        | 16    | all         | Periodic ZQCS interval. 0 = init-only.                              |
| `fgr_mode`            | 2     | DDR3+       | Fine-Granularity Refresh mode (DDR3 1x/2x/4x; DDR4 fixed-rate, on-the-fly). N/A in DDR2. |
| `refresh_per_rank`    | 1     | all         | Force per-rank dispatch even when `NUM_RANKS=1` (debug). Reset = 1 always when multi-rank. |

## ADDR_MAP_TUNING (Address-Mapping Family Bits)

| Bit Field            | Width | Apply       | Description                                                          |
|----------------------|-------|-------------|----------------------------------------------------------------------|
| `scheme_or`          | 2     | all         | Runtime scheme mux (ROW_MAJOR, BANK_INTERLEAVE, XOR_HASH)            |
| `synth_mask_obs`     | 4     | all (R only)| Bitmask of synthesized schemes. Software discovery.                  |
| `bg_field_position`  | 3     | DDR4+       | Bit position of bank-group field in flat address. N/A pre-DDR4.      |
| `xor_seed_runtime`   | 8     | all         | Runtime seed for the XOR_HASH scheme (changes hash without rebuild). |

## INIT_TUNING (Init Family Bits)

| Bit Field            | Width | Apply       | Description                                                          |
|----------------------|-------|-------------|----------------------------------------------------------------------|
| `zq_retries`         | 4     | all         | ZQ calibration retry count (DDR2 uses OCD; LPDDR2 uses MR10 ZQ).     |
| `init_timeout_ms`    | 8     | all         | Per-step init timeout (ms; scaled by `SIM_INIT_SCALE` in sim).       |
| `wl_retries`         | 4     | DDR3+       | Write-leveling retry count. N/A in DDR2 (no write-leveling).         |
| `mpr_enable`         | 1     | DDR3+       | Multi-Purpose Register read-back during init. N/A pre-DDR3.          |
| `ca_train_enable`    | 1     | LPDDR3+     | LPDDR3/4 CA-bus training. N/A in LPDDR2 (no CA training).            |
| `cbt_enable`         | 1     | LPDDR4-only | Command-Bus-Training. N/A pre-LPDDR4.                                |

## POWER_TUNING (Power-State Family Bits)

| Bit Field            | Width | Apply        | Description                                                          |
|----------------------|-------|--------------|----------------------------------------------------------------------|
| `apd_idle_threshold` | 16    | all          | Cycles of bank-idleness before APD entry                             |
| `srf_idle_threshold` | 24    | all          | Cycles before Self-Refresh entry                                     |
| `dpd_enable`         | 1     | LP-only      | Deep-Power-Down enable. N/A for DDR-only flavors.                    |
| `pasr_active`        | 1     | LP-only (R)  | Reflects whether any rank has a non-zero PASR mask. R-only.          |
| `ckedis_after_sr`    | 1     | DDR3+        | Drop CKE after SR-entry for sub-mW power floor. N/A in DDR2.         |
| `low_freq_mode`      | 1     | DDR3+        | Reduced-frequency operation hint to PHY. N/A in DDR2.                |

## ECC_TUNING (Future — Inline ECC)

This block is reserved for future inline-ECC controllers. The bits are **N/A in all current controllers** (DDR2/3/4 and LPDDR2/3/4 v1) because inline ECC is out of scope for the current generation. Future revisions of any flavor that adopt inline ECC will populate this block.

| Bit Field            | Width | Apply       | Description                                                          |
|----------------------|-------|-------------|----------------------------------------------------------------------|
| `ecc_enable`         | 1     | (reserved)  | Enable inline ECC. Reads as 0 in all v1 controllers.                 |
| `ecc_correct_mode`   | 2     | (reserved)  | SECDED / Chipkill / off                                              |

## RANK_TUNING (Multi-Rank Family Bits)

These are present in any flavor with `NUM_RANKS > 1`. For `NUM_RANKS = 1` builds, the bits read as 0 and writes are silently ignored.

| Bit Field            | Width | Apply       | Description                                                          |
|----------------------|-------|-------------|----------------------------------------------------------------------|
| `rank_enable_mask`   | 4     | all         | Per-rank enable; clearing a bit suppresses all commands to that rank. Up to 4 ranks. |
| `odt_rule_or`        | 2     | all         | Runtime override for `ODT_RULE_MULTIRANK` (00 = build-time default; 01 = JEDEC_DDR2; 10 = JEDEC_LPDDR2; 11 = OFF). |
| `num_ranks_obs`      | 3     | all (R only)| Echo of build-time `NUM_RANKS`. Software discovery.                  |
| `cs_assert_cycles`   | 4     | all         | Number of cycles to hold `CS_n` asserted per command; tunable for PHY timing margin. |

## Quiet-Point Behavior

All runtime config bits take effect at the **next configuration quiet point** — no DRAM commands in flight, no refresh sequence in progress. The CSR slave does not enforce quiet points automatically; software requests one by writing `CTRL.config_apply = 1`, which triggers a controlled drain. Reads of `STATUS.config_settled` indicate when the override propagation has completed.

The quiet-point requirement is family-wide because every flavor has hand-off state between scheduler / refresh / power-state that would be corrupted by mid-flight reconfiguration.

## Bit Discovery via the Capability Vector

At `0xFF8` of each controller's CSR map, a **capability vector** is exposed:

| Bits  | Field             | Description                                              |
|-------|-------------------|----------------------------------------------------------|
| 0     | `cap_happy`       | 1 = HAPPY predictor synthesized                          |
| 1     | `cap_bg_balance`  | 1 = bank-group balance scheduler logic present (DDR4+)   |
| 2     | `cap_fgr`         | 1 = Fine-Granularity Refresh supported (DDR3+)           |
| 3     | `cap_pasr`        | 1 = PASR mask is implemented (LP-only)                   |
| 4     | `cap_dpd`         | 1 = Deep-Power-Down supported (LP-only)                  |
| 5     | `cap_wl`          | 1 = Write-leveling implemented (DDR3+)                   |
| 6     | `cap_cbt`         | 1 = CBT implemented (LPDDR4-only)                        |
| 7     | `cap_xor_hash`    | 1 = XOR_HASH address scheme synthesized                  |
| 11:8  | `cap_max_ranks`   | Build-time `NUM_RANKS` (echo of geometry)                |
| 15:12 | `cap_n_phases`    | Build-time `N_PHASES`                                    |
| 19:16 | `cap_memtype`     | 0 = DDR2, 1 = DDR3, 2 = DDR4, 4 = LPDDR2, 5 = LPDDR3, 6 = LPDDR4 |

Software queries this once at boot to decide which family-wide bits are meaningful on the current flavor.

## Per-Flavor Applicability Matrix

| Bit                   | DDR2 | DDR3 | DDR4 | LPDDR2 | LPDDR3 | LPDDR4 |
|-----------------------|------|------|------|--------|--------|--------|
| `lookahead_active`    | ✓    | ✓    | ✓    | ✓      | ✓      | ✓      |
| `force_inorder`       | ✓    | ✓    | ✓    | ✓      | ✓      | ✓      |
| `happy_enable`        | ✓    | ✓    | ✓    | ✓      | ✓      | ✓      |
| `bank_group_balance`  | —    | —    | ✓    | —      | —      | ✓      |
| `refpb_policy_or`     | —    | —    | —    | ✓      | ✓      | ✓      |
| `fgr_mode`            | —    | ✓    | ✓    | —      | —      | —      |
| `bg_field_position`   | —    | —    | ✓    | —      | —      | ✓      |
| `wl_retries`          | —    | ✓    | ✓    | —      | —      | —      |
| `ca_train_enable`     | —    | —    | —    | —      | ✓      | ✓      |
| `cbt_enable`          | —    | —    | —    | —      | —      | ✓      |
| `dpd_enable`          | —    | —    | —    | ✓      | ✓      | ✓      |
| `ckedis_after_sr`     | —    | ✓    | ✓    | —      | —      | —      |
| `rank_enable_mask`    | ✓    | ✓    | ✓    | ✓      | ✓      | ✓      |
| `odt_rule_or`         | ✓    | ✓    | ✓    | ✓      | ✓      | ✓      |
| `xor_seed_runtime`    | ✓    | ✓    | ✓    | ✓      | ✓      | ✓      |

The "—" entries are present in the CSR map at the documented offsets but read 0 and ignore writes in that flavor. Software treats these as "soft-N/A" — not an error condition, just an absent feature.

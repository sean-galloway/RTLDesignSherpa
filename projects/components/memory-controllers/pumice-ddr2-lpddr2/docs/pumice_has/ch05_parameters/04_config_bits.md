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
| `qos_high_priority`   | 1     | all          | **PLANNED — not in the RDL yet** (roadmap Axis 1, QoS step): when 1, scheduler boosts requests with `awqos`/`arqos` ≥ 8. |
| `bank_group_balance`  | 1     | DDR4+        | Round-robin across bank groups in scheduler tie-break (DDR4/LPDDR4 only); N/A elsewhere. |

## REFRESH_TUNING (Refresh Family Bits)

| Bit Field             | Width | Apply       | Description                                                          |
|-----------------------|-------|-------------|----------------------------------------------------------------------|
| `refpb_policy_or`     | 2     | LP-only     | REFpb selection-policy override (LPDDR2/3/4); N/A for DDR-only flavors |
| `page_policy_or`      | 2     | all         | Runtime override for the LEGACY flat page policy (`01`=OPEN, `10`=CLOSE). Only consulted when `PAGE_POLICY_CFG.policy_mode == 0`; since policy_mode now RESETS to 3, this field is inert out of reset. `10`=CLOSE drives the legacy auto-precharge path, which measures 4.9x the activations of a background precharge -- see MAS ch02 "08_page_policy". |
| `refresh_defer_active`| 4     | all         | Active deferral count (1 .. build-time MAX). 1 = no batching.        |
| `zqcs_freq_hz`        | 16    | all         | Periodic ZQCS interval. 0 = init-only.                              |
| `fgr_mode`            | 2     | DDR3+       | Fine-Granularity Refresh mode (DDR3 1x/2x/4x; DDR4 fixed-rate, on-the-fly). N/A in DDR2. |
| `refresh_per_rank`    | 1     | all         | Force per-rank dispatch even when `NUM_RANKS=1` (debug). Reset = 1 always when multi-rank. |

## PAGE_POLICY_CFG / PAGE_TIMEOUT_CFG (Axis 2)

The runtime page-policy engine (`pumice_page_policy`). **This axis carries the
largest measured runtime win on the controller**, and as of 2026-09-27 its
resets SHIP that win: `policy_mode = 3` (`fixed_open`) and `tr_init = 2`.

Those two must move together. `tr_init = 0` disables the timeout outright, so
mode 3 with the old `tr_init` reset of 0 would have been open page wearing
another name -- which is exactly the trap the field description records.

**THE ADAPTIVE MODES WERE REMOVED 2026-09-27** (TASK-014). Paging modes 4
(`adapt_time`) and 5 (`adapt_access`) are gone, along with
`pumice_row_pred_table.sv` and the whole `PAGE_ADAPT_CFG` register. Mode 4 had
been MEASURED to be `fixed_open(tr_min)` -- its mistake counter is dominated by
the held-too-long case, so TR decayed monotonically to the floor and stayed
there, landing exactly on the matching fixed point at three different floors.
Mode 5 drove auto-precharge, which costs 4.9x the activations of a background
precharge and double the read latency, and commits at the column op before it
is known whether more same-row requests are coming -- it fights the FR-FCFS
reordering that justifies this design. Mode 5 was removed as a DECISION, not a
measurement: it was unproven and mis-plumbed rather than disproven.

`policy_mode` remains a 3-bit field, so software can still WRITE 4..7. Those
encodings fall through to the build default and never auto-precharge; that
contract is regressed by `test_page_predictor` and by the scheduler matrix.

| Field | Width | Reset | Notes |
|-------|-------|-------|-------|
| `PAGE_POLICY_CFG.policy_mode` | 3 | **3** | 0=build default, 1=static_open, 2=static_close, 3=fixed_open. **4..7 RETIRED** and fall through to the build default (4/5 on 2026-09-27, TASK-014; 6/7 on 2026-09-26, TASK-011). **RESET IS 3** (`fixed_open`) since 2026-09-27: it is the measured optimum and BUG-003, which blocked the change, is fixed. Measured on the board 2026-09-27 (75 MHz, BL4 x16, 600 MB/s peak, 24 cells over four scenario families, every cell integrity-clean): +9.1% col_major (195.2 -> 212.9 MB/s), +35.1% col_major_interleaved (262.1 -> 354.1), exactly flat on incremental (561.1) and row_major (572.0), nothing regressing. TR=1 and TR=2 measure identical; the cliff is between 2 and 3. |
| `PAGE_POLICY_CFG.policy_scope` | 1 | 0 | **RESERVED** since 2026-09-27. Was documented as "per-bank TR" but could not diverge: `r_mc` was one global counter driving every `r_tr[b]`. Retired with mode 4. |
| `PAGE_POLICY_CFG.ctr_open_max` / `ctr_init` | 4 each | 0 | **RESERVED** since 2026-09-27. Were the mode-5 predictor's close threshold and counter init. Bit positions held so `policy_mode` does not move. |
| `PAGE_TIMEOUT_CFG.tr_init` | 8 | **2** | The ONLY live field in this register. **RESET IS 2** since 2026-09-27, moved together with policy_mode -- `tr_init=0` DISABLES the timeout, so a reset of 0 would silently neuter mode 3 and the two must change together. Idle MC cycles before the background precharge fires. **`0` DISABLES the timeout** -- it is not a build-default sentinel on this field. TR=1 and TR=2 measure identically; TR=4 already loses the plain `col_major` wins. |
| `PAGE_TIMEOUT_CFG.tr_min` / `tr_max` / `tr_step` | 8 each | 0 | **RESERVED** since 2026-09-27. Were the mode-4 TR clamps and step. Bit positions held so `tr_init` does not move. |

`PAGE_ADAPT_CFG` (0x078) is **deleted**. The address is left a HOLE rather than
reused, exactly as 0x07C was when `PAGE_RBL_CFG` retired: every register in this
map carries an explicit absolute offset, so removing one shifts nothing, and an
old host reading 0x078 gets nothing back instead of another register's meaning.
Verified by diffing the generated register maps before and after -- 81 -> 80
registers, **zero moved**.

> **STALE ROWS ELSEWHERE IN THIS FILE.** `happy_enable` (SCHED_TUNING) and
> `zqcs_freq_hz` / `refresh_defer_active` / `refpb_policy_or` (REFRESH_TUNING)
> describe retired hardware: the HAPPY predictor and `page_predictor.sv` are
> gone, and the three REFRESH_TUNING fields were retired 2026-09-09 (refresh
> mode and the JEDEC postpone/pull-in credits are `REF_CTRL` now; no ZQCS engine
> ever consumed the interval). Left in place rather than silently rewritten
> because they predate this change and are not part of it -- they need their own
> pass against the RDL.

## ADDR_MAP (Address-Mapping Family Bits)

The address-map register at 0x04C is a single **placement knob**, not a scheme
mux. The old `ADDR_MAP_TUNING` register (with a `scheme_or` selector and a
`synth_mask_obs` synthesized-scheme bitmask) has been **retired** in this
generation: the classic ROW_MAJOR / BANK_INTERLEAVE / XOR_HASH schemes are just
settings of `bank_lsb` plus the optional `hash_en` fold, so there is nothing to
mux (see §5.4 §3/§4 and `rtl/fub/addr_mapper.sv`).

| Bit Field   | Width | Apply       | Description                                                                 |
|-------------|-------|-------------|-----------------------------------------------------------------------------|
| `bank_lsb`  | 5     | all         | Bank-field LSB in the word address. `= COL_WIDTH` -> ROW_MAJOR; lower -> interleave. RTL clamps to `[0, COL_WIDTH]`. |
| `hash_en`   | 1     | all         | Enable bank XOR-hash fold (`bank ^= fold(row) ^ hash_seed`) = the old XOR_HASH scheme. |
| `hash_seed` | 8     | all         | XOR-hash seed. Runtime seed change without rebuild.                         |

Family note: for DDR4+ the bank-group field is placed by extending the same
`bank_lsb`-relative stack rather than by a separate `bg_field_position`
selector; that generation's RDL documents the exact field split.

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

Runtime config bits take effect at the **next configuration quiet point** — no
DRAM commands in flight, no refresh sequence in progress. The register block
does not enforce quiet points automatically; SoC firmware is responsible for
sequencing writes at a drain point (typically during init or an
orchestrated idle window). This generation's RDL does not implement a
`config_apply` strobe or a `config_settled` status bit — a future family
revision may add one; today the SoC owns the drain.

The quiet-point requirement is family-wide because every flavor has hand-off state between scheduler / refresh / power-state that would be corrupted by mid-flight reconfiguration.

## Bit Discovery via the ID Register

This generation does not implement a dedicated capability vector; software
discovers the build via the `ID` register at `0xFF0` (see §6.3): `memtype`,
`n_phases` (gear ratio), and `version` are readable there, and `module_id` is
the fixed `0xD2` family tag. Echo fields embedded in the tuning registers
(`SCHED_TUNING.lookahead_max_obs`, etc.) expose the remaining synthesized
ceilings. A future family revision may add a packed capability vector along the
lines below:

| Bits  | Field             | Description                                              |
|-------|-------------------|----------------------------------------------------------|
| 0     | `cap_happy`       | 1 = HAPPY predictor synthesized                          |
| 1     | `cap_bg_balance`  | 1 = bank-group balance scheduler logic present (DDR4+)   |
| 2     | `cap_fgr`         | 1 = Fine-Granularity Refresh supported (DDR3+)           |
| 3     | `cap_pasr`        | 1 = PASR mask is implemented (LP-only)                   |
| 4     | `cap_dpd`         | 1 = Deep-Power-Down supported (LP-only)                  |
| 5     | `cap_wl`          | 1 = Write-leveling implemented (DDR3+)                   |
| 6     | `cap_cbt`         | 1 = CBT implemented (LPDDR4-only)                        |
| 7     | `cap_xor_hash`    | 1 = bank XOR-hash implemented                            |
| 11:8  | `cap_max_ranks`   | Build-time `NUM_RANKS` (echo of geometry)                |
| 15:12 | `cap_n_phases`    | Build-time gear ratio (`DFI_RATE`)                       |
| 19:16 | `cap_memtype`     | 0 = DDR2, 1 = DDR3, 2 = DDR4, 4 = LPDDR2, 5 = LPDDR3, 6 = LPDDR4 |

## Per-Flavor Applicability Matrix

| Bit                   | DDR2 | DDR3 | DDR4 | LPDDR2 | LPDDR3 | LPDDR4 |
|-----------------------|------|------|------|--------|--------|--------|
| `lookahead_active`    | Y    | Y    | Y    | Y      | Y      | Y      |
| `force_inorder`       | Y    | Y    | Y    | Y      | Y      | Y      |
| `happy_enable`        | Y    | Y    | Y    | Y      | Y      | Y      |
| `bank_group_balance`  | —    | —    | Y    | —      | —      | Y      |
| `refpb_policy_or`     | —    | —    | —    | Y      | Y      | Y      |
| `fgr_mode`            | —    | Y    | Y    | —      | —      | —      |
| `bg_field_position`   | —    | —    | Y    | —      | —      | Y      |
| `wl_retries`          | —    | Y    | Y    | —      | —      | —      |
| `ca_train_enable`     | —    | —    | —    | —      | Y      | Y      |
| `cbt_enable`          | —    | —    | —    | —      | —      | Y      |
| `dpd_enable`          | —    | —    | —    | Y      | Y      | Y      |
| `ckedis_after_sr`     | —    | Y    | Y    | —      | —      | —      |
| `rank_enable_mask`    | Y    | Y    | Y    | Y      | Y      | Y      |
| `odt_rule_or`         | Y    | Y    | Y    | Y      | Y      | Y      |
| `hash_en` / `hash_seed` | Y  | Y    | Y    | Y      | Y      | Y      |

The "—" entries are present in the CSR map at the documented offsets but read 0 and ignore writes in that flavor. Software treats these as "soft-N/A" — not an error condition, just an absent feature.

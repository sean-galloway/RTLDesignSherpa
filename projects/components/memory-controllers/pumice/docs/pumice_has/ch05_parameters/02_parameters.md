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

# Top-Level Parameter Table

All build-time parameters for the controller, with type, default, valid range, the section that governs their use, and a one-line purpose summary.

## Parameter Table

| Parameter                   | Type    | Default                          | Range                                        | Section | Purpose                                                                 |
|-----------------------------|---------|----------------------------------|----------------------------------------------|---------|-------------------------------------------------------------------------|
| `MEMTYPE`                   | string  | `"DDR2"`                         | `{"DDR2", "LPDDR2"}`                         | §3.6    | Picks encoder + step table at build time                                |
| `N_PHASES`                  | int     | 4                                | `{1, 2, 4}`                                  | §3.6    | DFI frequency-ratio gear                                                |
| `AXI_DATA_WIDTH`            | int     | 64                               | `{64, 128, 256}`                             | §3.1    | AXI4 data bus width                                                     |
| `AXI_ID_WIDTH`              | int     | 4                                | 1–16                                         | §3.1    | AXI ID tag width                                                        |
| `AXI_ADDR_WIDTH`            | int     | 32                               | 24–40                                        | §3.1    | AXI flat address width                                                  |
| `AXI_OOO_ACROSS_IDS`        | bool    | `true`                           | `{true, false}`                              | §3.1    | Allow out-of-order completion across AXI IDs                            |
| `SCHEDULER_MODE`            | enum    | `OOO`                            | `{OOO, INORDER}`                             | §3.2    | `OOO` = synthesize the full FR-FCFS scheduling logic (default; debug-friendly — INORDER mode is then available via runtime CSR). `INORDER` = omit FR-FCFS at elaboration; smaller area but permanent in-order operation. **Runtime override: `SCHED_TUNING.force_inorder`** forces FIFO at runtime without rebuild when `OOO` is synthesized. |
| `SUPPORT_FIXED_BURST`       | bool    | `false`                          | `{true, false}`                              | §3.1    | AXI4 FIXED burst type support                                           |
| `SUPPORT_WRAP_BURST`        | bool    | `false`                          | `{true, false}`                              | §3.1    | AXI4 WRAP burst type support                                            |
| `NUM_RANKS`                 | int     | 1                                | `{1, 2, 4}`                                  | §3.3    | Number of physical ranks (per-rank `CS_n`, `CKE`, `ODT`). 1 = single-rank point-to-point; 2 / 4 = DIMM-class. Rank bits are placed in the address map (see §3.1) and refresh state is tracked per (rank, bank). |
| `NUM_BANKS`                 | int     | 8                                | `{4, 8}`                                     | §3.3    | Per-device bank count (per rank)                                        |
| `ODT_RULE_MULTIRANK`        | enum    | `JEDEC_DDR2`                     | `{JEDEC_DDR2, JEDEC_LPDDR2, OFF}`            | §3.6    | Multi-rank ODT termination policy. `JEDEC_DDR2` = read→ODT-high on the non-accessed rank during the read window, write→ODT-high on the accessed rank during the write window. `JEDEC_LPDDR2` = LPDDR2's simpler always-off-during-read rule. `OFF` = no ODT driving (point-to-point only; valid only for `NUM_RANKS=1`). Forced to `OFF` when `NUM_RANKS=1`. |
| `ROW_WIDTH`                 | int     | 14                               | 12–16                                        | §3.3    | Row-address width                                                       |
| `COL_WIDTH`                 | int     | 10                               | 9–12                                         | §3.3    | Column-address width                                                    |
| `DFI_DATA_WIDTH`            | int     | 32                               | 16–128                                       | §3.6    | Per-phase DFI data width                                                |
| `DFI_ADDR_WIDTH`            | int     | 14 (DDR2) / 20 (LPDDR2)          | ≥14 (DDR2), ≥20 (LPDDR2)                     | §3.6    | DFI address bus width                                                   |
| `WRPHASE`                   | int     | 0                                | 0 .. `N_PHASES-1`                            | §3.6    | Which DFI phase carries write data                                      |
| `RDPHASE`                   | int     | 0                                | 0 .. `N_PHASES-1`                            | §3.6    | Which DFI phase carries read data                                       |
| `TXN_QUEUE_DEPTH`           | int     | 16                               | 4–64                                         | §3.2    | Pending-transaction queue depth                                         |
| `AGE_MAX`                   | int     | 256                              | 32–1024                                      | §3.2    | FR-FCFS anti-starvation cap                                             |
| `LOOKAHEAD_DEPTH_MAX`       | int     | 4                                | `{0, 1, 2, 4}`                               | §3.2    | Synthesized MAX number of same-bank lookahead comparators per bank. `0` omits lookahead at elaboration. **Runtime active depth: `SCHED_TUNING.lookahead_active`** picks how many of the synthesized comparators are gated on (0 .. MAX) without rebuild. Reset value of `lookahead_active` matches the build's recommended default (typically 1). |
| `PAGE_POLICY`               | enum    | `HAPPY_HYBRID` (LPDDR2) / `OPEN` (DDR2) | `{OPEN, CLOSE, HAPPY_HYBRID}`           | §3.2    | Fallback policy when lookahead is inconclusive                          |
| `PAGE_PREDICTOR_TABLE_BITS` | int     | 12                               | 8–16                                         | §3.2    | HAPPY predictor table size (synthesized only when `PAGE_POLICY` is `HAPPY_HYBRID`). **Runtime kill-switch: `SCHED_TUNING.happy_enable`** disables predictor lookup without rebuild — useful for A/B'ing HAPPY's contribution to perf. |
| `ADDR_MAP_SCHEMES_SYNTH`    | set     | `{ROW_MAJOR}`                    | subset of `{ROW_MAJOR, BANK_INTERLEAVE, XOR_HASH}` | §3.1 | Schemes synthesized for runtime mux. Including more schemes adds a small amount of address-decode logic. **Runtime mux: `ADDR_MAP_TUNING.scheme_or`** picks the active scheme among the synthesized set. |
| `ADDR_MAP_SCHEME_DEFAULT`   | enum    | `ROW_MAJOR`                      | one of `ADDR_MAP_SCHEMES_SYNTH`              | §3.1    | Reset-state choice among the synthesized schemes (used when CSR override is 00).        |
| `REFPB_POLICY`              | enum    | `DARP`                           | `{ROUND_ROBIN, OLDEST_FIRST, DARP}`          | §3.4    | Per-bank refresh scheduling policy                                      |
| `REFRESH_DEFER_MAX`         | int     | 8                                | 1–8                                          | §3.4    | Synthesized MAX refresh-postponement count (counter width is `clog2(MAX)`). **Runtime active: `REFRESH_TUNING.refresh_defer_active`** picks any value 1..MAX without rebuild. 1 = no batching (every tREFI fires one refresh). |
| `SIM_INIT_SCALE`            | int     | 1                                | 1–10000                                      | §3.5    | Init-delay divider for sim runs (silicon always uses 1)                 |

**Runtime-only knobs** (no build-time presence — purely register-file values):

- `REFRESH_TUNING.zqcs_freq_hz` (16-bit) — Periodic ZQCS interval in Hz. 0 disables periodic ZQCS (init-only). Reset = 1 Hz.
- `INIT_TUNING.zq_retries` (4-bit) — ZQ calibration retry count before raising `init_error`. Reset = 3.
- `INIT_TUNING.init_timeout_ms` (8-bit) — Per-step init timeout. Reset = 10.

These cost zero silicon area beyond the register flops; making them build-time parameters would have been wrong (and was, in earlier revisions of this document).

## Memtype-Dependent Constraints

Some parameters have memtype-dependent constraints checked at elaboration:

- `MEMTYPE == "LPDDR2"` ⇒ `DFI_ADDR_WIDTH ≥ 20` (CA bus packing requirement)
- `MEMTYPE == "DDR2"` ⇒ `DFI_ADDR_WIDTH ≥ ROW_WIDTH`
- `PAGE_POLICY == HAPPY_HYBRID` ⇒ `PAGE_PREDICTOR_TABLE_BITS` must be in range; otherwise the predictor module is not instantiated and the parameter is ignored

## Timing-Configuration Sanity Checks

The controller performs the following elaboration-time assertions on the loaded timing CSR values:

- `tREFI_cycles ≥ 100` — the MC clock must be fast enough relative to tREFI that the refresh timer is well-resolved. If not, elaboration fails with a clear error.
- `tRCD_cycles ≥ 2`, `tRP_cycles ≥ 2`, `tRC_cycles ≥ tRAS + tRP` — basic JEDEC consistency checks.
- `tRFC_cycles > tRP_cycles` — the refresh-cycle time must exceed the precharge time.

These are not preventable run-time errors — they're configuration bugs that should be caught at synthesis or boot time before silicon ships.

## Parameter Categories

| Category         | Parameters                                                                                          |
|------------------|-----------------------------------------------------------------------------------------------------|
| Memtype          | `MEMTYPE`                                                                                           |
| Geometry         | `NUM_RANKS`, `NUM_BANKS`, `ROW_WIDTH`, `COL_WIDTH`                                                  |
| Multi-rank       | `NUM_RANKS`, `ODT_RULE_MULTIRANK`                                                                   |
| Bus widths       | `AXI_DATA_WIDTH`, `AXI_ID_WIDTH`, `AXI_ADDR_WIDTH`, `DFI_DATA_WIDTH`, `DFI_ADDR_WIDTH`              |
| Gear             | `N_PHASES`, `WRPHASE`, `RDPHASE`                                                                    |
| AXI features     | `AXI_OOO_ACROSS_IDS`, `SUPPORT_FIXED_BURST`, `SUPPORT_WRAP_BURST`                                   |
| Capacity         | `TXN_QUEUE_DEPTH`, `AGE_MAX`                                                                        |
| Characterization | `LOOKAHEAD_DEPTH_MAX`, `PAGE_POLICY`, `PAGE_PREDICTOR_TABLE_BITS`, `ADDR_MAP_SCHEMES_SYNTH`, `REFPB_POLICY`, `REFRESH_DEFER_MAX` (all paired with runtime CSR overrides — see §6.3) |
| Init             | `SIM_INIT_SCALE`                                                                                    |

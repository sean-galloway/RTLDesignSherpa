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

# Register Map

> The full bit-level register map is in HAS §6.3. This MAS chapter is the **implementation-level** view: how the registers are generated, where the source of truth lives, how staging-vs-live works, and how the per-rank generation handles multi-rank.

---

## Source of Truth

The CSR map is generated from `regs/ddr2_lpddr2_csrs.yaml` (PeakRDL-style YAML). The generator produces:

| File                                  | Consumer                                           |
|---------------------------------------|----------------------------------------------------|
| `regs/ddr2_lpddr2_csr_pkg.sv`         | SV package: offsets, field masks, reset values     |
| `regs/ddr2_lpddr2_csr_block.sv`       | The wrapped register file (used inside `csr_apb_fub`) |
| `regs/ddr2_lpddr2_csrs.h`             | C header for SoC software                          |
| `regs/ddr2_lpddr2_csr_block_uvm.sv`   | UVM register model for verification                |
| `regs/ddr2_lpddr2_csrs.json`          | Machine-readable spec for documentation tools      |

The HAS-side bit-level table in HAS §6.3 is **derived** from the YAML — it is not the source of truth. If the YAML and HAS disagree, the YAML wins (and a CI check should catch the disagreement).

## Staging vs. Live State

Every R/W field has two storage cells:

1. **APB-side staging register** — written immediately on the APB write, lives in `apb_pclk` domain
2. **MC-side live register** — copied from staging at the next quiet point, lives in `mc_clk` domain

The staging→live commit takes one MC-clock edge. Reads can return either side depending on the field type:

| Field type                   | Read returns                                                       |
|------------------------------|--------------------------------------------------------------------|
| Read-only observation        | Live MC-side counter (Gray-synchronized to APB side)               |
| R/W configuration (`*_TUNING`)| Staging by default; switches to live after `CTRL.config_apply` is acknowledged |
| Read-only echo / capability   | Constant value from build parameters                                |

The two-cell architecture means software can read back the value it just wrote (from staging) before the commit completes — useful for sanity-checking the write took effect.

## Per-Rank Register Generation

The YAML uses a `repeat` clause to instantiate per-rank registers. Example:

```yaml
PASR_BANK_MASK_RANK:
  offset: 0x030
  repeat: NUM_RANKS
  stride: 0x004
  access: rw
  fields:
    pasr_banks:
      bits: 7:0
      reset: 0
```

At `NUM_RANKS=1` this produces only `PASR_BANK_MASK_RANK0` at 0x030. At `NUM_RANKS=4` it produces `PASR_BANK_MASK_RANK0..3` at 0x030, 0x034, 0x038, 0x03C.

The generator emits a `pslverr` decoder for ranks beyond `NUM_RANKS-1`. The HAS-side register map shows the maximum-config layout; software queries the `0xFF8` capability vector for the actual rank count.

## Per-(Rank, Bank) Register Generation

The observation registers in 0x080–0x0FF use a 2-D repeat:

```yaml
OBS_ROW_HIT_RANK_BANK:
  offset: 0x080
  repeat_outer: NUM_RANKS
  repeat_inner: NUM_BANKS
  outer_stride: NUM_BANKS * 4
  inner_stride: 0x004
  access: ro
  fields:
    row_hit_count:
      bits: 31:0
      source: scheduler.row_hit_ctr[r][b]
```

The 2-D layout means at NR=1, NB=8 the registers consume 0x080–0x09C (8 × 4 bytes). At NR=4, NB=8 they consume 0x080–0x0FF (32 × 4 bytes — saturates the available window).

If a future build needs NR > 4, NB > 8 (256 registers), the window needs to grow — there's a 0x180 spare slot available.

## Field Source Attribution

Each R/W field's MC-side live value drives a specific FUB input (per §1.3 and the per-FUB CSR sections):

| CSR field                                  | Drives                                          |
|--------------------------------------------|-------------------------------------------------|
| `SCHED_TUNING.force_inorder`               | `scheduler.cfg_force_inorder_i`             |
| `SCHED_TUNING.lookahead_active`            | `scheduler.cfg_lookahead_active_i`           |
| `REFRESH_TUNING.refresh_defer_active`      | `refresh_mgr_fub.cfg_refresh_defer_active_i`     |
| `REFRESH_TUNING.zqcs_freq_hz`              | `refresh_mgr_fub.cfg_zqcs_freq_hz_i`             |
| `ADDR_MAP_TUNING.scheme_or`                | `addr_mapper.scheme_active_i`                |
| `ADDR_MAP_TUNING.xor_seed_runtime`         | `addr_mapper.xor_seed_i`                     |
| `RANK_TUNING.odt_rule_or`                  | `odt_ctrl_fub.cfg_odt_rule_or_i`                 |
| `POWER_TUNING.apd_idle_threshold`          | `power_state_fub.cfg_apd_idle_threshold_i`        |
| ... (many more) ...                        | per-FUB CSR sections                             |

This attribution is also generated from the YAML — the `source:` field per CSR field tells the generator which SV instance hierarchy receives the value.

## Reset Values

| Field type                   | Reset value source                                        |
|------------------------------|-----------------------------------------------------------|
| Configuration (`*_TUNING`)   | YAML `reset:` field; populated to match build defaults     |
| Observation (`OBS_*`)        | 0                                                          |
| Build-time echo (`*_obs`)    | Build parameter value                                      |
| Capability vector (`0xFF8`)  | Derived from build-time config                             |

The reset values must match the synthesized defaults so that "do nothing" software sees the controller's intended baseline behavior.

## Generation Pipeline

```
ddr2_lpddr2_csrs.yaml
        |
        v
peakrdl-csr-gen.py    (or equivalent)
        |
        +--> ddr2_lpddr2_csr_pkg.sv
        +--> ddr2_lpddr2_csr_block.sv      <-- instantiated in csr_apb_fub
        +--> ddr2_lpddr2_csrs.h            <-- consumed by SoC firmware
        +--> ddr2_lpddr2_csr_block_uvm.sv  <-- consumed by UVM tests
        +--> ddr2_lpddr2_csrs.json         <-- consumed by doc-gen
```

The generator is invoked by the FUB filelist build (`rtl/filelists/fub/csr_apb.f`); the `ddr2_lpddr2_csr_block.sv` is a build artifact, not a checked-in source file. Changes to the YAML trigger regeneration on next build.

## Open Questions / Future Work

- **YAML schema versioning.** When the YAML schema changes (e.g., DDR3+ adds new fields), need a version bumper. Add `schema_version: 1.0` field to track.
- **HAS §6.3 ↔ YAML CI drift check.** Currently the HAS bit-level tables are hand-maintained from the YAML. A CI check that compares could catch drift. Punt to verification setup.
- **Field-level access timestamps.** When debugging "what wrote this register?", a per-field last-write-timestamp would be useful. Adds area; not in v1.

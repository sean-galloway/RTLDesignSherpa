<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> &middot; <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> &middot;
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Family-Wide Config-Bit Applicability

**Status:** Skeleton — to be authored during MAS week


> The full family-wide config-bit registry is in HAS §5.4. This MAS section documents the implementation-level shape of those bits in **this controller specifically**.

## Per-Bit Implementation Notes for DDR2 / LPDDR2

Bits flagged `(reserved)` in HAS §5.4 ECC_TUNING are present in the CSR map at the documented offsets but read as zero and writes are ignored. The CSR slave does not raise `pslverr` on these — software portability requires writing the family-wide config word to succeed on flavors that haven't implemented every bit.

Bits flagged `DDR3+`, `DDR4+`, `LPDDR3+`, `LPDDR4-only` likewise read as zero and ignore writes in this DDR2/LPDDR2 controller.

The `0xFF8` capability vector reports the build's actual capabilities; software queries this once at boot to decide which family-wide writes are meaningful.

## Soft-N/A Behavior Examples

- Writing `SCHED_TUNING.bank_group_balance = 1` in DDR2 build: silently ignored, no `pslverr`. Read-back returns 0.
- Writing `POWER_TUNING.dpd_enable = 1` in DDR2 build: silently ignored. (DPD is LPDDR-only.)
- Reading `INIT_TUNING.cbt_enable` in any v1 controller: returns 0. (LPDDR4 only.)

## TODO

- Per-bit implementation note for every family-wide bit
- Test plan for each soft-N/A bit
- Software bring-up sequence demonstrating capability-vector-gated writes


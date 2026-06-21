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

# `dfi_v21_interface_macro`

**Module:** `dfi_v21_interface_macro.sv`
**Location:** `rtl/macro/`
**Category:** Integration macro (pure structural)
**Parent macro:** `ddr2_lpddr2_core_macro`
**FUBs bundled:** 2

## Purpose

"Translate internal control + data into DFI v2.1 wires." The single
layer in the controller core that owns the JEDEC truth tables for
DDR2/LPDDR2 commands and the multi-phase pack.

**Swap THIS macro** when moving to DFI v3 / v4 / v5 / v6 for newer
DRAM generations — the rest of the core (scheduler, timers, refresh,
data path) is DFI-version-agnostic.

## FUBs

| FUB                  | Role                                                                                                |
|----------------------|-----------------------------------------------------------------------------------------------------|
| `dfi_cmd_formatter`  | JEDEC truth table for ACT/RD/RDA/WR/WRA/PRE/PREA/REF/REFpb/MRS/NOP → DFI control wires. ODT rule.   |
| `dfi_signal_pack`    | Multi-phase aggregation: widens every DFI bus to per-phase × `DFI_RATE`. v1 phase 0 only.           |

## External Boundaries

- **Upstream from `command_scheduler_macro`**: cmd_* channel.
- **Upstream from `data_path_macro`**: dfi_wrdata / dfi_wrdata_en /
  dfi_wrdata_mask, dfi_rddata_en.
- **Downstream**: DFI v2.1 master port to the PHY. Per-phase × `DFI_RATE`
  widths for every control bus.

## Multi-Phase Pack Convention

For `DFI_RATE = N`, every DFI control bus output is widened to
per-phase × N (e.g., for `DFI_RATE=2` and `DFI_ADDR_WIDTH=15`, the
aggregate `dfi_address_o` is 30 bits wide: phase-0 in bits [14:0],
phase-1 in bits [29:15]).

v1 uses phase 0 for the command and drives NOP on the other phases.
A future revision may issue different commands on each phase to
achieve >1 command per MC clock.

## Tests

No macro-level test yet; each FUB has its own unit test
(`test_dfi_cmd_formatter.py` 10 scenarios, `test_dfi_signal_pack.py`
6 scenarios).

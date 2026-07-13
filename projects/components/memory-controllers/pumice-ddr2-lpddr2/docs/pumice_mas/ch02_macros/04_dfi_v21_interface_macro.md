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

# `pumice_dfi_layer` (DFI v2.1 interface macro)

**Module:** `pumice_dfi_layer.sv`
**Location:** `rtl/macro/`
**Category:** Layer-3 macro (the PHY-facing layer of `pumice_core`)
**FUBs bundled:** single CDC + command path + write serializer + read aligner

## Purpose

"Translate the internal command + data streams into DFI v2.1 wires, and hold
the one clock crossing." This layer owns the JEDEC command encoding for
DDR2/LPDDR2, the multi-phase pack, and the **single** controller-to-PHY clock
crossing. It presents the controller-clock command / wrdata / rddata streams on
one side and the DFI 2.1 pin bus on the other.

**Swap THIS macro** when moving to DFI v3+ for newer DRAM generations -- the
other two core layers (AXI front-end, scheduler) are DFI-version-agnostic.

This replaces the old `dfi_v21_interface_macro` (`dfi_cmd_formatter` +
`dfi_signal_pack`) and the retired `gear_dfi` block; the CDC that used to be
implied elsewhere is now explicitly this layer's `pumice_dfi_cdc`.

## FUBs

| FUB                        | Clock     | Role                                                                                     |
|----------------------------|-----------|------------------------------------------------------------------------------------------|
| `pumice_dfi_cdc`           | both      | The **single** controller/PHY crossing -- async gaxi FIFOs only. Carries cmd (`aclk`->`dfi_clk`), wrdata (`aclk`->`dfi_clk`), rddata (`dfi_clk`->`aclk`), plus the init handshake. |
| `pumice_dfi_cmd_path`      | `dfi_clk` | Command FIFO -> DFI command bus. Uses `dfi_cmd_formatter` (+ `dfi_signal_pack`) to phase-place the JEDEC command on `wr_phase` / `rd_phase`; drives address/bank/ras/cas/we/cs/odt; emits `wr_fire` / `rd_fire` strobes. |
| `pumice_dfi_wr_serializer` | `dfi_clk` | Write-data FIFO -> `dfi_wrdata` / `dfi_wrdata_en` / `dfi_wrdata_mask` at `t_phy_wrlat` after `wr_fire`. |
| `pumice_dfi_rd_aligner`    | `dfi_clk` | Drives `dfi_rddata_en` at `t_rddata_en` after `rd_fire`; captures `dfi_rddata` on `dfi_rddata_valid`; packs DFI words into the read FIFO. |

The internal datapath unit is the **DFI word** (`dfi_wrdata` width, all
`DFI_RATE` phases). One FIFO word equals one DFI cycle, so the datapath is
bubble-free at rate.

## External Boundaries

- **Controller side (`ctl_clk = aclk`):** `cmd_*` in (from the scheduler, packed
  `{op,rank,bank,row,col,ap}`), `wd_*` in (write commit-data from
  `pumice_wr_data_cam`, `{last,strb,data}` DFI-word), `rd_*` out (read return to
  `pumice_rd_cmd_cam`, `{last,resp,data}`), and `init_start_i` /
  `init_complete_o`.
- **PHY side (`dfi_clk`):** the full DFI 2.1 pin bus -- `dfi_address` /
  `dfi_bank` / `dfi_cas_n` / `dfi_ras_n` / `dfi_we_n` / `dfi_cs_n` / `dfi_odt`,
  `dfi_wrdata` / `dfi_wrdata_en` / `dfi_wrdata_mask`, `dfi_rddata_en` /
  `dfi_rddata` / `dfi_rddata_valid`, and `dfi_init_start` / `dfi_init_complete`.
- **Config in (`dfi_clk` domain):** `memtype_i`, `rd_phase_i` / `wr_phase_i`,
  `t_phy_wrlat_i`, `t_rddata_en_i` -- delivered from the CSR by name.

## Multi-Phase Pack Convention

For `DFI_RATE = N`, every DFI control bus is `per-phase x N` wide (for example,
`dfi_address_o` = `ROW_WIDTH * DFI_RATE`, `dfi_cs_n_o` = `NUM_RANKS * DFI_RATE`).
The command path places the active JEDEC command on the `wr_phase` / `rd_phase`
slot as programmed by the `DFI_PHASE` CSR and drives NOP-equivalent idle on the
other phases. The scheduler never sees the phase dimension; the command path
absorbs all phase placement. `dfi_rddata` read gearing beyond `rd_phase` is left
to the PHY (`a7ddrphy` handles its internal read gearing).

## LPDDR2 Command Encoding

For `memtype_i = LPDDR2`, `dfi_cmd_formatter` takes the memtype branch and emits
bit-exact JESD209-2F CA-bus commands (Table 60): the 10-bit CA bus over 2 edges,
packed as a flat 20-bit word on `dfi_address`, with `ras/cas/we` idle. See
`rtl/LPDDR2_CA_ENCODING.md` for the transcription. DDR2 uses the classic
`ras/cas/we/cs` strobe encoding on the same pins.

## Tests

Each FUB has its own unit test in `dv/tests/fub/`
(`pumice_dfi_cdc`, `pumice_dfi_cmd_path`, `pumice_dfi_wr_serializer`,
`pumice_dfi_rd_aligner`), plus the layer-level test that drives the full
controller-to-PHY path against the DFI slave BFM.

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

> This chapter is the wire-level contract of the controller's DFI 2.1 master
> face -- what's driven, what's tied, what's sampled, what's deferred.
>
> The interface is implemented by `pumice_dfi_layer` (section 2.4):
> `pumice_dfi_cmd_path` (with `dfi_cmd_formatter` + `dfi_signal_pack`) drives the
> command bus, `pumice_dfi_wr_serializer` drives write data,
> `pumice_dfi_rd_aligner` captures read data, and `pumice_dfi_cdc` is the single
> clock crossing to `aclk`.

---

## DFI Spec Reference

Canonical: the DFI 2.1 specification (Denali cleartext copy at
`/home/seang/github/cold_storage/MemorySpecs/`). The controller covers the
subset of DFI 2.1 sub-interfaces needed for DDR2/LPDDR2 operation; higher-version
sub-interfaces are not driven.

## Sub-Interface Support Summary

| Sub-Interface       | Direction        | Supported? | Notes                                                 |
|---------------------|------------------|------------|-------------------------------------------------------|
| Command             | Controller -> PHY | Yes        | Per-phase; command placed on `wr_phase`/`rd_phase`    |
| Write-Data          | Controller -> PHY | Yes        | `dfi_wrdata` presented at `t_phy_wrlat` after WR fire |
| Read-Data           | PHY -> Controller | Yes        | `dfi_rddata_en` at `t_rddata_en` after RD fire; captured on `dfi_rddata_valid` |
| Status (init)       | Both             | Yes        | `dfi_init_start` / `dfi_init_complete` only           |
| Update              | Both             | No         | `ctrlupd_*` / `phyupd_*` not driven in v1             |
| Training            | Both             | No         | PHY-side (`a7ddrphy` self-trains at startup)          |
| Frequency Change    | Both             | No         | No use case                                           |
| Low-Power           | Controller -> PHY | No         | No PHY-side low-power coordination                    |
| Error / CRC         | -                | No         | Not used in DDR2/LPDDR2 here                          |

## Clock and CDC

The DFI pin bus is driven in the **`dfi_clk`** domain. Unlike the classic
"DFI is on the controller clock" model, this controller keeps the whole DFI
datapath on a dedicated PHY clock and places the **single** controller-to-PHY
CDC inside `pumice_dfi_layer` (`pumice_dfi_cdc`, async gaxi FIFOs only). The
command, write-data, and read-data streams plus the init handshake cross there;
the internal datapath unit is the whole DFI word, so one FIFO word is one
`dfi_clk` cycle and the path is bubble-free at rate. `a7ddrphy` handles any
further gearing to the DRAM clock.

## Command Sub-Interface

### Phase Topology

The command bus is `per-phase x DFI_RATE` wide. `dfi_address_o` is
`ROW_WIDTH * DFI_RATE`, `dfi_bank_o` is `$clog2(NUM_BANKS) * DFI_RATE`, and each
control strobe (`dfi_cas_n_o` / `dfi_ras_n_o` / `dfi_we_n_o`) is
`1 * DFI_RATE`. `pumice_dfi_cmd_path` places the active JEDEC command on the
`wr_phase` / `rd_phase` slot (programmed by the `DFI_PHASE` CSR) and drives
NOP-equivalent idle on the other phases.

### Chip-Select and ODT

`dfi_cs_n_o` and `dfi_odt_o` are each `NUM_RANKS * DFI_RATE` wide (rank inner,
phase outer, as the `DFI_CS_BUS_W = NUM_RANKS * DFI_RATE` packing implies). The
formatter drives the addressed rank's CS_n active for a single-rank command;
init-time REF broadcasts. ODT is driven inside `dfi_cmd_formatter` /
`mode_register` -- there is no standalone `odt_ctrl` block.

### DDR2 vs LPDDR2 Encoding

For `memtype_i = DDR2`, commands use the classic `ras/cas/we/cs` strobe
encoding. For `memtype_i = LPDDR2`, `dfi_cmd_formatter` takes the memtype branch
and emits bit-exact JESD209-2F CA-bus commands (Table 60): the 10-bit CA bus
over 2 edges packed as a flat 20-bit word on `dfi_address`, with `ras/cas/we`
idle. See `rtl/LPDDR2_CA_ENCODING.md`.

## Write-Data Sub-Interface

`pumice_dfi_wr_serializer` presents `dfi_wrdata` / `dfi_wrdata_en` /
`dfi_wrdata_mask` exactly `t_phy_wrlat` `dfi_clk` cycles after the `wr_fire`
strobe from the command path. The write burst arrives from the write CAM as
whole DFI words `{last, strb, data}`; the serializer splits into the per-phase
data / enable / mask.

`dfi_wrdata_en_o` is `DFI_RATE` wide (one enable per phase). A mask bit of 1
means "do not write this byte" per DFI convention; the mask payload carried from
the CAM is aligned to that convention.

## Read-Data Sub-Interface

`pumice_dfi_rd_aligner` drives `dfi_rddata_en_o` (`DFI_RATE` wide) exactly
`t_rddata_en` `dfi_clk` cycles after the `rd_fire` strobe, then captures
`dfi_rddata_i` when `dfi_rddata_valid_i` asserts, packing whole DFI words
(`{last, resp, data}`) into the read FIFO for the crossing back to `aclk`.

### Read-Data Error Handling

`dfi_rddata` carries no error bit in DFI 2.1. A missing / malformed read is
surfaced by the aligner's `resp` field and propagated as `SLVERR` on the
affected AXI R beats. On-silicon this path was hardened during board bring-up:
`t_rddata_en` and the DFI read-data delay are runtime CSRs, and `rd_phase = 0`
is correct for `a7ddrphy` (which handles read gearing internally).

## Status / Init Sub-Interface

`dfi_init_start_o` and `dfi_init_complete_i` are the only status signals. The
`init_sequencer` (in `pumice_mem_cmd_scheduler`) asserts `dfi_init_start` and
walks the JEDEC MRS init, waiting on `dfi_init_complete` from the PHY plus the
programmed init-timing CSRs. These cross the CDC in `pumice_dfi_cdc`.

## Pin Tie-Offs

| Pin                                    | Tie-off (when applicable)                  |
|----------------------------------------|--------------------------------------------|
| `dfi_ras_n_o` / `dfi_cas_n_o` / `dfi_we_n_o` | Idle in LPDDR2 (command rides the CA bus on `dfi_address`) |
| Update / frequency / low-power buses   | Not present / not driven                   |

## Open Questions / Future Work

- **DFI error / update.** `ctrlupd_*` / `phyupd_*` and a `dfi_error` input are
  not wired in v1; a later revision could add quiet-point update handshaking and
  route read errors to an IRQ.
- **Per-rank CS width form.** The controller produces the flat
  `NUM_RANKS * DFI_RATE` vector form; a PHY expecting a different packing needs a
  thin wrapper at the boundary.
- **DFI 3+ migration.** When the DDR3-LPDDR3 family controller arrives, the
  sub-interface set grows substantially. Swap `pumice_dfi_layer` and add a
  dedicated DFI section in that MAS; keep this one DDR2/LPDDR2-scoped.

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

# Command Formatter and Signal Pack

Two modules translate the scheduler's abstract command into DFI wire signals: `dfi_cmd_formatter` (memtype-specific encoding and phase placement) and `dfi_signal_pack` (the final registered pipeline stage). `dfi_cmd_formatter` is instantiated inside `pumice_dfi_cmd_path` in the DFI layer.

## `dfi_cmd_formatter`

### Purpose

Translate the scheduler's chosen `dram_op_e` plus `(rank, bank, row, col)` into the multi-phase DFI v2.1 control bus. RTL: `rtl/fub/dfi_cmd_formatter.sv`. It is the only place where DDR2 and LPDDR2 differ at the wire layer, and its outputs are strict-flopped.

### Input

The command arrives on `cmd_valid_i` / `cmd_ready_o` (always ready) with `cmd_op_i` (`dram_op_e`), `cmd_rank_i`, `cmd_bank_i`, `cmd_row_i`, `cmd_col_i`, `cmd_len_i`, and the runtime phase-placement knobs `rd_phase_i` / `wr_phase_i`.

### Multi-Phase Output

For `DFI_RATE = N`, every control signal is packed as N phases side by side on the bus (`dfi_address_o`, `dfi_bank_o`, `dfi_cas_n_o`, `dfi_ras_n_o`, `dfi_we_n_o`, `dfi_cs_n_o`, `dfi_odt_o`). The decoded command is placed on its target phase and the other phases emit selected/deselected NOP. The target phase is:

- `rd_phase_i` for `OP_RD` / `OP_RDA`,
- `wr_phase_i` for `OP_WR` / `OP_WRA`,
- phase 0 for everything else (ACT/PRE/REF/MRS have no data-phase contract).

The R/W phase knobs match the PHY's rdphase/wrphase contract (e.g. a7ddrphy DDR2 CL3 nphases=2). Defaults of 0/0 preserve the legacy "everything on phase 0" behavior. `cs_n` is per-rank: `cs_n[r]=0` selects rank `r`; all-ones is a deselected NOP.

### DDR2 Encoding

Combinational truth table per JESD79-2 Table 49:

| op   | cs_n | ras_n | cas_n | we_n | bank | addr           |
|------|------|-------|-------|------|------|----------------|
| NOP  | sel  | 1     | 1     | 1    | -    | -              |
| ACT  | sel  | 0     | 1     | 1    | BA   | row            |
| RD   | sel  | 1     | 0     | 1    | BA   | col (A10=0)    |
| RDA  | sel  | 1     | 0     | 1    | BA   | col + (1<<10)  |
| WR   | sel  | 1     | 0     | 0    | BA   | col            |
| WRA  | sel  | 1     | 0     | 0    | BA   | col + (1<<10)  |
| PRE  | sel  | 0     | 1     | 0    | BA   | A10=0          |
| PREA | sel  | 0     | 1     | 0    | -    | (1<<10)        |
| REF  | sel  | 0     | 0     | 1    | -    | -              |
| MRS  | sel  | 0     | 0     | 0    | MR   | MR data        |

The auto-precharge / all-bank bit is A10. MRS data rides `cmd_row_i` (ROW_WIDTH), not `cmd_col_i` — MR0 = `0x532` needs bit 10, which a 10-bit column field would truncate.

### LPDDR2 Encoding (bit-exact CA bus)

For LPDDR2 the command rides the multiplexed 10-bit CA bus over 2 edges, packed as a flat 20-bit word carried on `dfi_address` (low bits); `ras_n`/`cas_n`/`we_n` stay idle and `cs_n` asserts for the target rank. The two CA edges are already inside the word, so there is no per-DFI-phase command placement.

The CA word is built **bit-exact to JESD209-2F Table 60**, matching the DV BFM's `lpddr_ca` encoder. Layout: `w_lpddr2_ca[i] = CA{i}` rising edge (i = 0..9), `w_lpddr2_ca[10+i] = CA{i}` falling edge. Encoded commands include ACT, RD/RDA, WR/WRA, PRE, PREA, REF (all-bank), REFPB (per-bank), and MRW; NOP/Deselect drives CA0r..CA3r high. Column bit C0 is implied 0 and never transmitted; the auto-precharge flag lands on CA0f. The transcription reference is `rtl/LPDDR2_CA_ENCODING.md`.

For MRW, `MA0..MA5` map to `CA4r..CA9r`, `MA6/MA7` to `CA0f/CA1f`, and `OP0..OP7` to `CA2f..CA9f`. The init sequencer supplies the full MR index by packing `{MA[5:0], OP[7:0]}` into the ROW field, so MR10/MR63 are reachable.

> Note: the module's top-of-file header comment still carries a stale "LPDDR2 (TODO)" line from an earlier revision. The body implements the full bit-exact CA encoding above; LPDDR2 reads and writes are functional and pass the sim suite.

### Idle Defaults

When not issuing, every phase is driven to its deselected idle: `cs_n=1, ras_n=1, cas_n=1, we_n=1, bank=0, address=0, odt=0` (DFI v2.1 Table 2 defaults). ODT is driven from this module — there is no standalone `odt_ctrl` block.

---

## `dfi_signal_pack`

### Purpose

Final pipeline-register stage on the DFI v2.1 bus. RTL: `rtl/fub/dfi_signal_pack.sv`. It latches every command / write-data / read-data-enable input and drives it out the next MC cycle, owning `dfi_dram_clk_disable` and reset-safe output values.

### Behavior

- v1 is a pure one-cycle registered pipeline. Bus widths are `DFI_*_WIDTH * DFI_RATE`, so the multi-phase content from `dfi_cmd_formatter` passes through unchanged. This is where the internal `DW = DRAM_BEAT_WIDTH * DFI_RATE` word is presented across the `DFI_RATE` phases.
- `dram_clk_disable` is held at 0 in v1; per-phase staggering and power-down assertion are documented TODOs.

### Multi-Cycle Commands

LPDDR2's 2-edge CA command is not split here. The 20-bit CA word is already packed onto `dfi_address` by `dfi_cmd_formatter`; the PHY splits it into two DRAM cycles per DFI v2.1.

### Verification

The RTL output round-trips against the DFI BFM: the DDR2 truth table against the JESD79-2 reference, and the LPDDR2 CA bus against the shared `lpddr_ca` encoder/decoder (the same layout the RTL encodes).

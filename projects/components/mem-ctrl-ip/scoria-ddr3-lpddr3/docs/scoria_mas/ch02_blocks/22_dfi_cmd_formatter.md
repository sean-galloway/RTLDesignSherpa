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

# DFI Command Formatter (`scoria_dfi_cmd_formatter`)

**Module:** `scoria_dfi_cmd_formatter.sv`
**Location:** `rtl/fub/`
**Category:** DFI command encoding
**Parent:** `scoria_dfi_layer`
**Status:** implemented

## Purpose

`scoria_dfi_cmd_formatter` is the last combinational step before the abstract command stream becomes DFI wires. It translates the scheduler's `dram_op_e` opcode plus `{rank, bank, row, col, ap}` into the pin patterns the DRAM expects: DDR3 uses the JESD79-3F `{ras_n, cas_n, we_n}` truth table with address and bank fields; LPDDR3 uses the bit-exact JESD209-2F Table 60 CA-bus encoding packed as `{w_ca_f, w_ca_r}`. The block does not sequence anything — it only encodes. Sequence lives in the scheduler and init sequencer, the same split pumice used.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `NUM_RANKS` | int | 1..4 | 1 | rank count |
| `NUM_BANKS` | int | power of 2 | 8 | bank count |
| `ROW_WIDTH` | int | — | 14 | row address width |
| `COL_WIDTH` | int | — | 10 | column address width |
| `BURST_LEN_WIDTH` | int | — | 8 | burst-length field width (unused) |
| `DFI_RATE` | int | power of 2 | 2 | DFI frequency ratio |
| `DFI_ADDR_WIDTH` | int | — | 14 | per-phase DFI address width |
| `DFI_BANK_WIDTH` | int | — | 3 | per-phase DFI bank width |
| `DFI_CTRL_WIDTH` | int | — | 1 | per-phase control width |
| `DFI_CS_WIDTH` | int | — | `NUM_RANKS` | per-phase chip-select width |

: Table 2.22.1: `scoria_dfi_cmd_formatter` parameters

## Interface

| Signal | Direction | Width | Description |
|---|---|---|---|
| `mc_clk` | in | 1 | controller / DFI clock |
| `mc_rst_n` | in | 1 | active-low synchronous reset |
| `memtype_i` | in | `memtype_e` | DDR3 or LPDDR3 selection |
| `cmd_valid_i` | in | 1 | command valid |
| `cmd_ready_o` | out | 1 | always 1 after reset |
| `cmd_op_i` | in | `dram_op_e` | opcode |
| `cmd_rank_i` | in | `RKW` | target rank |
| `cmd_bank_i` | in | `BKW` | bank address |
| `cmd_row_i` | in | `ROW_WIDTH` | row address / MR payload |
| `cmd_col_i` | in | `COL_WIDTH` | column address |
| `cmd_len_i` | in | `BURST_LEN_WIDTH` | unused — tied off |
| `rd_phase_i` | in | `PHW` | DFI phase for read commands |
| `wr_phase_i` | in | `PHW` | DFI phase for write commands |
| `dfi_address_o` | out | `DFI_ADDR_BUS_W` | multi-phase address bus |
| `dfi_bank_o` | out | `DFI_BANK_BUS_W` | multi-phase bank bus |
| `dfi_cas_n_o` | out | `DFI_CTRL_BUS_W` | multi-phase CAS# |
| `dfi_ras_n_o` | out | `DFI_CTRL_BUS_W` | multi-phase RAS# |
| `dfi_we_n_o` | out | `DFI_CTRL_BUS_W` | multi-phase WE# |
| `dfi_cs_n_o` | out | `DFI_CS_BUS_W` | multi-phase chip-select |
| `dfi_odt_o` | out | `DFI_CS_BUS_W` | multi-phase ODT |

: Table 2.22.2: `scoria_dfi_cmd_formatter` ports

## Microarchitecture internals

### DDR3 command truth table

The DDR3 encoding follows JESD79-3F. `A10` selects auto-precharge inside read and write commands, precharge-all inside precharge, and long/short inside ZQ calibration. The table below is the citation anchor for the block.

```text
CS_n=0:
  RAS_n  CAS_n  WE_n    Command / notes
    1      1      1     NOP
    0      1      1     ACT  (bank=BA, address=row)
    1      0      1     RD   (bank=BA, A10=0, address=col)
    1      0      1     RDA  (bank=BA, A10=1, address=col)
    1      0      0     WR   (bank=BA, A10=0, address=col)
    1      0      0     WRA  (bank=BA, A10=1, address=col)
    0      1      0     PRE  (bank=BA, A10=0)
    0      1      0     PREA (A10=1, bank don't-care)
    0      0      1     REF  (all-bank refresh)
    0      0      0     MRS  (bank=MR index, address=MR data)
    1      1      0     ZQCS (A10=0)
    1      1      0     ZQCL (A10=1)

CS_n=1:  NOP / deselect
```

: Table 2.22.3: DDR3 command truth table (JESD79-3F)

For `OP_MRS`, the MR data is carried on `cmd_row_i` rather than `cmd_col_i` because DDR3 mode-register payloads can need bit 10, which a 10-bit column field would truncate.

### Marking against pumice

Most of the DDR3 table is inherited unchanged from pumice's DDR2 formatter. The new encodings relative to pumice are:

| Opcode | Status | Reason |
|---|---|---|
| `OP_ZQCL` | MODIFIED | DDR3 adds ZQ calibration long; pumice defined the opcode but drove NOP |
| `OP_ZQCS` | MODIFIED | DDR3 adds ZQ calibration short; pumice defined the opcode but drove NOP |
| `OP_PREA` | MODIFIED | DDR3 precharge-all uses the same RAS/CAS/WE as precharge with A10=1 |

: Table 2.22.4: MODIFIED command encodings versus pumice

### LPDDR3 CA-bus encoding

For `memtype_i == MEMTYPE_LPDDR3`, the formatter builds a 20-bit CA word bit-exact to JESD209-2F Table 60:

```text
w_lpddr2_ca[9:0]   = CA[9:0]  on the rising edge
w_lpddr2_ca[19:10] = CA[9:0]  on the falling edge
packed form:        {w_ca_f, w_ca_r}
```

The word is driven on `dfi_address_o[19:0]`; `ras_n`, `cas_n`, and `we_n` stay idle, and chip-select is asserted on phase 0. The CA encoding covers ACT, RD/RDA, WR/WRA, PRE/PREA, REF, REFPB, and MRW. MRW carries the MR index in `cmd_row_i[13:8]` and MR data in `cmd_row_i[7:0]` because the LPDDR3 MR range exceeds the 3-bit bank port.

Key CA field mappings:

```text
ACT:    CA0r=0, CA1r=1 ; bank -> CA7r..CA9r ; row[12:8] -> CA2r..CA6r
        row[7:0] -> CA0f..CA7f ; row[13] -> CA8f ; row[14] -> CA9f
RD/RDA: CA0r=1, CA1r=0, CA2r=1 ; bank -> CA7r..CA9r ; col[2:1] -> CA5r,CA6r
        AP -> CA0f ; col[11:3] -> CA1f..CA9f
WR/WRA: CA0r=1, CA1r=0, CA2r=0 ; bank -> CA7r..CA9r ; col[2:1] -> CA5r,CA6r
        AP -> CA0f ; col[11:3] -> CA1f..CA9f
PRE:    CA0r=1, CA1r=1, CA2r=0, CA3r=1 ; bank -> CA7r..CA9r
PREA:   CA0r=1, CA1r=1, CA2r=0, CA3r=1, CA4r=1
REF:    CA0r=0, CA1r=0, CA2r=1, CA3r=1
REFPB:  CA0r=0, CA1r=0, CA2r=1, CA3r=0
MRW:    MA[5:0] -> CA4r..CA9r ; MA[7:6] -> CA0f,CA1f ; OP[7:0] -> CA2f..CA9f
NOP:    CA0r..CA3r = 1
```

### ODT

`dfi_odt_o` is declared on the interface but is driven to zero for all commands in this implementation. The ODT pin is part of the DFI command group per the HAS, but scoria's PHY target does not require dynamic ODT control at the formatter; any ODT behavior is handled elsewhere or left inactive.

### Phase placement

Reads are placed on `rd_phase_i`, writes on `wr_phase_i`, and all other commands on phase 0. This matches the a7ddrphy rdphase/wrphase contract. Phases that do not carry the active command are driven as NOP.

## FSM policy

There is no FSM. The formatter is combinational encoding followed by a single registered pipeline stage. `cmd_ready_o` is tied high after reset.

## Timing

The formatter introduces one `mc_clk` cycle of latency from decoded inputs to DFI outputs. All command-to-command spacing is enforced upstream by the scheduler.

## Notes

- `OP_SREFE`, `OP_SREFX`, and `OP_DPDE` are not encoded here. They fall through the default arm and are driven as NOP on the DFI command pins; the real behavior is CKE/power-down sequencing, which is described in `ch02_blocks/26_dormant_powerdown_and_pack.md`.
- `OP_REFPB` is LPDDR3-only and uses the same CA encoding branch as the per-bank refresh case.
- The module comment header still names DDR2/LPDDR2 because the formatter body was inherited from pumice and the file was not renamed; the actual `memtype_e` values and encoding targets are DDR3 and LPDDR3.

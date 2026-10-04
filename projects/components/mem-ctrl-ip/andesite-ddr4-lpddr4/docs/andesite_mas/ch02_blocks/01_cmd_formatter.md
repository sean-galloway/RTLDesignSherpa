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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Command Formatter (`andesite_dfi_cmd_formatter`)

**Module:** `andesite_dfi_cmd_formatter.sv`
**Location:** `rtl/fub/` (planned)
**Category:** FUB
**Parent:** `dfi_cmd_path` / `dfi_layer`
**Status:** specified — no RTL exists (HAS v0.1 posture)

---

## Purpose

`dfi_cmd_formatter` is the last combinational step before the command stream hits the DFI pins. It takes the scheduler's abstract opcode and address fields and turns them into the wire pattern the DRAM expects: ACT_n, RAS_n, CAS_n, WE_n, chip-select, bank, bank-group and address for DDR4; the 6-bit double-data-rate CA bus for LPDDR4. The block doesn't sequence anything — it just encodes. Sequence lives in the scheduler and the init_sequencer, the same split pumice and scoria used.

The andesite delta is the DDR4 fifth pin and bank-group wiring, plus a NEW LPDDR4 CA submodule that sits beside the DDR4 path so each stays reviewable on its own. Parity generation also lands here, gated by init and returned on `dfi_alert_n`.

## Parameters

| Parameter | Type | Range | Default | Meaning | Source |
|---|---|---|---|---|---|
| `ADDR_WIDTH` | int | 18 | 18 | row/column address width presented to formatter | design point |
| `BANK_WIDTH` | int | 2 | 2 | bank address width (DDR4); 3 for LPDDR4 | design point |
| `BG_WIDTH` | int | 2 | 2 | bank-group width (DDR4 only) | design point |
| `RANK_WIDTH` | int | 1 | 1 | rank/chip-select width | design point |
| `CA_WIDTH` | int | 6 | 6 | LPDDR4 CA bus width | JESD209-4 |
| `PARITY_EN` | bit | 0/1 | 0 | CA parity generation enable (dynamic after init) | CSR |

: Table 2.1: Command formatter parameters

## Interface

| Signal | Direction | Width | Description |
|---|---|---|---|
| `clk` | in | 1 | controller clock; DFI 1:4 gear ratio means one command beat per four DRAM clocks `§TBC(TASK-005)` |
| `rst_n` | in | 1 | active-low synchronous reset |
| `op_i` | in | 4 | internal opcode: `OP_NOP`, `OP_ACT`, `OP_RD`, `OP_WR`, `OP_PRE`, `OP_REF`, `OP_ZQ`, `OP_MRS`, plus `OP_MPC` for LPDDR4 |
| `bank_i` | in | `BANK_WIDTH` | bank address from the mapper |
| `bg_i` | in | `BG_WIDTH` | bank-group address from the mapper (DDR4) |
| `row_i` | in | `ADDR_WIDTH` | row address, valid with `OP_ACT` |
| `col_i` | in | `ADDR_WIDTH` | column address, valid with `OP_RD`/`OP_WR` |
| `rank_i` | in | `RANK_WIDTH` | chip select / rank target |
| `memtype_i` | in | 3 | family memtype enum from `andesite_pkg` |
| `parity_en_i` | in | 1 | enable CA parity generation after init |
| `mpc_op_i` | in | 6 | LPDDR4 MPC opcode, valid with `OP_MPC` |
| `dfi_act_n` | out | 1 | DFI 4.0 activate command pin `§TBC(TASK-005)` |
| `dfi_ras_n` | out | 1 | DFI row-address strobe command pin |
| `dfi_cas_n` | out | 1 | DFI column-address strobe command pin |
| `dfi_we_n` | out | 1 | DFI write-enable command pin |
| `dfi_bank` | out | `BANK_WIDTH` | DFI bank address |
| `dfi_bg` | out | `BG_WIDTH` | DFI bank-group address (DDR4) |
| `dfi_address` | out | `ADDR_WIDTH` | DFI address bus |
| `dfi_cs_n` | out | `RANK_WIDTH` | DFI chip-select, active low |
| `dfi_cke` | out | `RANK_WIDTH` | DFI clock-enable |
| `dfi_parity_in` | out | 1 | DFI CA parity output to PHY `§TBC(TASK-005)` |
| `dfi_alert_n` | in | 1 | DFI alert return from PHY: parity or command error `§TBC(TASK-005)` |
| `ca_o` | out | `CA_WIDTH` | LPDDR4 CA bus to PHY, double-data-rate |
| `ca_valid_o` | out | 1 | LPDDR4 CA two-cycle command valid |

: Table 2.2: Command formatter ports

## Microarchitecture internals

### DDR4 command truth table

The DDR4 encoding follows the JESD79-4 four-pin command convention, with `ACT_n` as the fifth pin for activate. The truth table is the citation anchor for the block; don't renumber it.

```text
CS_n=0:
  ACT_n  RAS_n  CAS_n  WE_n    Command
    1      1      1      1     NOP
    0      1      1      1     ACT
    1      1      0      1     RD
    1      1      0      0     WR
    0      0      0      0     MRS
    0      0      0      1     REF
    1      0      1      0     PRE     (A10=0: PRE per bank; A10=1: PREA)
    1      1      1      0     ZQ      (A10=0: ZQCS; A10=1: ZQCL)

RD/WR auto-precharge variants (RDA/WRA) reuse the RD/WR pin encoding with
the AP address bit set (A10=1) -- the auto-precharge select is an address
input, not a pin variant, so the kmap book treats AP as a table input.

CS_n=1: DES (deselect)

CKE-qualified entries: SRE (self-refresh entry), SRX (self-refresh exit)
LPDDR4-only command: MPC (multipurpose command), see CA submodule below
```

: Table 2.3: DDR4 command truth table (citation anchor). Pin encodings are
stated per the JESD79-4 command-truth-table convention and are confirmed at
the HAS Q1 cold-storage read before RTL; the kmap book's DDR4 table (andesite TASK-004)
minimizes its qualifier SOPs from exactly this anchor.

A10 inside `PRE` selects precharge-all (`PREA`); A10 inside `ZQ` selects
`ZQCL` versus `ZQCS`; A10 inside `RD`/`WR` selects the auto-precharge
variants (`RDA`/`WRA`). During `ACT`, A10 is not a variant-select bit; it
carries row address bit 10 like any other activate address pin. `BG0` and
`BG1` ride the address bus during `ACT`.

### Activate form

The activate command packs the row and bank-group fields onto the DFI address and bank-group outputs:

```text
{ ACT_n=0, dfi_bank[1:0]=BA[1:0], dfi_bg[1:0]=BG[1:0], dfi_address[17:0]=row[17:0] }
```

: Figure 2.1: DDR4 activate field packing

### CA parity

Parity is generated in the formatter from the command pins plus the address/bank/bank-group bits that travel on the same DRAM clock edge. The insertion point is the registered pipeline stage that drives `dfi_parity_in`. Generation only runs when `parity_en_i` is asserted; that bit is cleared at reset and set by the init_sequencer once the MR sequence has programmed parity mode. This is the same init-side enable dependency scoria used for DLL-related gating.

A parity error returned on `dfi_alert_n` is a DFI 4.0 alert event `§TBC(TASK-005)`. The formatter logs the raw `dfi_alert_n` pulse; the sequencer owns the recovery policy and the MR re-programming path.

### NEW LPDDR4 CA submodule

LPDDR4 uses a 6-bit double-data-rate CA bus, two cycles per command. The submodule takes the internal opcode, bank, and MPC/MRW payload and emits the two-cycle CA beat pair. Each command is therefore a 12-bit symbol split across two half-rates. The exact CA encodings are pinned by the kmap book's LPDDR4 CA-bus table in `docs/kmaps/generated/` (andesite TASK-004); this page does not fabricate them.

```text
Command class -> CA encoding source
  NOP      -> kmap table
  ACT      -> kmap table
  RD       -> kmap table
  WR       -> kmap table
  MPC      -> kmap table
  MRW      -> kmap table
  MRR      -> kmap table
  REFab    -> kmap table
  REFpb    -> kmap table (bank carried in command)
```

: Table 2.4: LPDDR4 CA encoding placeholder (kmap book anchor)

The submodule is combinational encoding plus the two-cycle registered shifter. The first cycle drives `ca_o` with CA[5:0]; the second cycle drives `ca_o` with CA[11:6]. `ca_valid_o` marks both cycles.

## FSM policy

There is no FSM. The formatter is combinational encoding followed by a registered pipeline stage; the LPDDR4 submodule adds a two-cycle shift register for the second CA beat. This is the pumice/scoria precedent: encode here, sequence elsewhere.

## Timing

All command-to-command spacing is enforced upstream by `global_timers` and the scheduler. The formatter introduces one controller-clock pipeline delay from decoded inputs to DFI outputs. LPDDR4 commands consume two controller clocks on the CA bus, so the downstream command accept handshake reflects that stretch. Specific JEDEC values (`tCCD_L`, `tCCD_S`, `tMRD`, `tMOD`, the ODT latency family) are runtime CSRs, initialised from the JESD79-4/JESD209-4 speed bin at CSR-derivation time (HAS Ch 5; numeric constants are HAS open question Q1).

## Notes

- Keep the DDR4 and LPDDR4 paths separate at the top level of this FUB. Merging them makes review harder and gains nothing — the memtype select is one mux at the output boundary.
- `dfi_alert_n` is asynchronous at the PHY; sample it synchronously inside this block and export a one-cycle pulse.
- LPDDR4's REFpb command names the bank explicitly in the CA encoding, which is why the refresh controller's per-bank scheduling lands naturally on this path.

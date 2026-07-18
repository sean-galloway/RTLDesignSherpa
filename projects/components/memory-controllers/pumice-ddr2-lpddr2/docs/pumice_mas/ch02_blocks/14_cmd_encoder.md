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

# DFI Command Formatter (`dfi_cmd_formatter` + `dfi_signal_pack`)

**Module:** `dfi_cmd_formatter.sv` (command decode) / `dfi_signal_pack.sv` (final DFI pipe stage)
**Location:** `rtl/fub/`
**Category:** FUB
**Parent macro:** `pumice_dfi_layer`
**Status:** Implemented (DDR2 truth table + bit-exact LPDDR2 CA-bus encoding; both memtypes functional)

> **Replaces the retired command encoder.** The original `cmd_encoder_fub` (with
> its `ddr2_cmd_encoder` / `lpddr2_cmd_encoder` generate-branch sub-modules and a
> separate `odt_ctrl_fub`) is gone. The live design is `dfi_cmd_formatter.sv` — a
> single module with a runtime `memtype_i` branch (not an elaboration-time
> generate) — followed by `dfi_signal_pack.sv`, the final registered DFI-bus
> pipeline stage.
>
> **LPDDR2 is now fully implemented.** The retired chapter listed LPDDR2 as
> "deferred to v2." The live formatter builds the bit-exact JESD209-2F Table 60
> CA-bus word for every command; the transcription lives in
> `rtl/LPDDR2_CA_ENCODING.md`, and the DV BFM (`lpddr_ca.py`) encodes/decodes
> against the identical layout.
>
> **ODT is absorbed here.** There is no standalone ODT block (see the retired
> ODT chapter). `dfi_cmd_formatter` drives `dfi_odt_o`; the DDR2 ODT rule follows
> from the same truth table. In v1 `dfi_odt_o` is driven to 0 (the decode leaves
> `w_p0_odt` at its NOP default for every op); the JEDEC ODT-timing hooks live in
> `mode_register`'s `odt_o` decode.

---

## Purpose

`dfi_cmd_formatter` translates the scheduler's abstract command — `(cmd_op,
rank, bank, row, col, len)` plus an implicit auto-precharge encoded in the op
(RDA/WRA vs RD/WR) — into wire-level DFI v2.1 control-bus signals, packed across
`DFI_RATE` phases. For DDR2 it drives the classic `{ras_n, cas_n, we_n}` strobes
plus `dfi_address` / `dfi_bank`; for LPDDR2 it packs the multiplexed 10-bit CA
bus (two edges = a flat 20-bit word) onto `dfi_address`.

`dfi_signal_pack` is the final pipeline register on the DFI v2.1 bus. It latches
the formatter's command bus together with the write/read data-enable signals and
drives reset-safe NOP values during reset. It owns `dfi_dram_clk_disable`
(currently held 0).

Both modules run in the DFI clock domain inside `pumice_dfi_layer` (see
[the DFI layer / gearing chapter](15_gear_dfi.md)); the formatter is instantiated
via `pumice_dfi_cmd_path`.

---

## Synthesis Parameters (`dfi_cmd_formatter`)

| Parameter          | Default | Effect                                                          |
|--------------------|---------|-----------------------------------------------------------------|
| `NUM_RANKS`        | 1       | Width of the per-rank `dfi_cs_n` / `dfi_odt` output             |
| `NUM_BANKS`        | 8       | Bank-field width (`BKW`)                                        |
| `ROW_WIDTH`        | 14      | Row operand width (also carries DDR2 MR data and LPDDR2 MRW field) |
| `COL_WIDTH`        | 10      | Column operand width                                           |
| `BURST_LEN_WIDTH`  | 8       | `cmd_len_i` width (currently unused — tied into `unused_v1`)     |
| `DFI_RATE`         | 2       | Phases per DFI-layer word; sets the multi-phase bus widths       |
| `DFI_ADDR_WIDTH`   | 14      | Per-phase address width; the LPDDR2 CA word needs `DFI_ADDR_BUS_W >= 20` |
| `DFI_BANK_WIDTH`   | 3       | Per-phase bank width                                           |
| `DFI_CTRL_WIDTH`   | 1       | Per-phase width of each ras/cas/we strobe                      |
| `DFI_CS_WIDTH`     | NUM_RANKS | Per-phase CS/ODT width                                        |

The multi-phase bus widths (`DFI_*_BUS_W = DFI_*_WIDTH * DFI_RATE`) are derived.
`memtype_i` is a **runtime input** (`MEMTYPE_DDR2` / `MEMTYPE_LPDDR2`), not a
parameter — both encoding paths are synthesized and the branch is selected live,
so one bitstream can serve either family.

---

## Command Interface and Runtime Phase Placement

The formatter takes a valid/ready command handshake from the DFI-layer command
FIFO:

| Signal          | Width           | Description                                     |
|-----------------|-----------------|-------------------------------------------------|
| `cmd_valid_i`   | 1               | Command present                                 |
| `cmd_ready_o`   | 1               | Always 1 (registered) — formatter never stalls  |
| `cmd_op_i`      | `dram_op_e`     | The chosen operation                            |
| `cmd_rank_i`    | RKW             | Target rank (selects the active CS_n)           |
| `cmd_bank_i`    | BKW             | Target bank (MR index for MRS)                  |
| `cmd_row_i`     | ROW_WIDTH       | Row (ACT); DDR2 MR data; LPDDR2 packed MRW field |
| `cmd_col_i`     | COL_WIDTH       | Column (RD/WR)                                  |
| `cmd_len_i`     | BURST_LEN_WIDTH | Burst length (reserved; unused in v1)           |
| `rd_phase_i`    | PHW             | DFI sub-phase carrying the READ command         |
| `wr_phase_i`    | PHW             | DFI sub-phase carrying the WRITE command        |

`rd_phase_i` / `wr_phase_i` are CSR-driven (`DFI_PHASE` CSR). The decoded command
is placed on `wr_phase` for WR/WRA, `rd_phase` for RD/RDA, and phase 0 for
everything else. This matches a PHY that consumes a per-command rdphase/wrphase
off the DFI bus. Defaults are 0, which reproduces the legacy "everything on phase
0" behavior — notably the LiteDRAM a7ddrphy takes the command on phase 0 and
applies its rdphase internally, so on the board target these stay 0. (See the
gearing chapter §"DFI_PHASE CSR".)

---

## DDR2 Encoding Branch

For `memtype_i == MEMTYPE_DDR2`, a combinational block builds the phase-0
command fields (`w_p0_*`). The default is an all-deselected NOP; when a command
is valid, `w_p0_cs_n` is set to the active-rank mask (`w_active_rank_mask`, bit
`r` low for the target rank) and the strobes/address are driven per the JEDEC
JESD79-2 truth table (transcribed verbatim from the RTL):

| Op       | `cs_n`      | `ras_n` | `cas_n` | `we_n` | `bank` | `address`                          |
|----------|-------------|---------|---------|--------|--------|-------------------------------------|
| `OP_NOP` | active mask | 1       | 1       | 1      | 0      | 0                                  |
| `OP_ACT` | active mask | 0       | 1       | 1      | bank   | row                                |
| `OP_RD`  | active mask | 1       | 0       | 1      | bank   | col (A10 = 0)                      |
| `OP_RDA` | active mask | 1       | 0       | 1      | bank   | col with bit 10 set (auto-PRE)     |
| `OP_WR`  | active mask | 1       | 0       | 0      | bank   | col (A10 = 0)                      |
| `OP_WRA` | active mask | 1       | 0       | 0      | bank   | col with bit 10 set (auto-PRE)     |
| `OP_PRE` | active mask | 0       | 1       | 0      | bank   | 0 (A10 = 0, single-bank)           |
| `OP_PREA`| active mask | 0       | 1       | 0      | 0      | bit 10 set (all-bank)              |
| `OP_REF` | active mask | 0       | 0       | 1      | 0      | 0                                  |
| `OP_MRS` | active mask | 0       | 0       | 0      | MR idx | MR data from `cmd_row_i`            |

`cs_n` is per-rank: bit `r` is 0 for the selected rank, 1 elsewhere; all-1 is an
all-deselected NOP. The A10 auto-precharge bit is set by OR-ing `1 << 10` into
the address for RDA/WRA, and doubles as the all-bank flag for PREA.

**MRS carries data on the ROW field, not the column.** The RTL comment is
explicit: MR0 = 0x532 needs bit 10 (tWR[1]), which a `COL_WIDTH` (10-bit) field
would truncate — so the formatter reads MR data from `cmd_row_i` (ROW_WIDTH) and
the MR index from `cmd_bank_i`. This matches `init_sequencer`, which drives MR
data on `init_cmd_row_o`.

Unhandled DDR2-irrelevant ops (`OP_REFPB`, `OP_ZQCS`/`ZQCL`, self-refresh entry/
exit) fall through the `default` arm and emit NOP — they are driven via CKE / a
separate sequencer, not the strobe truth table.

---

## LPDDR2 Encoding Branch (bit-exact JESD209-2F Table 60)

LPDDR2 has no `ras_n`/`cas_n`/`we_n`. The command AND a scrambled address are
multiplexed onto a 10-bit CA bus over two clock edges (rising `r`, falling `f`),
carried on the DFI bus as a flat 20-bit word. The formatter builds two 10-bit
half-words `w_ca_r` / `w_ca_f` and concatenates them:

```systemverilog
assign w_lpddr2_ca = {w_ca_f, w_ca_r};   // [19:10] = falling, [9:0] = rising
```

This is the exact layout locked in `rtl/LPDDR2_CA_ENCODING.md` and enforced by a
round-trip conformance test against the DV decoder (`lpddr_ca.py`). Per JEDEC,
any other bit ordering is prohibited, so bit-exactness is a spec requirement.

**Command decode** is by the rising-edge opcode bits {CA0r, CA1r, CA2r, CA3r},
transcribed from the RTL `unique case`:

| Op                | Rising opcode bits set                     | Payload placement |
|-------------------|--------------------------------------------|-------------------|
| `OP_ACT`          | CA1r = 1                                   | bank → CA7r..CA9r; row hi R8..R12 → CA2r..CA6r; row lo R0..R7 → CA0f..CA7f; R13 → CA8f; R14 → CA9f |
| `OP_RD` / `OP_RDA`| CA0r = 1, CA2r = 1 (read)                  | bank → CA7r..CA9r; C1,C2 → CA5r,CA6r; AP → CA0f; C3..C11 → CA1f..CA9f |
| `OP_WR` / `OP_WRA`| CA0r = 1, CA2r = 0 (write)                 | same column/bank/AP placement as read |
| `OP_PRE`          | CA0r=1, CA1r=1, CA3r=1 (AB=0)              | bank → CA7r..CA9r |
| `OP_PREA`         | CA0r=1, CA1r=1, CA3r=1, CA4r=1 (AB=1)      | bank don't-care |
| `OP_REF`          | CA2r=1, CA3r=1 (all-bank)                  | — |
| `OP_REFPB`        | CA2r=1 (per-bank; CA3r=0)                  | bank implied by device counter |
| `OP_MRS` (MRW)    | all opcode bits 0                          | MA0..MA5 → CA4r..CA9r; MA6,MA7 → CA0f,CA1f; OP0..OP7 → CA2f..CA9f |
| default (NOP)     | CA0r=CA1r=CA2r=CA3r=1                       | — |

Auto-precharge is `w_ca_ap = (op == OP_RDA) || (op == OP_WRA)`, placed on CA0f.
C0 is implied 0 and never transmitted (only C1..C11 ride the bus). Row/column/
bank are zero-extended (`w_row15`, `w_col12`) so wider geometries (R14, C10, C11)
light up their reserved pins cleanly.

**MRW field packing.** LPDDR2 mode-register addresses reach MR63 (MA[5:0]), which
a 3-bit bank port cannot express. The scheduler therefore carries the MRW fields
in the ROW request as `{MA[5:0], OP[7:0]}` — `w_mr_ma = {2'b0, cmd_row_i[13:8]}`,
`w_mr_op = cmd_row_i[7:0]` — matching `init_sequencer`'s `mrw_row()` packing.
MA[7:6] are 0 (MR <= 63).

---

## Multi-Phase Packing and CS_n

After the decode, a combinational stage packs the command into the multi-phase
buses (`w_dfi_*`). Every phase starts at NOP (cs_n = 1, ras/cas/we = 1); then:

- **DDR2:** the decoded `w_p0_*` fields are placed on the target phase
  `w_cmd_phase` (rd_phase for reads, wr_phase for writes, phase 0 otherwise); the
  other phases stay NOP.
- **LPDDR2:** the whole 20-bit CA word is written to `w_dfi_address[19:0]` (low
  bits), ras/cas/we stay idle, and `dfi_cs_n` is asserted for the target rank on
  phase 0 when the op is not NOP. The two CA edges are already inside the word,
  so there is no per-DFI-phase command placement for LPDDR2.

The active-rank CS_n mask is built once (`w_active_rank_mask`): bit `r` = 0 when
`r == cmd_rank_i`, else 1. For `NUM_RANKS == 1` only bit 0 exists.

---

## `dfi_signal_pack` — Final Registered DFI Stage

`dfi_signal_pack` is a pure one-cycle registered pipeline. It latches the
formatter's command bus plus the data-enable/mask signals from the write/read
serializers and drives them to the PHY the next DFI cycle. Its value is the
reset-safe defaults it guarantees during reset / before first issue:

| Output                     | Reset value | Meaning                              |
|----------------------------|-------------|--------------------------------------|
| `dfi_cs_n_o`               | all-1       | all-deselected                       |
| `dfi_ras_n_o/cas_n_o/we_n_o` | all-1     | NOP                                  |
| `dfi_cke_o`                | 0           | DRAM held CKE-low until init          |
| `dfi_odt_o`                | 0           | ODT off                              |
| `dfi_wrdata_en_o` / `dfi_rddata_en_o` | 0 | no data movement                     |
| `dfi_wrdata_mask_o`        | all-1       | mask all bytes (write nothing)       |
| `dfi_dram_clk_disable_o`   | 0           | clock enabled (power-state TODO)     |

It owns `dfi_dram_clk_disable` for a future power-state machine (held 0 today).
Phase staggering and CKE power-down driving are v2 TODOs noted in the RTL header;
today it is a transparent width-preserving flop.

---

## Interface (`dfi_cmd_formatter` outputs)

| Signal          | Width           | Description                          |
|-----------------|-----------------|--------------------------------------|
| `dfi_address_o` | DFI_ADDR_BUS_W  | DDR2 row/col operand per phase; LPDDR2 flat CA word |
| `dfi_bank_o`    | DFI_BANK_BUS_W  | Per-phase bank (DDR2)                |
| `dfi_cas_n_o`   | DFI_CTRL_BUS_W  | Per-phase CAS strobe                 |
| `dfi_ras_n_o`   | DFI_CTRL_BUS_W  | Per-phase RAS strobe                 |
| `dfi_we_n_o`    | DFI_CTRL_BUS_W  | Per-phase WE strobe                  |
| `dfi_cs_n_o`    | DFI_CS_BUS_W    | Per-phase per-rank chip-select       |
| `dfi_odt_o`     | DFI_CS_BUS_W    | Per-phase per-rank ODT (0 in v1)     |

All outputs are strict-flopped; `dfi_signal_pack` widens/relatches them onto the
PHY pins unchanged.

---

## Timing Budget

The formatter is combinational decode into a single output flop; `dfi_signal_pack`
adds one more flop. The worst path is the LPDDR2 ACT with full row-bit spreading
across CA0r/CA0f (bank + 5 rising row bits + 8 falling row bits), which is a few
LUT levels feeding the output register — well within the DFI clock budget. The
formatter is not the controller's critical path; that is the arbiter upstream.

---

## Verification Notes (cocotb test plan)

| Scenario                                                                          | What it proves                          |
|-----------------------------------------------------------------------------------|-----------------------------------------|
| DDR2 ACT bank 3 row 0x1234 → `{ras,cas,we}={0,1,1}`, address=0x1234, bank=3       | DDR2 ACT truth-table row                |
| DDR2 RDA bank 3 col 0x40 → `{ras,cas,we}={1,0,1}`, address bit 10 set             | DDR2 auto-precharge via A10             |
| DDR2 PREA → `{ras,cas,we}={0,1,0}`, address bit 10 set                            | DDR2 all-bank precharge via A10         |
| DDR2 MRS MR0=0x532 → MR data on address (bit 10 present, not truncated)           | MRS data on ROW field                   |
| LPDDR2 ACT bank 3 row 0x1234 → `w_lpddr2_ca` bit-exact vs `lpddr_ca.py` decode    | LPDDR2 ACT CA packing                   |
| LPDDR2 WRA bank 3 col 0x40 → AP bit (CA0f) set                                     | LPDDR2 auto-precharge via CA            |
| LPDDR2 REFpb (CA2r=1, CA3r=0) vs REFab (CA2r=1, CA3r=1)                            | LPDDR2 refresh CA decode                |
| LPDDR2 MRW MR63 → MA/OP packed on CA4r..CA9r / CA0f.. per Table 60                 | LPDDR2 MRW field packing                |
| Multi-rank ACT rank 1 → `dfi_cs_n` bit 1 low, bit 0 high                          | Per-rank CS_n mask                      |
| rd_phase=1 → RD command lands on DFI phase 1, other phases NOP                    | Runtime phase placement                 |
| NOP / `!cmd_valid` → all-deselected (cs_n all-1), strobes all-1                   | Idle pattern                            |
| Reset → `dfi_signal_pack` drives cs_n=1, cke=0, wrdata_mask=all-1                 | Reset-safe NOP defaults                 |

---

## Open Questions / Future Work

- **ODT driving.** `dfi_odt_o` is held 0 in v1 (the decode leaves the ODT default
  at NOP). Multi-rank DDR2 needs the JEDEC cross-termination window (ODT-high on
  the non-accessed rank during a read, on the accessed rank during a write). The
  hooks exist (`mode_register.odt_o` decodes the DDR2 MR1 ODT bits); wiring the
  timed ODT window through the formatter is future work — see the absorbed ODT
  chapter.
- **`cmd_len_i` unused.** The burst-length input is reserved (tied into
  `unused_v1`); burst geometry is handled by the data-path serializers, so the
  formatter does not need it today.
- **Phase staggering / clk-disable.** `dfi_signal_pack` is a plain relatch;
  per-phase output staggering and `dfi_dram_clk_disable` driving (for power-down)
  are v2 items noted in the RTL header.
- **LPDDR2 BL16.** `mode_register.bl_o` is 4-bit and clips BL16 to BL8; only
  BL4/BL8 are wired end-to-end. Widening the burst path is a separate item.

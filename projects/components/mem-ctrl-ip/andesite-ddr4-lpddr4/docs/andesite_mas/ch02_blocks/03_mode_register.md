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

# Mode Register (`andesite_mode_register`)

**Module:** `andesite_mode_register.sv`
**Location:** `rtl/fub/` (planned)
**Category:** FUB
**Parent:** `init_sequencer` / `dfi_cmd_formatter` / training interfaces
**Status:** specified — no RTL exists (HAS v0.1 posture)

---

## Purpose

`mode_register` holds the MR images per memtype and feeds them to the formatter in the order the init_sequencer demands. It also services runtime MR reads and writes — firmware training paths re-touch MR3 for MPR access and MR1 for write leveling, and the LPDDR4 MR set gets similar treatment during CA and WDQ training. The block is a set of registers plus a mux; it doesn't own the programming order. Order is the init_sequencer's property, and this page cites that split rather than duplicating it.

## Parameters

| Parameter | Type | Range | Default | Meaning | Source |
|---|---|---|---|---|---|
| `DDR4_MR_COUNT` | int | 7 | 7 | MR0-MR6 for DDR4 | JESD79-4 |
| `LPDDR4_MR_COUNT` | int | TBD | TBD | LPDDR4 MR space; exact count per JESD209-4 | Q1 |
| `DATA_WIDTH` | int | 16 | 16 | MR payload width (max across both memtypes) | design point |
| `RANK_WIDTH` | int | 1 | 1 | rank select for per-rank MR images | design point |

: Table 2.5: Mode register parameters

## Interface

| Signal | Direction | Width | Description |
|---|---|---|---|
| `clk` | in | 1 | controller clock |
| `rst_n` | in | 1 | active-low synchronous reset |
| `memtype_i` | in | 3 | family memtype enum from `andesite_pkg` |
| `rank_i` | in | `RANK_WIDTH` | rank target for MR access |
| `wr_en_i` | in | 1 | write strobe from init_sequencer or firmware |
| `wr_addr_i` | in | 3 | MR index (0-6 for DDR4; LPDDR4 index per JESD209-4) |
| `wr_data_i` | in | `DATA_WIDTH` | MR write payload |
| `rd_en_i` | in | 1 | read strobe for firmware readback |
| `rd_addr_i` | in | 3 | MR index for readback |
| `rd_data_o` | out | `DATA_WIDTH` | MR readback data |
| `mr_sel_o` | out | 3 | MR index to formatter for MRS/MRW command |
| `mr_data_o` | out | `DATA_WIDTH` | MR payload to formatter for MRS/MRW command |
| `mpr_page_o` | out | 2 | MR3 MPR page select to `rdlvl_ifc` |
| `fgr_factor_o` | out | 2 | MR3 FGR 1x/2x/4x select to `refresh_ctrl` |
| `rtt_nom_o` | out | 3 | MR1 RTT_NOM value to `odt_ctrl` |
| `rtt_wr_o` | out | 3 | MR2 RTT_WR value to `odt_ctrl` |
| `rtt_park_o` | out | 3 | MR5 RTT_PARK value to `odt_ctrl` |
| `rd_dbi_en_o` | out | 1 | MR5 read DBI enable to datapath |
| `wr_dbi_en_o` | out | 1 | MR5 write DBI enable to datapath |
| `ca_parity_lat_o` | out | 2 | MR5 CA parity latency/mode to formatter |
| `wrlvl_en_o` | out | 1 | MR1 write-leveling enable to `wrlvl_ifc` |
| `lpddr4_odt_o` | out | TBD | LPDDR4 ODT/DQ-ODT programming to PHY/odt_ctrl | JESD209-4 |

: Table 2.6: Mode register ports

## Microarchitecture internals

### DDR4 MR semantics

The DDR4 mode-register set expands scoria's four registers to seven. The table below is semantics-binding; bit positions per JESD79-4 are confirmed at Q1 cold-storage read.

| Register | Fields (semantics-binding) |
|---|---|
| MR0 | Burst length (fixed 8 or on-the-fly 4/8), read burst type (sequential/interleaved), CAS latency select, DLL reset bit, write recovery |
| MR1 | DLL enable, additive latency (AL), RTT_NOM, write-leveling enable, TDQS enable, output driver impedance |
| MR2 | CAS write latency (CWL), RTT_WR, write CRC mode bits (inert this edition per HAS Ch 3.1), LP ASR |
| MR3 | MPR operation and page select, FGR refresh factor (1x/2x/4x), gear-down mode, MPR read format |
| MR4 | Temperature status, preamble, CAL (command address latency) |
| MR5 | Read DBI enable, write DBI enable, RTT_PARK, data-mask enable, CA parity latency/mode (A[2:0]), parity persistent-error (A9), parity error status (A4) |
| MR6 | VrefDQ training range and value, tCCD_L select |

: Table 2.7: DDR4 MR0-MR6 field semantics

Bit map per JESD79-4 MRn (confirmed at Q1 cold-storage read); the maps above are semantics-binding.

### LPDDR4 MR set

LPDDR4 doesn't use the same MRS command as DDR4. Its MRs are written by MRW over the 6-bit CA bus and read back by MRR. The page owns the LPDDR4 write image alongside DDR4's. LPDDR4's MRs cover ODT and DQ-ODT programming, drive strength, CA training patterns, refresh-related bits, and the vendor-specific area. Exact LPDDR4 MR bit maps per JESD209-4 (Q1). The coupling is looser than DDR4's because termination is MR-programmed rather than ODT-pin driven, but the register-block structure is the same: one image per rank, one write port, one readback port.

### MR coupling table

| MR / Field | Consumer | What it controls |
|---|---|---|
| MR3 FGR select | `refresh_ctrl` | Refresh interval scaling: 1x, 2x or 4x |
| MR3 MPR page | `rdlvl_ifc` | MPR read-leveling page and format |
| MR2 RTT_WR | `odt_ctrl` | Write termination for DDR4 |
| MR5 RTT_PARK | `odt_ctrl` | Idle termination for DDR4 |
| MR5 RD/WR DBI | datapath (`dfi_rd_aligner`, `dfi_wr_serializer`) | Data Bus Inversion enable |
| MR5 CA parity | `dfi_cmd_formatter` | Parity latency and mode |
| MR1 write leveling | `wrlvl_ifc` | Write-leveling entry/exit |
| MR1 RTT_NOM | `odt_ctrl` | Nominal termination for DDR4 |
| MR2 CWL | datapath / scheduler | CAS write latency (value flows to write-data timing) |
| MR6 VrefDQ | `rdlvl_ifc` / firmware | VrefDQ training range and value |
| LPDDR4 ODT/DQ-ODT | PHY / `odt_ctrl` | LPDDR4 MR-programmed termination |

: Table 2.8: Mode-register coupling

## FSM policy

There is no FSM. The block is registers, a write port, a readback mux, and field fanout to the consumers above. Programming order is the init_sequencer's property (HAS Ch 3.2). Runtime MRW/MRR requests from firmware are single-cycle register updates; the formatter turns `mr_sel_o` and `mr_data_o` into the actual bus command.

## Timing

MR writes and reads complete in one controller clock. The formatter and sequencer enforce the JEDEC command intervals (`tMRD`, `tMOD`) around MRS and MRW commands. Those values are runtime CSRs, initialised from the JESD79-4/JESD209-4 speed bin at CSR-derivation time (HAS Ch 5; numeric constants are HAS open question Q1).

## Notes

- Keep the DDR4 and LPDDR4 image arrays in separate address spaces selected by `memtype_i`. Don't try to map them onto one flat array — the field widths and meanings differ enough that a unified map invites mistakes.
- The MR3 FGR factor and MPR page are the two fields most likely to be rewritten at runtime; expose them as named CSR fields even if the rest of the MR image is write-only at init.
- LPDDR4's MR-programmed termination means the `odt_ctrl` block is DDR4-scoped for this edition; the LPDDR4 ODT values still live here and fan out to the PHY configuration path.

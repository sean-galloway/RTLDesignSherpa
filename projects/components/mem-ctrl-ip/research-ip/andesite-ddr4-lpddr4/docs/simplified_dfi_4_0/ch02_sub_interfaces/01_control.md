# Control Interface

The control interface carries address, command and control signals from the MC to the PHY. The
PHY is responsible for preserving bit ordering and presenting the signals to the DRAM with the
delay defined by `tctrl_delay`. In frequency-ratio systems the control bus is phase-replicated with
`_pN` suffixes; the MC may issue commands on any phase.

Some signals are DRAM-type-specific. `dfi_reset_n` is used only by DDR3, DDR4 and LPDDR4.
`dfi_odt` is used by DDR2, DDR3, DDR4 and LPDDR3. For LPDDR2/3/4 the command encoding
pins (`dfi_act_n`, `dfi_ras_n`, `dfi_cas_n`, `dfi_we_n`), bank (`dfi_bank`), bank-group (`dfi_bg`) and
chip-ID (`dfi_cid`) must be held constant; the CA bus is mapped onto `dfi_address`.

## Control signals

| Signal | Width | Default | Direction | What it does |
| --- | --- | --- | --- | --- |
| `dfi_act_n` | 1 bit | - | MC -> PHY | Activate select; part of DRAM command encoding with ras/cas/we. Asserted for DDR4 ACT; polarity defines command. |
| `dfi_address` | DFI Address Width | - | MC -> PHY | Address bus. DDR4: column + lower row bits (A[13:0]); A[16:14] carried on ras/cas/we during ACT. LPDDR2/3: maps 20-bit DDR CA bus. LPDDR4: 6-bit SDR CA. |
| `dfi_bank` | DFI Bank Width | - | MC -> PHY | Bank address. PHY preserves bit ordering. Constant for LPDDR2/3/4. |
| `dfi_bg` | DFI Bank Group Width | - | MC -> PHY | DDR4 bank group. Constant for LPDDR2/3/4. |
| `dfi_cas_n` | DFI Control Width | 0x1 | MC -> PHY | Column address strobe; command encoding. During DDR4 ACT it carries row address bit A15. |
| `dfi_cid` | DFI Chip ID Width | 0 | MC -> PHY | Chip ID for 3D stacked (3DS) devices. Initializes to 0. Constant for LPDDR2/3/4. |
| `dfi_cke` | DFI CKE Width | 0x0/0x1 | MC -> PHY | Clock enable. MC drives in all phases. For LPDDR3/4 also enables DRAM output drivers during CA training. |
| `dfi_cs` | DFI Chip Select Width | 0x1 | MC -> PHY | Chip select; polarity matches memory signal. During LPDDR3/4 CA training it carries the calibration command on the trained rank. |
| `dfi_odt` | DFI ODT Width | 0x0 | MC -> PHY | On-die termination control. MC drives in all phases. |
| `dfi_ras_n` | DFI Control Width | 0x1 | MC -> PHY | Row address strobe; command encoding. During DDR4 ACT it carries row address bit A16. |
| `dfi_reset_n` | DFI Reset Width | 0x0/0x1 | MC -> PHY | DRAM reset. PHY preserves bit ordering. |
| `dfi_we_n` | DFI Control Width | 0x1 | MC -> PHY | Write enable; command encoding. During DDR4 ACT it carries row address bit A14. |

: DFI 4.0 control signals

## Command encoding on the control pins

For most DRAM types the command is encoded by the classic four pins:

| `dfi_act_n` | `dfi_ras_n` | `dfi_cas_n` | `dfi_we_n` | Typical command |
| --- | --- | --- | --- | --- |
| 1 | 0 | 1 | 0 | ACT (bank activate) |
| 1 | 1 | 0 | 1 | RD (read) |
| 1 | 1 | 0 | 0 | WR (write) |
| 1 | 0 | 1 | 1 | PRE (precharge) |
| 1 | 0 | 0 | 1 | REF (refresh) |
| 0 | x | x | x | DDR4 ACT (ACT_n asserted, ras/cas/we carry upper row bits) |

: Simplified command encoding on DFI control pins

DDR4 uses `dfi_act_n` asserted with `dfi_ras_n`, `dfi_cas_n` and `dfi_we_n` carrying row address
bits A16, A15 and A14. For LPDDR2/3/4 the command pins are held constant and the CA bus is
carried on `dfi_address`.

## LPDDR2/LPDDR3 CA mapping

For LPDDR2 and LPDDR3 the `dfi_address` bus is at least 20 bits wide. The PHY transmits it as a
double-data-rate 10-bit CA bus: bits [9:0] on the rising edge and bits [19:10] on the falling edge
of the DRAM clock.

## LPDDR4 CA mapping

LPDDR4 uses a 6-bit single-data-rate CA bus. The command is delivered over two consecutive
DRAM clock cycles, so a single LPDDR4 command spans two DFI phases. The andesite controller
formats this through a dedicated CA submodule in the command formatter.

## Control timing parameters

| Parameter | Defined by | Description |
| --- | --- | --- |
| `tcmd_lat` | MC | DFI PHY clocks from `dfi_cs` assertion until associated CA signals are driven (LPDDR4 CS-to-CA delay). |
| `tctrl_delay` | PHY | DFI clocks from a control signal change to the change reaching the DRAM interface. |

: Control timing parameters

**Source:** DFI Specification v4.0 sections 3.1, 4.2, Table 5, Table 6

# Command Mapping

DFI does not define DRAM commands directly. It defines the wires that carry them. The MC must
map each DRAM command onto the correct pattern of `dfi_act_n`, `dfi_ras_n`, `dfi_cas_n`,
`dfi_we_n`, `dfi_address`, `dfi_bank`, `dfi_bg`, `dfi_cid`, `dfi_cs` and `dfi_cke`.

## DDR4 command mapping

For DDR4, `dfi_act_n` distinguishes ACT from other commands. During ACT, `dfi_ras_n`,
`dfi_cas_n` and `dfi_we_n` carry row address bits A16, A15 and A14. During non-ACT
commands they carry the classic RAS/CAS/WE encoding.

| DRAM command | `dfi_act_n` | `dfi_ras_n` | `dfi_cas_n` | `dfi_we_n` | `dfi_address` | `dfi_bank` | `dfi_bg` |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ACT | 0 | A16 | A15 | A14 | Row[13:0] | Bank | Bank group |
| RD | 1 | 1 | 0 | 1 | Column + A10=auto-precharge | Bank | Bank group |
| WR | 1 | 1 | 0 | 0 | Column + A10=auto-precharge | Bank | Bank group |
| PRE | 1 | 0 | 1 | 1 | A10=precharge-all | Bank | Bank group |
| REF | 1 | 0 | 0 | 1 | - | - | - |
| MRS | 1 | 0 | 0 | 0 | MR data | MR address | - |
| DES | 1 | 1 | 1 | 1 | - | - | - |

: Simplified DDR4 command mapping on DFI control wires

## LPDDR4 CA command mapping

LPDDR4 uses a 6-bit single-data-rate CA bus delivered over two consecutive DRAM clock cycles.
The command formatter must hold the command pins constant and drive the CA encoding onto
`dfi_address[5:0]` across two phases. The exact two-cycle encoding is defined by JESD209-4;
the andesite controller generates it through a dedicated CA submodule.

Because the CA bus is SDR and commands span two cycles, the MC cannot change CA
arbitrarily on every phase. The CA valid qualifier marks both cycles of a command.

## LPDDR2/LPDDR3 CA mapping

LPDDR2 and LPDDR3 use a 10-bit double-data-rate CA bus. The MC drives a 20-bit value on
`dfi_address`; the PHY transmits bits [9:0] on the rising edge and bits [19:10] on the falling edge.
Command pins (`dfi_act_n`, `dfi_ras_n`, `dfi_cas_n`, `dfi_we_n`, `dfi_bank`, `dfi_bg`, `dfi_cid`)
are held constant.

## Chip select and rank targeting

`dfi_cs` selects the rank for control commands. DFI 4.0 adds `dfi_wrdata_cs` and `dfi_rddata_cs`
to separately identify the target rank on the data path. In a single-rank andesite configuration these
are driven constant. In multi-rank or 3DS configurations they follow the rank selected by the
command.

## CA parity

DDR4 supports command/address parity. The MC generates parity on `dfi_parity_in` covering
`dfi_address`, `dfi_bank`, `dfi_bg`, `dfi_act_n`, `dfi_cas_n`, `dfi_cid`, `dfi_ras_n` and `dfi_we_n`.
The PHY returns any detected parity error on `dfi_alert_n`. The `tparin_lat` and `tphy_paritylat`
parameters define the timing relationship.

**Source:** DFI Specification v4.0 sections 3.1, 4.2, 4.3, 4.11, 4.19

# Revision Deltas

DFI 3.1 is best understood as the v3.0 DDR4 additions plus the LPDDR3 and
interface-split changes of 3.1. The scoria controller inherits the v2.1.1
baseline from pumice and upgrades to 3.1 for the leveling and
initialization model.

## What carried over unchanged from v2.1.1

- Frequency ratios and the `_pN` replication convention. v2.1.1 enumerated
  phase variants explicitly; v3.1 generalizes them to `_pN`. The 1:4 ratio
  is still defined.
- The update interface (`dfi_ctrlupd_*` and `dfi_phyupd_*`).
- The basic command/address/data interface, apart from the DDR4 additions.
- `dfi_init_start` and `dfi_init_complete`, now reused for frequency
  change.
- `dfi_data_byte_disable` and `dfi_dram_clk_disable`.
- Read and write leveling as concepts, though the signal names and per-CS
  scheme were reworked.

## v2.1.1 -> v3.0 changes

v3.0 added the features that enable DDR4:

| Area | v3.0 additions |
| --- | --- |
| Command encoding | `dfi_act_n`, `dfi_bg`, `dfi_cid`; `dfi_ras_n`/`dfi_cas_n`/`dfi_we_n` carry A16/A15/A14 when `dfi_act_n` is asserted. |
| Parity/CRC/alert | `dfi_parity_in`, `dfi_alert_n_aN`, CRC timing parameters. |
| DBI | `dfi_rddata_dbi_n`, `phydbi_mode`. |
| Data path chip select | `dfi_wrdata_cs_n`, `dfi_rddata_cs_n`. |
| Error interface | `dfi_error`, `dfi_error_info`, `terror_resp`. |
| Programmable parameters | `phycrc_mode`, `phydbi_mode`, per-training enables. |

: v3.0 additions over v2.1.1

## v3.0 -> v3.1 changes

v3.1 focused on LPDDR3 and interface refinement:

| Area | v3.1 additions |
| --- | --- |
| LPDDR3 CA training | `dfi_calvl_*`, `dfi_phy_calvl_cs_n`, CA training parameters. |
| LPDDR3 command support | LPDDR3 added to gate training, read data eye training and write leveling. |
| Low power split | `dfi_lp_req` becomes `dfi_lp_ctrl_req` and `dfi_lp_data_req`. |
| PHY-requested training | `dfi_phylvl_req_cs_n`, `dfi_phylvl_ack_cs_n` for non-DFI training mode. |
| LPDDR3 CA mapping | 20-bit `dfi_address` maps to LPDDR3 CA bus. |

: v3.1 additions over v3.0

## Brief v4.0 preview

DFI 4.0 later extended the spec with a much larger training interface,
including DBI training, PHY-master training, and additional status and
frequency-change capabilities. Those features are beyond the scope of a
DDR3/LPDDR3 controller and are not used by scoria.

## What scoria leaves out

The scoria DDR3/LPDDR3 controller does not implement:

- DDR4 command encoding (`dfi_act_n`, `dfi_bg`, `dfi_cid`).
- CA parity, CRC and `dfi_alert_n`.
- DBI.
- LPDDR3 CA training (`dfi_calvl_*`).

These are either DDR4-era or LPDDR4-era features that do not apply to the
target memory types.

**Source:** DFI Specification v3.1 Release Information and revision notes; `projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/docs/scoria_has/ch04_interfaces/01_dfi_v31.md`

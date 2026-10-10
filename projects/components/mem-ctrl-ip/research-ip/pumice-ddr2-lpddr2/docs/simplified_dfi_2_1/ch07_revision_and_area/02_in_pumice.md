# DFI 2.1 in the Pumice DDR2/LPDDR2 Controller

This book is a simplified study guide for the DFI 2.1 interface used by the
pumice DDR2/LPDDR2 memory controller. The controller's DFI layer is implemented
in `rtl/macro/pumice_dfi_layer.sv` and documented in the project's microarchitecture
and interface specifications.

## Sub-interface support

| Sub-interface | Used by pumice? | Notes |
| --- | --- | --- |
| Control | Yes | Per-phase command placement for DDR2 RAS/CAS/WE and LPDDR2 CA. |
| Write data | Yes | Serialized write data, mask, and enable at `t_phy_wrlat`. |
| Read data | Yes | Read data enable at `t_rddata_en`; capture on `dfi_rddata_valid`. |
| Status init | Yes | `dfi_init_start` / `dfi_init_complete` only. |
| Update | No | `ctrlupd_*` / `phyupd_*` not driven in the first revision. |
| Training | No | PHY self-trains at startup (`a7ddrphy`). |
| Frequency change | No | No use case in the current design. |
| Low power | No | No PHY-side low-power coordination. |
| Parity / error | No | Not needed for DDR2/LPDDR2 here. |
: Pumice DFI 2.1 sub-interface support

## Clock-domain crossing

Unlike the classic model where DFI sits on the controller clock, pumice places
the DFI datapath on a dedicated `dfi_clk` and puts the single controller-to-PHY
crossing inside `pumice_dfi_layer`. The crossing uses `gaxi_fifo_async`
instances for command, write data, read data, and init event tokens. There are
no standalone synchronizers.

## Command path

`pumice_dfi_cmd_path` pops a command FIFO and places the active JEDEC command
on the programmed write or read phase, filling the other phases with NOP. For
DDR2 it uses the classic RAS/CAS/WE encoding. For LPDDR2 it uses the CA-bus
formatter described in `docs/uarch/LPDDR2_CA_ENCODING.md`, packing rising CA on
`dfi_address[9:0]` and falling CA on `dfi_address[19:10]` while holding the
RAS/CAS/WE/bank signals idle.

## Write and read serializers

`pumice_dfi_wr_serializer` presents `dfi_wrdata`, `dfi_wrdata_en`, and
`dfi_wrdata_mask` at the programmed write latency. `pumice_dfi_rd_aligner`
drives `dfi_rddata_en` at the programmed read enable latency and captures
`dfi_rddata` when `dfi_rddata_valid` asserts, packing whole words into the
async FIFO back to the controller clock domain.

## Known gaps and future work

The first pumice DFI layer intentionally omits update handshaking, training
control, low-power coordination, and frequency change. These could be added in
a later revision without changing the command/write/read datapath. A future
DDR3/LPDDR3 controller would need a larger DFI sub-interface set and would
likely replace the DFI layer rather than extend this one.

**Source:** `docs/uarch/PUMICE_DFI_LAYER_UARCH.md`, `docs/pumice_mas/ch03_interfaces/02_dfi_v21_interface_spec.md`, `docs/uarch/LPDDR2_CA_ENCODING.md`

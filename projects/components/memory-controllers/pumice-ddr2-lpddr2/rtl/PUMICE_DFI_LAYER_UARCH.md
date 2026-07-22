# pumice DFI layer — µarch (locked spec)

The layer between the scheduler (abstract command stream) and the PHY (DFI 2.1).
Owns per-phase command placement, write-data serialization, read-data alignment,
and the SINGLE clock-domain crossing.

## Clock domains — ONE boundary

```
        aclk (controller) domain                 |   dfi_clk (PHY) domain
  AXI IFC + scheduler + CAMs                      |   DFI phase-packer + PHY
                     │                            |            │
                     └──────  pumice_dfi_cdc  ────┼────────────┘
                         (all CDC here, async     |
                          gaxi FIFOs only)         |
```

- **One CDC module** (`pumice_dfi_cdc`). Every crossing is a `gaxi_fifo_async`
  (Gray-pointer). NO hand-rolled synchronizers, NO open-loop bit crossings.
- Everything up to and including the scheduler + CAMs is on `aclk`. Only the DFI
  phase-packer + PHY are on `dfi_clk`.

## pumice_dfi_cdc — the async-FIFO crossing (payload-agnostic)

| FIFO (gaxi_fifo_async) | dir | payload |
|---|---|---|
| cmd     | ctl→phy | opaque CMD_DW = {op,rank,bank,row,col,ap} |
| wrdata  | ctl→phy | opaque WD_DW  = {data,strb,last} (BL8 beats) |
| rddata  | phy→ctl | opaque RD_DW  = {data,resp,last} |
| init_start   | ctl→phy | 1-bit EVENT TOKEN (rising edge -> latch pinit_start) |
| init_complete| phy→ctl | 1-bit EVENT TOKEN (rising edge -> latch init_complete) |

Level signals (init_start/init_complete) cross as **event tokens** (edge-detect →
push token → pop → set latch), so there are literally zero standalone
synchronizers. init is monotonic (happens once); leveling re-runs are future.
Depths even (gaxi_fifo_async requires even depth).

## PHY-side blocks (dfi_clk) — reworked from existing FUBs

- **phase-packer** (`dfi_cmd_formatter` reworked): pop the cmd FIFO, place the
  command on the correct DFI phase (rd/wr phase, ACT/PRE/REF/MRS on phase 0),
  NOP the rest. Multi-command-per-DFI-cycle packing is where BL8/1-cmd-per-ctl-
  clock maps to nphases; today's formatter is phase-0-only → rework.
- **write serializer** (`pumice_dfi_wr_serializer`; supersedes the retired
  `wr_beat_sequencer`): pop the wrdata FIFO,
  drive dfi_wrdata + dfi_wrdata_mask at tphy_wrlat, BL/2 per phase.
- **read aligner** (`pumice_dfi_rd_aligner`; supersedes the retired
  `rd_cl_aligner`): capture dfi_rddata on
  dfi_rddata_valid, push {data,resp,last} into the rddata FIFO.
- `dfi_signal_pack` + `dfi_v21_interface`: pack the multi-phase bus, DFI egress.

## Verification
- `pumice_dfi_cdc`: dual-clock cocotb (independent ctl/dfi clocks) — data FIFOs
  pass items across in order + lossless; init tokens set the latches.
- Full DFI layer: against the strict per-phase `DFISlavePHY` model (RDS-DV) —
  where the per-phase timing that broke bank-parallel open_page on silicon is
  caught.

## Bandwidth note
1 cmd / controller-clock fills the DQ bus iff BL = 2·nphases. At BL8 @
nphases=4 single-issue is full bandwidth: the DFI layer packs each command's
BL8 across the 4 phases of one DFI cycle. BL and gear are RUNTIME CSRs
(`DFI_PHASE.bl`/`.gear_ratio`, task #146) — the Nexys A7 board build runs
BL4 @ DFI_RATE=2 (the a7ddrphy netlist is 1:2 / nphases=2; the "fixed
nphases=4" reading of it was disproven on silicon), where a BL4 x16 burst is
one 64b DFI word per command.

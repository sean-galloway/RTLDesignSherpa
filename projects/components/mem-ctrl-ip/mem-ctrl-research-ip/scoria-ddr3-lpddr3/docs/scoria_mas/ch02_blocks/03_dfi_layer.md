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

# DFI Layer (`scoria_dfi_layer`)

**Module:** `scoria_dfi_layer.sv` / **Location:** `rtl/macro/` / **Category:** DFI/PHY interface / **Parent:** `scoria_core` / **Status:** complete and sim-verified.

---

## Purpose

The DFI layer owns the only controller-clock to PHY-clock boundary in the design. It carries commands, write data, and read data across asynchronous FIFOs; formats the abstract scheduler command onto the DFI command bus; serializes write data at `t_phy_wrlat`; aligns read data at `t_rddata_en`; and safely crosses the write-leveling handshake. All JEDEC spacing is enforced upstream in the scheduler; this layer is never allowed to stall.

## Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| `NUM_RANKS` | int | 1 | DRAM ranks |
| `NUM_CS` | int | `NUM_RANKS` | Chip selects |
| `NUM_BANKS` | int | 8 | DRAM banks |
| `ROW_WIDTH` | int | 14 | Row address width |
| `COL_WIDTH` | int | 10 | Column address width |
| `DFI_RATE` | int | 2 | DFI phases per clock |
| `DRAM_BEAT_WIDTH` | int | 64 | DRAM beat width |
| `DFI_BEATS_PER_BURST` | int | 8 | DRAM beats per burst |
| `N_SUBCMD` | int | 1 | Sub-DFI-word commands per word |
| `SUB_COL_STRIDE` | int | 1 | Column stride between sub-commands |
| `CMD_FIFO_DEPTH` | int | 8 | Command async FIFO depth |
| `WD_FIFO_DEPTH` | int | 16 | Write-data async FIFO depth |
| `RD_FIFO_DEPTH` | int | 32 | Read-data async FIFO depth |
| `N_FLOP_CROSS` | int | 2 | Pointer synchronizer stages |
| `USE_JOHNSON` | int | 0 | 0 = Gray pointers, 1 = Johnson |
| `RD_MAX_OUTSTANDING` | int | 16 | Read aligner outstanding depth |
| `RD_EN_CYC` | int | `BL_WORDS` | `rddata_en` window width |
| `CMD_HISTORY_EN` | int | 0 | DFI-wire command-history scoreboard |

: Table 2.3.1: DFI layer parameters

`RD_FIFO_DEPTH = 32` was chosen because `dfi_rddata_valid` is fire-and-forget. A depth of 16 dropped beats under paced adjacent bursts.

## Interface

### Controller-domain ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `ctl_clk` | in | 1 | Controller clock |
| `ctl_rstn` | in | 1 | Controller reset (active-low) |
| `cmd_valid_i` | in | 1 | Command valid from scheduler |
| `cmd_ready_o` | out | 1 | Command ready to scheduler |
| `cmd_data_i` | in | `CMD_DW` | Packed command `{ap, col, row, bank, rank, op}` |
| `wd_valid_i` | in | 1 | Write-data valid |
| `wd_ready_o` | out | 1 | Write-data ready |
| `wd_data_i` | in | `WD_DW` | Write data `{last, strb, data}` |
| `rd_valid_o` | out | 1 | Read-data valid |
| `rd_ready_i` | in | 1 | Read-data ready |
| `rd_data_o` | out | `RD_DW` | Read data `{last, resp, data}` |
| `init_start_i` | in | 1 | Init start level |
| `init_complete_o` | out | 1 | Init complete sticky |

: Table 2.3.2: Controller-domain ports

### PHY DFI-domain ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `dfi_clk` | in | 1 | DFI clock |
| `dfi_rstn` | in | 1 | DFI reset (active-low) |
| `memtype_i` | in | `memtype_e` | DDR3 or LPDDR3 |
| `rd_phase_i` | in | `PHW` | Read-command DFI phase |
| `wr_phase_i` | in | `PHW` | Write-command DFI phase |
| `t_phy_wrlat_i` | in | 8 | WR command to `dfi_wrdata_en` delay |
| `t_rddata_en_i` | in | 8 | RD command to `dfi_rddata_en` delay |
| `gear_i` | in | 2 | Active gear ratio selector |
| `n_subcmd_i` | in | `SUBW_MAX` | Active sub-commands per DFI word |
| `sub_col_stride_i` | in | `COL_WIDTH` | Active column stride |
| `sub_phase_stride_i` | in | `PHW` | Active phase stride |
| `dfi_address_o` | out | `DFI_ADDR_BUS_W` | DFI address bus |
| `dfi_bank_o` | out | `DFI_BANK_BUS_W` | DFI bank bus |
| `dfi_cas_n_o` | out | `DFI_CTRL_BUS_W` | DFI CAS# |
| `dfi_ras_n_o` | out | `DFI_CTRL_BUS_W` | DFI RAS# |
| `dfi_we_n_o` | out | `DFI_CTRL_BUS_W` | DFI WE# |
| `dfi_cs_n_o` | out | `DFI_CS_BUS_W` | DFI chip select |
| `dfi_odt_o` | out | `DFI_CS_BUS_W` | DFI ODT |
| `dfi_wrdata_o` | out | `DFI_DATA_WIDTH` | DFI write data |
| `dfi_wrdata_en_o` | out | `DFI_EN_WIDTH` | DFI write data enable |
| `dfi_wrdata_mask_o` | out | `DFI_STRB_WIDTH` | DFI write data mask |
| `dfi_rddata_en_o` | out | `DFI_EN_WIDTH` | DFI read data enable |
| `dfi_rddata_i` | in | `DFI_DATA_WIDTH` | DFI read data |
| `dfi_rddata_valid_i` | in | `DFI_VALID_WIDTH` | DFI read data valid |
| `dfi_init_start_o` | out | 1 | DFI init start sticky |
| `dfi_init_complete_i` | in | 1 | DFI init complete level |

: Table 2.3.3: PHY DFI-domain ports

### Write-leveling crossing ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `wl_req_cs_n_i` | in | `NUM_CS` | Leveling request from scheduler (active-low) |
| `wl_wrlvl_cs_n_i` | in | `NUM_CS` | WRLVL mode from scheduler (active-low) |
| `wl_strobe_i` | in | 1 | One-cycle strobe from scheduler |
| `wl_ack_cs_n_o` | out | `NUM_CS` | PHY ack to scheduler (active-low) |
| `wl_prime_dq_o` | out | 1 | Prime DQ to scheduler |
| `dfi_phylvl_req_cs_n_o` | out | `NUM_CS` | Leveled request to PHY (active-low) |
| `dfi_phylvl_ack_cs_n_i` | in | `NUM_CS` | PHY ack (active-low) |
| `dfi_phy_wrlvl_cs_n_o` | out | `NUM_CS` | Leveled WRLVL mode to PHY (active-low) |
| `dfi_wrlvl_strobe_o` | out | 1 | Leveled one-cycle strobe to PHY |
| `dfi_prime_dq_i` | in | 1 | Prime DQ from PHY |

: Table 2.3.4: Write-leveling crossing ports

## Microarchitecture internals

### Instantiation tree

The DFI layer instantiates:

- `scoria_dfi_cdc` — the single controller/PHY async-FIFO crossing.
- `scoria_dfi_cmd_path` — DFI command bus formatter and fire-strobe generator.
- `scoria_dfi_wr_serializer` — `t_phy_wrlat` delay line to `dfi_wrdata_en`.
- `scoria_dfi_rd_aligner` — `t_rddata_en` delay line and read-data capture.
- `cdc_synchronizer` and `sync_pulse` — write-leveling clock-domain crossings.

### Single CDC

All controller-to-PHY traffic crosses through `scoria_dfi_cdc` using `gaxi_fifo_async` Gray-pointer FIFOs. The block carries command, write data, read data, and init start/complete tokens. Level signals are converted to rising-edge tokens, crossed, and latched sticky on the far side. Write data and a one-bit "write burst staged" token are accepted together so a WR command cannot reach the PHY ahead of its data.

### Active-gear phase mask

The active DFI rate is `w_active_rate = 1 << gear_i`. The unmasked `dfi_wrdata_en` and `dfi_rddata_en` from the serializer and aligner are gated by `w_phase_active` before reaching the pins. When `gear_i == log2(DFI_RATE)` the mask is all-ones and the outputs are bit-identical to the unmasked FUB outputs.

### Command path

`scoria_dfi_cmd_path` owns the DFI command bus and produces `wr_fire_o` and `rd_fire_o` strobes. It does not pace commands; all JEDEC spacing lives upstream. It supports sub-DFI-word burst packing via `N_SUBCMD`, `SUB_COL_STRIDE`, and `SUB_PHASE_STRIDE`.

### Write serializer

On `wr_fire_i`, the serializer waits `t_phy_wrlat_i` DFI cycles and then streams one DFI-word per cycle from the write-data FIFO onto `dfi_wrdata_o` until the burst's `last` word. It pops one word per DFI cycle with zero bubbles. `dfi_wrdata_mask_o` is driven as `~wd_strb_i`.

### Read aligner

On `rd_fire_i`, the aligner drives `dfi_rddata_en_o` after `t_rddata_en_i` cycles and captures `BL_WORDS` DFI words into the read CDC FIFO. It tracks multiple outstanding reads and uses a combinational credit counter to reject the PHY preamble valid before the true read window. `rd_last_o` is asserted when the captured word count reaches `BL_WORDS - 1`.

### Write-leveling crossing

Write-leveling signals cross here because this layer owns the only `ctl_clk`/`dfi_clk` boundary. Slow levels use `cdc_synchronizer` flop chains; the one-cycle `wl_strobe_i` pulse uses `sync_pulse` so the pulse count survives arbitrary clock ratios. Active-low `_n` signals are inverted to active-high before synchronizing and inverted again at the output, avoiding spurious assertions out of reset.

## FSM policy

There is no FSM in this layer. The CDC, command path, serializer, and aligner are all dataflow blocks. The only sequential state is in the FIFOs, delay-line shift registers, and synchronizers.

## Timing

The command and write-data paths are fully registered on `dfi_clk` once they cross. The read path captures `dfi_rddata_i` combinationally when `dfi_rddata_valid_i` is asserted and the credit counter allows, then pushes into the async FIFO. The command-path fire strobes are combinational from the CDC command FIFO output.

## Notes

- `RD_FIFO_DEPTH = 32` is required because `dfi_rddata_valid` cannot be back-pressured. Depth 16 was proven insufficient under paced adjacent bursts.
- `RD_EN_CYC` defaults to `BL_WORDS`, which is dangerous whenever `DRAM_BEAT_WIDTH > DRAM_DEVICE_WIDTH`. `scoria_core` overrides it explicitly with the true DQ occupancy.
- `scoria_dfi_signal_pack` is not instantiated here; the DFI bus is driven directly by the command and data paths.
- The write-leveling strobe must use `sync_pulse`, not a flop chain, because a one-cycle pulse would otherwise be duplicated or swallowed across an arbitrary clock ratio.

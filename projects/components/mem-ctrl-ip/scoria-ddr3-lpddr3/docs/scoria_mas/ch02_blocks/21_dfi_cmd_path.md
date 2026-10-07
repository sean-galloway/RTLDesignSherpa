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

# DFI Command Path (`scoria_dfi_cmd_path`)

**Module:** `scoria_dfi_cmd_path.sv`
**Location:** `rtl/fub/`
**Category:** DFI datapath
**Parent:** `scoria_dfi_layer`
**Status:** implemented (TASK-007)

## Purpose

`scoria_dfi_cmd_path` pops the abstract command stream from the CDC command FIFO, unpacks `{ap, col, row, bank, rank, op}`, and drives the multi-phase DFI command bus through `scoria_dfi_cmd_formatter`. It also emits `wr_fire_o` and `rd_fire_o` strobes so the write serializer and read aligner can align their data phases to the accepted command.

The most important thing this block does **not** do is pace commands. All JEDEC timing lives in the scheduler — the bank timers, global timers, and command arbiter enforce `tRCD`, `tRP`, `tRAS`, `tRFC`, `tCCD`, `tRTW`, and `tWTR` upstream of the CDC. A previous revision tried to re-enforce some of those windows inside this module; TASK-007 traced the resulting FIFO compression to board failures, and the only remaining gates here are structural (read-aligner slot availability and write-data staging). The command path is a constant-latency conduit, not a scheduler.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `NUM_RANKS` | int | 1..4 | 1 | rank count |
| `NUM_BANKS` | int | power of 2 | 8 | bank count |
| `ROW_WIDTH` | int | — | 14 | row address width |
| `COL_WIDTH` | int | — | 10 | column address width |
| `BURST_LEN_WIDTH` | int | — | 8 | burst-length field width (unused by formatter) |
| `DFI_RATE` | int | power of 2 | 4 | DFI frequency ratio |
| `CMD_HISTORY_EN` | int | 0/1 | 0 | enable DFI-wire command-history scoreboard |
| `HIST_T_RCD` | int | — | 0 | scoreboard `tRCD` |
| `HIST_T_RP` | int | — | 0 | scoreboard `tRP` |
| `HIST_T_RAS` | int | — | 0 | scoreboard `tRAS` |
| `HIST_T_RFC` | int | — | 0 | scoreboard `tRFC` |
| `HIST_T_WTR` | int | — | 0 | scoreboard `tWTR` |
| `HIST_T_RTW` | int | — | 0 | scoreboard `tRTW` |
| `N_SUBCMD` | int | 1.. | 1 | compile-time max packed sub-commands |
| `SUB_COL_STRIDE` | int | — | 1 | compile-time max column stride |
| `SUB_PHASE_STRIDE` | int | — | 1 | compile-time max DFI-phase stride |
| `DFI_ADDR_WIDTH` | int | — | 14 | per-phase DFI address width |
| `DFI_BANK_WIDTH` | int | — | 3 | per-phase DFI bank width |
| `DFI_CTRL_WIDTH` | int | — | 1 | per-phase control width |
| `DFI_CS_WIDTH` | int | — | `NUM_RANKS` | per-phase chip-select width |

: Table 2.21.1: `scoria_dfi_cmd_path` parameters

## Interface

### Controller-side command in

| Signal | Direction | Width | Description |
|---|---|---|---|
| `dfi_clk` | in | 1 | DFI / PHY clock |
| `dfi_rstn` | in | 1 | active-low synchronous reset |
| `memtype_i` | in | `memtype_e` | DDR3 or LPDDR3 selection |
| `rd_phase_i` | in | `PHW` | DFI phase carrying read commands |
| `wr_phase_i` | in | `PHW` | DFI phase carrying write commands |
| `n_subcmd_i` | in | `SUBW_MAX` | active sub-command count (runtime) |
| `sub_col_stride_i` | in | `COL_WIDTH` | active column stride (runtime) |
| `sub_phase_stride_i` | in | `PHW` | active phase stride (runtime) |
| `cmd_valid_i` | in | 1 | CDC command FIFO valid |
| `cmd_ready_o` | out | 1 | CDC command FIFO ready |
| `cmd_data_i` | in | `CMD_DW` | packed `{ap, col, row, bank, rank, op}` |

: Table 2.21.2: Command input group

### DFI command bus

| Signal | Direction | Width | Description |
|---|---|---|---|
| `dfi_address_o` | out | `DFI_ADDR_BUS_W` | multi-phase DFI address bus |
| `dfi_bank_o` | out | `DFI_BANK_BUS_W` | multi-phase DFI bank bus |
| `dfi_cas_n_o` | out | `DFI_CTRL_BUS_W` | multi-phase CAS# |
| `dfi_ras_n_o` | out | `DFI_CTRL_BUS_W` | multi-phase RAS# |
| `dfi_we_n_o` | out | `DFI_CTRL_BUS_W` | multi-phase WE# |
| `dfi_cs_n_o` | out | `DFI_CS_BUS_W` | multi-phase chip-select |
| `dfi_odt_o` | out | `DFI_CS_BUS_W` | multi-phase ODT |

: Table 2.21.3: DFI command output group

### Fire strobes

| Signal | Direction | Width | Description |
|---|---|---|---|
| `wr_fire_o` | out | 1 | WR/WRA accepted this cycle |
| `rd_fire_o` | out | 1 | RD/RDA accepted this cycle |
| `fire_rank_o` | out | `RKW` | rank of the fired command |
| `rd_op_ready_i` | in | 1 | read aligner has a free slot |
| `wr_op_ready_i` | in | 1 | write burst is staged in the CDC |
| `wr_accept_o` | out | 1 | pops the write-staged token |

: Table 2.21.4: Data-path strobe group

## Microarchitecture internals

### No command pacing

The accept gate `w_gate` is purely structural:

```text
w_gate = (!read || rd_op_ready_i) && (!write || wr_op_ready_i)
```

`rd_op_ready_i` comes from the read aligner's outstanding-read slot count; `wr_op_ready_i` comes from the CDC write-staged token FIFO. Both are sized so they never deassert in steady state. If either does deassert, the in-order command stream stalls and compresses spacing for every command behind it — exactly the failure mode TASK-007 measured. The `r_wr_held_*` counters (simulation-only) make any such hold observable.

All real timing is enforced upstream:

| Timing | Upstream owner |
|---|---|
| `tCCD` | `scoria_cmd_arbiter` `r_tccd_fwd`, clamped to burst length in `scoria_core` |
| `tRTW` / `tWTR` | `scoria_global_timers` `r_trtw_cnt` / `r_twtr_cnt` |
| `tRFC` | `scoria_cmd_arbiter` `r_rfc_cnt` |
| `tRCD` / `tRP` / `tRAS` / `tRRD` / `tFAW` | `scoria_bank_timer` and rank gates |

: Table 2.21.5: Timing enforcement remains upstream of the command path

### Sub-DFI-word burst packing

When `N_SUBCMD > 1`, a single scheduled column command packs multiple JEDEC bursts into one DFI word. The canonical case is gear 1:4 with x16 BL4: each BL4 occupies only two of the four DFI phases, so two BL4 reads share one 128-bit DFI word. The path issues `n_subcmd_i` sub-column-commands in a single DFI cycle on phases `{base_phase, base_phase + sub_phase_stride_i, ...}` with columns `{col, col + sub_col_stride_i, ...}`. One formatter instance per sub-command places its decoded command on its own phase; the per-sub buses merge with OR for address/bank/ODT and AND for chip-select and the three command strobes, because inactive phases carry NOP (`cs_n`/`ras_n`/`cas_n`/`we_n` all ones, address/bank/ODT zero).

The whole packed group produces exactly one FIFO pop, one `wr_fire_o` or `rd_fire_o`, and one `wr_accept_o`. The data path therefore drives or captures the single DFI word once, even though `N_SUBCMD` DRAM commands were issued.

```text
compile-time max:  N_SUBCMD, SUB_COL_STRIDE, SUB_PHASE_STRIDE
runtime active:    n_subcmd_i, sub_col_stride_i, sub_phase_stride_i
legacy path:       N_SUBCMD == 1, sub 0 only on the base phase
```

### DFI-wire command-history scoreboard

When `CMD_HISTORY_EN != 0`, the block instantiates `scoria_cmd_history_checker` on the accepted command stream (`w_fire`). This checker sees the same spacing the DRAM sees, downstream of the CDC FIFO, so it catches compression that the scheduler-side checker cannot observe. The feature is simulation-only and off by default.

## FSM policy

There is no FSM. The command path is combinational unpack, generate, and merge, followed by registered outputs and the registered fire strobes.

## Timing

- Command accept-to-DFI-bus latency is one `dfi_clk` cycle (the formatter's registered output).
- `wr_fire_o` / `rd_fire_o` are registered one cycle to align with the formatter outputs.
- Sub-DFI-word packing adds no extra latency; all sub-commands issue in the same cycle.

## Notes

- The elaboration assertions at `scoria_dfi_cmd_path.sv:403-413` require `DFI_RATE` to be a power of two and, when `N_SUBCMD > 1`, `N_SUBCMD * SUB_PHASE_STRIDE == DFI_RATE`. These mirror the DV BFM's anchored-slot-mask contract so the a7ddrphy de-interleaver packs every sub-burst into the same DFI word with no stale phases.
- The `BURST_LEN_WIDTH` parameter is carried for interface compatibility but `cmd_len_i` is tied off inside the formatter for this controller generation.
- Dormant operations `OP_SREFE`, `OP_SREFX`, and `OP_DPDE` fall through the formatter default arm and are driven as NOP on the DFI command pins; their real behavior is CKE sequencing handled elsewhere. See `ch02_blocks/26_dormant_powerdown_and_pack.md`.

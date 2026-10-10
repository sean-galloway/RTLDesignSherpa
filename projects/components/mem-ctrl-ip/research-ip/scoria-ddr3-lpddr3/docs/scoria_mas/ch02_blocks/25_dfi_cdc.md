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

# DFI Clock-Domain Crossing (`scoria_dfi_cdc`)

**Module:** `scoria_dfi_cdc.sv`
**Location:** `rtl/fub/`
**Category:** clock-domain crossing
**Parent:** `scoria_dfi_layer`
**Status:** implemented and formally proven (`formal/scoria/scoria_dfi_cdc.sby`)

## Purpose

`scoria_dfi_cdc` is the single boundary between the controller clock domain (`ctl_clk`) and the PHY DFI clock domain (`dfi_clk`). All traffic between the two domains crosses through `gaxi_fifo_async` Gray-pointer FIFOs; there are no hand-rolled synchronizers and no open-loop bit crossings. The block is formally proven.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `CMD_DW` | int | — | 32 | command payload width |
| `WD_DW` | int | — | 72 | write-data payload width |
| `RD_DW` | int | — | 66 | read-data payload width |
| `CMD_DEPTH` | int | power of 2 | 8 | command FIFO depth |
| `WD_DEPTH` | int | power of 2 | 16 | write-data FIFO depth |
| `RD_DEPTH` | int | power of 2 | 16 | read-data FIFO depth |
| `TOK_DEPTH` | int | power of 2 | 4 | init-token FIFO depth |
| `N_FLOP_CROSS` | int | — | 2 | pointer synchronizer stages |
| `USE_JOHNSON` | int | 0/1 | 0 | 0 = Gray pointers, 1 = Johnson pointers |

: Table 2.25.1: `scoria_dfi_cdc` parameters

## Interface

### Controller domain

| Signal | Direction | Width | Description |
|---|---|---|---|
| `ctl_clk` | in | 1 | controller clock |
| `ctl_rstn` | in | 1 | active-low synchronous reset |
| `cmd_valid_i` | in | 1 | command FIFO push valid |
| `cmd_ready_o` | out | 1 | command FIFO push ready |
| `cmd_data_i` | in | `CMD_DW` | packed command payload |
| `wd_valid_i` | in | 1 | write-data FIFO push valid |
| `wd_ready_o` | out | 1 | write-data FIFO push ready |
| `wd_data_i` | in | `WD_DW` | packed write-data payload |
| `wd_last_i` | in | 1 | last word of write burst |
| `init_start_i` | in | 1 | init-start level |
| `rd_valid_o` | out | 1 | read-data FIFO pop valid |
| `rd_ready_i` | in | 1 | read-data FIFO pop ready |
| `rd_data_o` | out | `RD_DW` | packed read-data payload |
| `init_complete_o` | out | 1 | init-complete sticky latch |

: Table 2.25.2: Controller-domain ports

### PHY domain

| Signal | Direction | Width | Description |
|---|---|---|---|
| `dfi_clk` | in | 1 | DFI / PHY clock |
| `dfi_rstn` | in | 1 | active-low synchronous reset |
| `pcmd_valid_o` | out | 1 | command FIFO pop valid |
| `pcmd_ready_i` | in | 1 | command FIFO pop ready |
| `pcmd_data_o` | out | `CMD_DW` | packed command payload |
| `pwd_valid_o` | out | 1 | write-data FIFO pop valid |
| `pwd_ready_i` | in | 1 | write-data FIFO pop ready |
| `pwd_data_o` | out | `WD_DW` | packed write-data payload |
| `pwr_staged_valid_o` | out | 1 | write-burst-staged token valid |
| `pwr_staged_pop_i` | in | 1 | write-burst-staged token pop |
| `pinit_start_o` | out | 1 | init-start sticky latch |
| `prd_valid_i` | in | 1 | read-data FIFO push valid |
| `prd_ready_o` | out | 1 | read-data FIFO push ready |
| `prd_data_i` | in | `RD_DW` | packed read-data payload |
| `pinit_complete_i` | in | 1 | init-complete level |

: Table 2.25.3: PHY-domain ports

## Microarchitecture internals

### FIFO instances

| Instance | Direction | Payload | Depth | Purpose |
|---|---|---|---|---|
| `u_cmd_fifo` | ctl to phy | `CMD_DW` | `CMD_DEPTH` | commands |
| `u_wd_fifo` | ctl to phy | `WD_DW` | `WD_DEPTH` | write data |
| `u_wtok_fifo` | ctl to phy | 1 bit | `WD_DEPTH` | write-burst-staged tokens |
| `u_rd_fifo` | phy to ctl | `RD_DW` | `RD_DEPTH` | read data |
| `u_istart_tok` | ctl to phy | 1 bit | `TOK_DEPTH` | init-start rising-edge token |
| `u_icmp_tok` | phy to ctl | 1 bit | `TOK_DEPTH` | init-complete rising-edge token |

: Table 2.25.4: Clock-domain-crossing FIFOs

All six FIFOs use `gaxi_fifo_async` with `N_FLOP_CROSS = 2` synchronizer stages.

### Payload packing

```text
CMD_DW = 32 : { op[3:0], rank, bank, row, col, ap }
WD_DW  = 72 : { data[63:0], strb[7:0], last }
RD_DW  = 66 : { data[63:0], resp[1:0], last }
```

The command payload is opaque to the CDC; unpacking happens in `scoria_dfi_cmd_path`. The write-data and read-data payloads include their respective `last` bits so the serializer and return ring can detect burst boundaries.

### Pointer encoding

Gray pointers are the default (`USE_JOHNSON = 0`), which requires power-of-two depths. Johnson encoding is opt-in (`USE_JOHNSON = 1`) and supports arbitrary depths, but it costs `DEPTH`-bit pointers in both clock domains and every synchronizer stage.

### Init tokens

`init_start_i` and `pinit_complete_i` are level signals, but initialization is monotonic: once asserted it stays asserted. The CDC converts each rising edge to a one-bit token, crosses it through a token FIFO, and sets a sticky latch on the far side. Re-runs are future work.

### The staged-token invariant

Write data and write-staged tokens are accepted together on the controller side:

```text
wd_ready_o  = w_wd_data_ready && w_wtok_ready
w_wtok_push = wd_valid_i && wd_last_i && w_wd_data_ready
```

A token is pushed only on the burst's last word, and only if the data FIFO also has room. On the PHY side, `scoria_dfi_cmd_path` pops one token for each accepted WR command. This guarantees that a WR command can never reach the PHY ahead of its data. With the controller's rate-matched commit and `CMD_DELAY`, the token gate is an invariant that never holds; the command path's `r_wr_held_*` counters prove it.

## FSM policy

There is no FSM. The CDC is a structural assembly of async FIFOs plus the two token sticky-latch paths.

## Timing

- Command and data FIFO crossings add the latency of the `gaxi_fifo_async` implementation plus `N_FLOP_CROSS` synchronizer stages on each pointer.
- Init-token crossing adds one rising-edge detector, one FIFO, and one sticky latch on each side.
- No combinational path exists between `ctl_clk` and `dfi_clk`.

## Notes

- The staged-token FIFO depth equals `WD_DEPTH` because at most one token can be staged per data word.
- All six crossings go through `gaxi_fifo_async`; there are no custom synchronizers.
- The block is formally proven in `formal/scoria/scoria_dfi_cdc.sby` with `prove` and `cover` tasks at depth 20.

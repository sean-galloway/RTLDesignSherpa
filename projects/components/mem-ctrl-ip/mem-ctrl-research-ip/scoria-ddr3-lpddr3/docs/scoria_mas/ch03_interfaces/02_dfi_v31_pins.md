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

# DFI v3.1 Pin-Level Table

This page pins every DFI signal that appears on `scoria_top`. The widths below are expressed in the design-point parameters (`ROW_WIDTH = 14`, `NUM_BANKS = 8`, `NUM_RANKS = 1`, `DRAM_BEAT_WIDTH = 64`, `DFI_RATE = 2`) and therefore evaluate to the default values shown in parentheses. The DFI-layer internals are in [DFI Layer](../ch02_blocks/03_dfi_layer.md); command encoding is in [DFI Command Formatter](../ch02_blocks/22_dfi_cmd_formatter.md); write leveling is in [Write Leveling Interface](../ch02_blocks/20_wrlvl_ifc.md).

The "Version" column marks whether a signal is part of the v2.1.1 base surface or added by v3.1. Scoria targets v3.1 (HAS decision D1), so the v3.1-added signals are required at the boundary even when this PHY family does not consume them.

## Per-phase packed buses

DFI v3.1 generalises the phase-specific notation that v2.1.1 enumerated as `_p0`, `_p1`, ... into `_pN`. Scoria's buses are packed: phase `p` occupies bits `[p*W +: W]` of the bus. A command bus with `DFI_RATE = 2` therefore carries two independent command slots per DFI cycle; the data buses carry one DRAM beat per phase. The formatter places non-column commands on phase 0, READ on `rd_phase`, and WRITE on `wr_phase`.

## Reset convention

DFI outputs reset to the de-asserted, command-inactive level: chip selects high, command pins high, data enables low, and address/bank buses at 0. DFI inputs are qualified by their valid/enable companions and carry no reset value. `dfi_reset_n_o` is the exception: it is driven active from reset and released by the init sequencer when the sequence reaches CKE high.

## Clock, reset, and init

| Pin | Dir | Width | Version | Notes |
|---|---|---|---|---|
| `dfi_clk` | in | 1 | v2.1.1 base | PHY clock |
| `dfi_rstn` | in | 1 | v2.1.1 base | PHY reset, active low |
| `dfi_reset_n_o` | out | 1 | v2.1.1 base (DDR3) | DRAM RESET#; gated on memory type, not DFI version |
| `dfi_init_start_o` | out | 1 | v3.1 added | MC init / frequency-change request |
| `dfi_init_complete_i` | in | 1 | v3.1 added | PHY init complete / frequency-change acknowledge |

: Table 3.2.1: Clock, reset, and init handshake

`dfi_reset_n_o` is driven by the init sequencer and is latched released at `S_D3_CKE`; it is never re-asserted without an `init_force_restart`. `dfi_init_start_o` and `dfi_init_complete_i` form a self-timed handshake: the controller raises start, the PHY returns complete when ready, and the controller does not wait on the return at this design point. The `init_done_o` pin is the host-visible completion flag.

## Command bus

| Pin | Dir | Width | Version | Notes |
|---|---|---|---|---|
| `dfi_address_o` | out | `ROW_WIDTH * DFI_RATE` (28) | v2.1.1 base | address; row on ACT, column on RD/WR, MR data on MRS |
| `dfi_bank_o` | out | `$clog2(NUM_BANKS) * DFI_RATE` (6) | v2.1.1 base | bank address |
| `dfi_cas_n_o` | out | `1 * DFI_RATE` (2) | v2.1.1 base | command pin; A15 in non-ACT commands |
| `dfi_ras_n_o` | out | `1 * DFI_RATE` (2) | v2.1.1 base | command pin; A16 in non-ACT commands |
| `dfi_we_n_o` | out | `1 * DFI_RATE` (2) | v2.1.1 base | command pin; A14 in non-ACT commands |
| `dfi_cs_n_o` | out | `NUM_RANKS * DFI_RATE` (2) | v2.1.1 base | chip select; low asserts the rank |
| `dfi_odt_o` | out | `NUM_RANKS * DFI_RATE` (2) | v2.1.1 base | on-die termination |

: Table 3.2.2: DFI command bus

The DDR3 command truth table is `NOP/ACT/RD/RDA/WR/WRA/PRE/PREA/REF/MRS/ZQCS/ZQCL`; LPDDR3 uses the bit-exact JESD209-2F Table 60 CA-bus encoding packed into `dfi_address_o`. See [DFI Command Formatter](../ch02_blocks/22_dfi_cmd_formatter.md) for the decode.

`dfi_odt_o` is driven according to the mode-register ODT settings and the direction of the current transaction; it is not a static tie-off. At init it is held low (or off) until the MRS chain has programmed the termination values.

At `NUM_RANKS = 1` the `dfi_cs_n_o` bus carries one active-low select repeated across `DFI_RATE` phases. There is no `dfi_cid` because chip ID is meaningful only for 3DS multi-rank stacks.

## Write data

| Pin | Dir | Width | Version | Notes |
|---|---|---|---|---|
| `dfi_wrdata_o` | out | `DRAM_BEAT_WIDTH * DFI_RATE` (128) | v2.1.1 base | write data, per-phase packed |
| `dfi_wrdata_en_o` | out | `DFI_RATE` (2) | v2.1.1 base | write data enable, one bit per phase |
| `dfi_wrdata_mask_o` | out | `(DRAM_BEAT_WIDTH * DFI_RATE) / 8` (16) | v2.1.1 base | byte mask; `~strb` from the write data stream |

: Table 3.2.3: DFI write data

The write serializer drives `dfi_wrdata_en_o` after `t_phy_wrlat` DFI cycles and streams one DFI word per cycle until the burst's last word. `dfi_wrdata_mask_o` is the inverse of the AXI write strobe.

The write-data path is rate-matched to the command path by the staged-token invariant in the CDC: a WR command cannot reach the PHY ahead of its data. See [DFI Clock-Domain Crossing](../ch02_blocks/25_dfi_cdc.md) for the token mechanism.

## Read data

| Pin | Dir | Width | Version | Notes |
|---|---|---|---|---|
| `dfi_rddata_en_o` | out | `DFI_RATE` (2) | v2.1.1 base | read data enable, one bit per phase |
| `dfi_rddata_i` | in | `DRAM_BEAT_WIDTH * DFI_RATE` (128) | v2.1.1 base | read data, per-phase packed |
| `dfi_rddata_valid_i` | in | `DFI_RATE` (2) | v2.1.1 base | read data valid, one bit per phase |

: Table 3.2.4: DFI read data

The read aligner drives `dfi_rddata_en_o` after `t_rddata_en` cycles and captures `BL_WORDS` DFI words. `dfi_rddata_valid_i` is fire-and-forget: the aligner accepts every asserted beat and pushes it into the read CDC FIFO.

`dfi_rddata_en_o` is masked to the active phases by `gear_ratio`: at the default gear the mask is all-ones, and the outputs are unchanged. See [DFI Read Aligner](../ch02_blocks/24_dfi_rd_aligner.md).

## Per-data-phase chip selects (v3.1 added)

| Pin | Dir | Width | Version | Notes |
|---|---|---|---|---|
| `dfi_wrdata_cs_n_o` | out | `NUM_RANKS * DFI_RATE` (2) | v3.1 only | which rank owns the DQ bus during the write window |
| `dfi_rddata_cs_n_o` | out | `NUM_RANKS * DFI_RATE` (2) | v3.1 only | which rank owns the DQ bus during the read window |

: Table 3.2.5: Per-data-phase chip selects

At `NUM_RANKS = 1` both buses are driven constant `'0`; the only legal value is rank 0. The CS-under-training role of `dfi_wrdata_cs_n_o` is degenerate at one rank because the rank being leveled is always CS0. A multi-rank build must drive them from the granted command's rank, in step with `dfi_cs_n_o`.

## Write-leveling handshake (v3.1 added)

| Pin | Dir | Width | Version | Notes |
|---|---|---|---|---|
| `dfi_phylvl_req_cs_n_o` | out | `NUM_CS` (1) | v3.1 only | per-CS leveling request to PHY |
| `dfi_phylvl_ack_cs_n_i` | in | `NUM_CS` (1) | v3.1 only | PHY acknowledge per CS |
| `dfi_phy_wrlvl_cs_n_o` | out | `NUM_CS` (1) | v3.1 only | which CS is under write leveling |
| `dfi_wrlvl_strobe_o` | out | 1 | v3.1 only | one-cycle DQS strobe to PHY |
| `dfi_prime_dq_i` | in | 1 | v3.1 only | prime DQ result from PHY |

: Table 3.2.6: Write-leveling handshake

This PHY family does not implement the DFI leveling handshake, so on the Genesys 2 build these pins are unused; write leveling there is the PHY's own. They exist for a PHY that exposes the v3.1 interface. The crossing from controller clock to `dfi_clk` lives in [DFI Layer](../ch02_blocks/03_dfi_layer.md); the protocol state machine is in [Write Leveling Interface](../ch02_blocks/20_wrlvl_ifc.md). The `dfi_wrlvl_strobe_o` pulse is generated only in the `WL_READY` state.

## Signals not pinned out

The following DFI v3.1 signals are defined by the specification but are **not present on `scoria_top`** at this design point:

| Signal | Why absent |
|---|---|
| `dfi_lp_ctrl_req` / `dfi_lp_data_req` | The dormant `powerdown_ctrl` / `dfi_signal_pack` pair is retained uninstantiated; power-down is absent by decision. See [The Dormant Pair](../ch02_blocks/26_dormant_powerdown_and_pack.md). |
| `dfi_error` / `dfi_error_info` | DDR4-era CA-parity error surface; scoria uses the error indication only conceptually and ignores the DDR4-specific encodings. |

: Table 3.2.7: DFI v3.1 signals not pinned out

The absence of the low-power handshake means the HAS's never-wedge timeout behavior has no RTL driver at the pin level in this build. If a future PHY consumes `dfi_lp_ctrl_req` / `dfi_lp_data_req`, the handshake must be added at the top level and the timeout rule becomes binding.

## References

The DFI v3.1 specification delta is argued in the HAS Chapter 4. The RTL port list is `rtl/top/scoria_top.sv`; the DFI-layer internal surface is `rtl/macro/scoria_dfi_layer.sv`.

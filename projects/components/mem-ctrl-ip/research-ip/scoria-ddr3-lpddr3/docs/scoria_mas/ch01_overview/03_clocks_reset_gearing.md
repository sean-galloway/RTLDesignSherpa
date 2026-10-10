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

# Clocks, Reset, and Gearing

## The two domains

scoria has exactly two clock domains, and the boundary between them is a
single block.

| Domain | Signals | Clock | What lives there |
|---|---|---|---|
| Controller | `aclk` / `aresetn` | host/MC clock | AXI4 front-end, CAMs, return ring, scheduler (arbiter, timers, refresh/ZQ/init), the controller side of the CDC |
| PHY / DFI | `dfi_clk` / `dfi_rstn` | PHY clock | DFI command path, write serializer, read aligner, the PHY side of the CDC |

: Table 1.4: Clock domains

Every crossing between them goes through `scoria_dfi_cdc` (page 2.25): five
`gaxi_fifo_async` instances for commands, write data, read data, and the
init/leveling event tokens. There are no hand-rolled synchronizers anywhere
else in the design, and the DFI layer is deliberately never allowed to stall
— all JEDEC spacing is enforced on the controller side, upstream of the FIFOs.

The init handshake crosses as rising-edge tokens and latches sticky on the
far side: `dfi_init_start_o` (controller → PHY) and `dfi_init_complete_i`
(PHY → controller). Software sees the far end of the same handshake as
`STATUS.init_done`.

Both resets are active-low and asynchronous-assert, synchronous-deassert in
the usual family style; each side of the CDC has its own reset
(`ctl_rstn`/`dfi_rstn` derive from them inside the DFI layer).

## The target design point

One operating point is characterized and gated today — the macro-tier
consistency test (`test_scoria_dram_config_consistency.py`) cross-checks the
framework's cycle-accurate view of every timing against the controller's
programmed spacing table, so the numbers below are a gate, not a hope:

| Property | Value |
|---|---|
| Board / PHY | Genesys 2, K7 DDR3 PHY |
| Devices | 2 x MT41J256M16, 32-bit DQ |
| Grade | DDR3-800 — 400 MHz DRAM clock, 3200 MB/s peak |
| MC clock (`aclk`) | 75 MHz (13.33 ns) — restated by the owner 2026-10-10; 100 MHz was never the target (scoria BUG-003, closed) |
| `DFI_RATE` | 4 (the RTL default of 2 is overridden at integration) |
| Burst | BL8 |
| Address geometry | 8 banks, row 15 / col 10 |

: Table 1.5: The `genesys2_ddr3_800` operating point

## Width gearing

`scoria_core` ties the host AXI data width to the DFI word width
(`DW = DRAM_BEAT_WIDTH * DFI_RATE`). When a host needs a different width,
`scoria_top_geared` wraps `scoria_top` with formally verified AXI
data-width converters (write and read directions) and enforces a power-of-two
ratio between `HOST_AXI_DATA_WIDTH` and `DW`. When the widths already match,
the converter is bypassed (`g_direct`) and existing builds are bit-identical.

## Timing floors worth knowing up front

Three floor rules are set at integration in `scoria_core`/`scoria_top`, long
before any block page gets to them:

- `w_t_rtw_eff` is floored at `t_rddata_en + RD_EN_CYC_TOP - t_phy_wrlat`
  (pumice BUG-014) so a write can never land inside the controller's own read
  window.
- `RD_EN_CYC` is overridden explicitly to `ceil(DRAM_BL / DFI_RATE)`; the
  aligner's parameter default would lose half a burst on narrow devices
  (page 2.24).
- `CMD_DELAY` defaults to auto (`5 + 2*BURST_WORDS`) — the scheduler's
  output FIFO releases each command only after its token matures, so write
  data always reaches the DFI no later than the command (page 2.2).

Two CSR-encoding landmines were disarmed at the top level and are recorded
where they belong: the page-policy encoding is translated from software
values to the internal enum in `scoria_top` (a raw cast swapped OPEN/CLOSE —
issue #42), and `STATUS.init_done` plus the per-bank `OBS_ROW_HIT` registers
are actually driven (they weren't, once, and software polled forever —
pumice BUG-020).

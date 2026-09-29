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

# Write and Read Data Paths

The data path spans two clock domains. On the controller (`aclk`) side the two CAMs in `pumice_axi4_ifc` buffer burst data; on the DFI (`dfi_clk`) side the write serializer and read aligner drive/capture the DFI data bus. All four are **de-FSM'd streaming readers** — they are FIFO-fed / beat-counter datapaths with no active/slot state latch.

## Controller-Side CAMs

### `pumice_wr_data_cam`

RTL: `rtl/fub/pumice_wr_data_cam.sv`. A write-command CAM plus a write-data SRAM. Entries are keyed on `{bank, row, col}` with a free-running age; the burst payload lives in an SRAM slot. Three data movers stream over the SRAM:

- **fill** — captures W beats into the slot on insert.
- **commit-drain** — streams the slot to the DFI write path when the scheduler commits the entry.
- **snarf** — forwards a slot to a matching read (read-your-write), limited to unscheduled entries with a matching id and burst length.

Age is compared wrap-safe as a relative age (`age_ctr - entry_age`). The snarf lookup returns the **youngest** match (latest data), the scheduler lookup returns the **oldest** match (in-order commit per row), and the `oldest` port returns the oldest valid entry for the scheduler fallback. A fill-complete flag gates schedulability and snarf so a partially-filled burst is never committed or forwarded.

There is no standalone `wr2rd_forward` block — write-to-read forwarding is exactly the snarf mover in this CAM.

### `pumice_rd_cmd_cam`

RTL: `rtl/fub/pumice_rd_cmd_cam.sv`. The read miss path — an outstanding-read tracker acting as a **reorder buffer**. Entries are keyed `{bank, row, col}` with a free-running age and N scheduler lookups so reads row-hit-schedule like writes. Data flows the opposite direction from the write CAM: it comes **in** from the DFI read return and drains **out** to `pumice_rd_intake`. DRAM read data returns in issue order and is buffered per entry; it drains in AR (insert) order, which is what enforces per-ID read ordering.

The issue-side oldest/lookups pick the oldest not-yet-issued entry; the drain side releases the oldest valid entry gated on data-ready. There is no snarf port (that is a write-CAM concept).

## DFI-Side Data Movers

Both movers live in the DFI layer on `dfi_clk`. Their internal unit is the **DFI word** (`DRAM_BEAT_WIDTH * DFI_RATE` wide), which already carries all `DFI_RATE` phases; `dfi_signal_pack` splits it to the pins. One FIFO pop is one DFI cycle, so both are bubble-free.

### `pumice_dfi_wr_serializer`

RTL: `rtl/fub/pumice_dfi_wr_serializer.sv`. On a `wr_fire` from the command path it waits `t_phy_wrlat_i` DFI cycles, then streams one DFI-word per cycle from the write-data FIFO onto `dfi_wrdata` (with `dfi_wrdata_en` and `dfi_wrdata_mask`) until the burst's `last` word. Because the write CAM pre-stages the burst into the FIFO when the command is scheduled, the burst is already waiting at `wr_fire` and the drive never stalls. The DFI byte mask is the inverted AXI strobe (`mask = ~strb`; AXI `wstrb=1` = write byte, DFI `mask=1` = mask).

### `pumice_dfi_rd_aligner`

RTL: `rtl/fub/pumice_dfi_rd_aligner.sv`. The mirror of the write serializer. On a `rd_fire` it drives `dfi_rddata_en` for the read window starting `t_rddata_en_i` DFI cycles later, captures `dfi_rddata` whenever the PHY asserts `dfi_rddata_valid`, and pushes one DFI-word per valid cycle into the read FIFO as `{last, resp, data}`. `BL_WORDS = BL/DFI_RATE` words per burst; `last` marks the final word so the read intake can split words back into AXI R beats. v1 supports one outstanding read window (single-issue, tRTW/tCCD spaced).

## Response Generation

- **B response** — the write intake returns B when the write CAM signals commit-done for the transaction id, matching AXI4 posted-write semantics and decoupling B latency from DRAM-side delays.
- **R response** — the read intake drains the read CAM onto the R channel in AR order with the correct id and `rlast`. In v1 all reads return `OKAY` (the DFI `resp` field is carried through but DDR2/LPDDR2 have no CA parity to surface).

## Runtime PHY Timing

The write and read timing offsets are runtime CSR knobs rather than hard-coded PHY latencies, so one build ports across PHYs: `t_phy_wrlat` (WR command to `dfi_wrdata_en`) and `t_rddata_en` (RD command to `dfi_rddata_en`), plus the `DFI_PHASE` CSR (`rd_phase` / `wr_phase`) covered in the DFI/CSR chapter.

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: granite_pkg
// Purpose: granite (DDR2/LPDDR2 product, v2) SKU parameters. A product is
//          a configuration of the common-ip stack (common_has ch5.2) - this
//          package is the single place the SKU's structural choices live;
//          config/product_config.md records the reasoning and the values
//          that are not yet decided.
//
// Documentation: product-ip/granite-ddr2-lpddr2/config/product_config.md

package granite_pkg;

    // ------------------------------------------------------------------
    // Storage plane, lite configuration (ch5.2 v2 default)
    // N-deep in-order seam (N=8, matching pumice's NUM_ENTRIES): the entry
    // store allocates in-order, so the seam behaves as an N-deep FIFO per
    // direction, while the scheduler's pick machinery argmaxes over the
    // schedulable-entry vectors exactly as it does at any depth. Storage
    // "off" shrinks toward one, never reaches zero -- and at 8 the seam
    // hides the read round-trip latency (~5 outstanding needed to sustain
    // the port at BL8; 8 gives margin).
    // ------------------------------------------------------------------
    parameter int GRANITE_SEAM_N          = 8;
    parameter int GRANITE_ENTRY_STORE_DEPTH = 8;

    // ------------------------------------------------------------------
    // Write-data staging at the SKU minimum (ch5.2: never zero). Sized by
    // the product burst profile, not the research sweep. BL4 x16 default;
    // re-derive at board bring-up.
    // ------------------------------------------------------------------
    parameter int GRANITE_WR_DATA_BUF_WORDS = 16;

    // ------------------------------------------------------------------
    // Direction batch cap: column fires in one direction before the pick
    // must hand the bus to the other while it is waiting (mc_bank_pick
    // dir_batch_max_i; read back as SCHED_WR_WM.wr_batch_max). 255, the
    // field maximum, measured 2026-10-30 on the char proxy (hybrid page mode,
    // MB/s total, wr/rd balanced within 6%): cap 64 / 128 / 255 ->
    // conc_banks 485 / 526 / 549, conc_rows 491 / 525 / 549, concurrent
    // col_major 310 / 321 / 326, mixed 295 flat. Uncapped (0, how it was
    // wired until then) reached 571 / 564 only because a direction that
    // never ran dry was never made to yield: concurrent col_major split
    // 166 / 345 and the cap-on runs went 2048 reads, then 2048 writes.
    // ------------------------------------------------------------------
    parameter int GRANITE_DIR_BATCH_MAX = 255;

    // ------------------------------------------------------------------
    // Fast read release (mc_scheduler_plane FAST_RD_RELEASE): a command
    // skips the CMD_DELAY write-data lead while no write is in the line,
    // entered after the line has idled CMD_DELAY + the largest programmed
    // spacing. On the char proxy the unloaded page-hit read was 26 cycles
    // AR->R of which 7 were that lead (2026-10-31, granite TASK-003).
    // ------------------------------------------------------------------
    parameter bit GRANITE_FAST_RD_RELEASE = 1'b1;

    // Read-return head bypass (mc_rd_return_ring RET_BYPASS): the next beat
    // in AR order goes from the DFI return straight into the ring's output
    // skid, skipping the BRAM write -> ready -> read round trip (3 -> 1).
    parameter bit GRANITE_RD_RET_BYPASS = 1'b1;

    // ------------------------------------------------------------------
    // RAS plane: ABSENT in this SKU (true bypass, reserved CSR decode
    // only). Expressed as omission - no transform pair is instantiated -
    // not as a parameter.
    // ------------------------------------------------------------------

    // ------------------------------------------------------------------
    // Frequency plan. Every timer CSR is an mc_clk cycle count derived
    // from these - a frequency change invalidates the whole CSR set
    // (common HAS frequency warning). Granite A7 plan: 75 MHz sys / 300 MT/s
    // DDR2-300. Define GRANITE_SYS_66 selects 66.67 MHz / DDR2-266 fallback.
    // ------------------------------------------------------------------
    parameter int GRANITE_ACLK_MHZ = 75;   // Granite A7 sys clock (mc_clk)
    parameter int GRANITE_DFI_MHZ  = 300;  // DFI/DRAM data rate (2x sys_clk)

    // Training clients: the LPDDR2 set lives in common-ip
    // (mc_lpddr2_zq_ctrl, mc_lpddr2_dq_cal) and is composed by
    // mc_training_plane. DDR2 has no ZQ/DQ-cal maintenance requirement.

endpackage : granite_pkg

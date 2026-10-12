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
    // N=1 in-order seam: the scheduler's pick machinery still argmaxes over
    // schedulable-entry vectors, so the entry store shrinks toward one and
    // never reaches zero.
    // ------------------------------------------------------------------
    parameter int GRANITE_SEAM_N          = 1;
    parameter int GRANITE_ENTRY_STORE_DEPTH = 1;

    // ------------------------------------------------------------------
    // Write-data staging at the SKU minimum (ch5.2: never zero). Sized by
    // the product burst profile, not the research sweep. BL4 x16 default;
    // re-derive at board bring-up.
    // ------------------------------------------------------------------
    parameter int GRANITE_WR_DATA_BUF_WORDS = 16;

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

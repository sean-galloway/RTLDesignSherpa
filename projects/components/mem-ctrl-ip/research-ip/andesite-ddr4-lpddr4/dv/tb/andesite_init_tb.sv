// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// P1 integration wrapper: init_sequencer + dfi_cmd_formatter + mode_register,
// exposing the DFI 4.0 command pins to the BFM. Not a product module -- the
// P4 core supersedes it. See dv/tests/macro/test_andesite_init_slice.py.

`timescale 1ns / 1ps

module andesite_init_tb (
    input  logic        clk,
    input  logic        dfi_clk,
    input  logic        reset_n,

    input  logic [15:0] tinit1_csr,
    input  logic [15:0] tinit3_csr,
    input  logic [15:0] tinit4_csr,
    input  logic [15:0] tdllk_csr,
    input  logic [15:0] tzqinit_csr,
    input  logic [15:0] tmrd_csr,
    input  logic [15:0] tmod_csr,
    input  logic        geardown_en_csr,
    input  logic        parity_en_csr,
    input  logic [15:0] mr0_image_csr,
    input  logic [15:0] mr1_image_csr,
    input  logic [15:0] mr2_image_csr,
    input  logic [15:0] mr3_image_csr,
    input  logic [15:0] mr4_image_csr,
    input  logic [15:0] mr5_image_csr,
    input  logic [15:0] mr6_image_csr,

    output logic        phy_dfi_reset_n,
    output logic        phy_dfi_cke,
    // Named phy_dfi_cs_n (not the v4.0 'cs') because the DV framework's
    // DFISlavePHY monitor binds the legacy cs_n wire; cf. andesite_core_tb.sv.
    output logic [0:0]  phy_dfi_cs_n,
    output logic        phy_dfi_act_n,
    output logic        phy_dfi_ras_n,
    output logic        phy_dfi_cas_n,
    output logic        phy_dfi_we_n,
    output logic [1:0]  phy_dfi_bank,
    output logic [1:0]  phy_dfi_bg,
    output logic [17:0] phy_dfi_address,
    output logic        phy_dfi_parity_in,
    output logic        phy_dfi_geardown_en,
    // v4.0/DDR4 catalog-required data-path + ODT wires. P1 is init-only:
    // the DUT outputs idle constant, the BFM-driven read wires dangle.
    output logic [63:0] phy_dfi_wrdata,
    output logic [7:0]  phy_dfi_wrdata_mask,
    output logic [7:0]  phy_dfi_wrdata_en,
    output logic [0:0]  phy_dfi_odt,
    input  logic [63:0] phy_dfi_rddata,
    input  logic [7:0]  phy_dfi_rddata_en,
    input  logic        phy_dfi_rddata_valid,
    // v3.0 Error interface, v2.1 init handshake, and v2.1 update handshakes:
    // not exercised by this P1 slice (no error injection, no DFI init/update
    // choreography), but declared so the DV framework's per-version behavior
    // dispatch can bind them -- it samples ctrlupd_req/ctrlupd_ack/
    // phyupd_req/error/init_start/init_complete unconditionally (only the
    // alert_n/phyupd_type paths are presence-tolerant). MC-side outputs tie
    // to protocol idle (no request); PHY-side inputs dangle like the read
    // wires above (the BFM drives its own idle levels at construction).
    input  logic        phy_dfi_error,
    input  logic        phy_dfi_error_info,
    input  logic        phy_dfi_init_complete,
    input  logic        phy_dfi_ctrlupd_ack,
    input  logic        phy_dfi_phyupd_req,
    output logic        phy_dfi_init_start,
    output logic        phy_dfi_ctrlupd_req,
    output logic        phy_dfi_phyupd_ack,
    output logic        init_done,
    output logic        init_err
);

    import andesite_pkg::*;

    logic        w_mr_load;
    logic [15:0] w_mr_image;
    logic [2:0]  w_cmd_bank;
    logic        w_cmd_req, w_cmd_ack;
    dram_op_e    w_cmd_op;
    logic [17:0] w_cmd_addr;
    logic        w_parity_enable;
    logic        w_zq_cal_start;

    andesite_init_sequencer #() u_sequencer (
        .clk               (clk),
        .reset_n           (reset_n),
        .csr_init_trigger  (1'b0),
        .csr_memtype       (3'(MEMTYPE_DDR4)),
        .csr_geardown_en   (geardown_en_csr),
        .csr_parity_en     (parity_en_csr),
        .tinit1_csr        (tinit1_csr),
        .tinit3_csr        (tinit3_csr),
        .tinit4_csr        (tinit4_csr),
        .tdllk_csr         (tdllk_csr),
        .tzqinit_csr       (tzqinit_csr),
        .tmrd_csr          (tmrd_csr),
        .tmod_csr          (tmod_csr),
        .csr_mr0_image     (mr0_image_csr),
        .csr_mr1_image     (mr1_image_csr),
        .csr_mr2_image     (mr2_image_csr),
        .csr_mr3_image     (mr3_image_csr),
        .csr_mr4_image     (mr4_image_csr),
        .csr_mr5_image     (mr5_image_csr),
        .csr_mr6_image     (mr6_image_csr),
        .mr_image_out      (w_mr_image),
        .mr_load           (w_mr_load),
        .reset_n_out       (phy_dfi_reset_n),
        .cke_out           (phy_dfi_cke),
        .cmd_req           (w_cmd_req),
        .cmd_ack           (w_cmd_ack),
        .cmd_op            (w_cmd_op),
        .cmd_bank          (w_cmd_bank),
        .cmd_addr          (w_cmd_addr),
        .zq_cal_start      (w_zq_cal_start),
        .gear_down_entry   (phy_dfi_geardown_en),
        .parity_enable_out (w_parity_enable),
        .init_done         (init_done),
        .init_err          (init_err),
        .ca_train_start    (),
        // TASK-006 recovery pins: this smoke-level tb has no alert source;
        // grounded/open until the tb grows the parity scenario.
        .parity_alert_i     (1'b0),
        .recovery_interval_i(16'd0),
        .csr_telem_clear_i  (1'b0),
        .retract_req_o      (),
        .retract_ack_i      (1'b0),
        .obs_recovery_state_o(),
        .obs_alerts_seen_o  (),
        .obs_cmds_dropped_o (),
        .obs_cmds_resent_o  ()
    );

    andesite_dfi_cmd_formatter #() u_formatter (
        .clk           (clk),
        .rst_n         (reset_n),
        .op_i          (w_cmd_op),
        .bank_i        (w_cmd_bank[1:0]),
        // DDR4 MRS: the 3-bit MR index rides {BG0, BA1, BA0}; MR6 = 3'b110.
        .bg_i          ({1'b0, w_cmd_bank[2]}),
        .row_i         (18'h0),
        .col_i         (w_cmd_addr),
        .rank_i        (1'b0),
        .memtype_i     (MEMTYPE_DDR4),
        .parity_en_i   (w_parity_enable),
        .dfi_cs        (phy_dfi_cs_n),
        .dfi_act_n     (phy_dfi_act_n),
        .dfi_ras_n     (phy_dfi_ras_n),
        .dfi_cas_n     (phy_dfi_cas_n),
        .dfi_we_n      (phy_dfi_we_n),
        .dfi_bank      (phy_dfi_bank),
        .dfi_bg        (phy_dfi_bg),
        .dfi_address   (phy_dfi_address),
        // CKE ownership during init is the sequencer's (MAS Ch 3.2 seam); the
        // formatter's dfi_cke copy stays unconnected in this wrapper.
        .dfi_cke       (),
        .dfi_parity_in (phy_dfi_parity_in)
    );

    andesite_mode_register #() u_mode_register (
        .clk          (clk),
        .rst_n        (reset_n),
        .memtype_i    (MEMTYPE_DDR4),
        .rank_i       (1'b0),
        .wr_en_i      (w_mr_load),
        .wr_addr_i    ({3'b0, w_cmd_bank}),
        .wr_data_i    (w_mr_image),
        .rd_en_i      (1'b0),
        .rd_addr_i    (6'h0),
        .rd_data_o    (),
        .mr_sel_o     (),
        .mr_data_o    (),
        .mpr_page_o   (),
        .fgr_factor_o (),
        .rtt_nom_o    (),
        .rtt_wr_o     (),
        .rtt_park_o   (),
        .rd_dbi_en_o  (),
        .wr_dbi_en_o  (),
        .ca_parity_lat_o (),
        .wrlvl_en_o   (),
        .lpddr4_odt_o ()
    );

    assign phy_dfi_wrdata     = '0;
    assign phy_dfi_wrdata_mask = '0;
    assign phy_dfi_wrdata_en  = '0;
    assign phy_dfi_odt        = '0;
    // Protocol idle on the MC-side handshake outputs (see port comment).
    assign phy_dfi_init_start  = 1'b0;
    assign phy_dfi_ctrlupd_req = 1'b0;
    assign phy_dfi_phyupd_ack  = 1'b0;

    // The init slice owns the bus in P1: the formatter is a pure pipeline, so
    // the request is acknowledged combinationally (one-deep, never full).
    assign w_cmd_ack = w_cmd_req;

endmodule : andesite_init_tb

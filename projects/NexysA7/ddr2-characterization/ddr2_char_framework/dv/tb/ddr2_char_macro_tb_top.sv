// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Cocotb-side TB wrapper around ddr2_char_macro.
//
// Mirrors the pattern in projects/.../ddr2_lpddr2_top_tb_top.sv: APB stays
// as ports (APBMaster BFM drives via prefix), DFI is aliased to internal
// phy_dfi_* nets so the DFISlavePHY BFM auto-binds. AXI is fully internal
// to the macro (writer + reader engines drive it) — only the engine cfg
// ports and the controller's runtime externs come out.

`timescale 1ns / 1ps

module ddr2_char_macro_tb_top
    import ddr2_lpddr2_pkg::*;
#(
    parameter int AXI_ADDR_WIDTH   = 32,
    parameter int AXI_DATA_WIDTH   = 64,
    parameter int AXI_ID_WIDTH     = 4,
    parameter int AXI_USER_WIDTH   = 8,
    parameter int AXI_STRB_WIDTH   = AXI_DATA_WIDTH / 8,

    parameter int APB_ADDR_WIDTH   = 12,
    parameter int APB_DATA_WIDTH   = 32,
    parameter int APB_STRB_WIDTH   = APB_DATA_WIDTH / 8,
    parameter int APB_PROT_WIDTH   = 3,

    parameter int NUM_RANKS        = 1,
    parameter int NUM_BANKS        = 8,
    parameter int ROW_WIDTH        = 14,
    parameter int COL_WIDTH        = 10,
    parameter int PAGE_POLICY      = 1,

    parameter int DFI_RATE         = 2,
    parameter int DFI_DATA_WIDTH   = AXI_DATA_WIDTH * DFI_RATE,
    parameter int DFI_STRB_WIDTH   = AXI_STRB_WIDTH * DFI_RATE,
    parameter int DFI_EN_WIDTH     = DFI_RATE,
    parameter int DFI_VALID_WIDTH  = DFI_RATE,
    parameter int DFI_ADDR_BUS_W   = ROW_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W   = $clog2(NUM_BANKS) * DFI_RATE,
    parameter int DFI_CTRL_BUS_W   = 1 * DFI_RATE,
    parameter int DFI_CS_BUS_W     = NUM_RANKS * DFI_RATE,

    parameter int TXN_COUNT_WIDTH  = 16,
    parameter int INDEX_WIDTH      = 16,
    parameter int STRIDE_WIDTH     = 24,

    // Aliases
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH
) (
    input  logic                          mc_clk,
    input  logic                          mc_rst_n,
    input  logic                          pclk,
    input  logic                          presetn,

    // -------- Writer engine cfg ----------------------------------------
    input  logic [AW-1:0]                 cfg_wr_start_addr,
    input  logic signed [STRIDE_WIDTH-1:0] cfg_wr_addr_stride_0,
    input  logic signed [STRIDE_WIDTH-1:0] cfg_wr_addr_stride_1,
    input  logic [AW-1:0]                 cfg_wr_addr_wrap_mask_0,
    input  logic [AW-1:0]                 cfg_wr_addr_wrap_mask_1,
    input  logic [7:0]                    cfg_wr_burst_len,
    input  logic [TXN_COUNT_WIDTH-1:0]    cfg_wr_txn_count,
    input  logic [IW-1:0]                 cfg_wr_axi_id,
    input  logic [1:0]                    cfg_wr_id_mode,
    input  logic [2:0]                    cfg_wr_axi_size,
    input  logic [1:0]                    cfg_wr_axi_burst,
    input  logic [31:0]                   cfg_wr_lfsr_seed,
    input  logic                          cfg_wr_data_mode,
    input  logic [31:0]                   cfg_wr_hash_seed0,
    input  logic [31:0]                   cfg_wr_hash_seed1,
    input  logic [31:0]                   cfg_wr_hash_seed2,
    input  logic [3:0]                    cfg_wr_gap,
    input  logic                          cfg_wr_start,
    output logic                          cfg_wr_done,
    output logic [31:0]                   o_expected_crc,
    output logic                          o_expected_crc_valid,
    output logic                          o_bresp_error,

    // -------- Reader engine cfg ----------------------------------------
    input  logic [AW-1:0]                 cfg_rd_start_addr,
    input  logic signed [STRIDE_WIDTH-1:0] cfg_rd_addr_stride_0,
    input  logic signed [STRIDE_WIDTH-1:0] cfg_rd_addr_stride_1,
    input  logic [AW-1:0]                 cfg_rd_addr_wrap_mask_0,
    input  logic [AW-1:0]                 cfg_rd_addr_wrap_mask_1,
    input  logic [7:0]                    cfg_rd_burst_len,
    input  logic [TXN_COUNT_WIDTH-1:0]    cfg_rd_txn_count,
    input  logic [IW-1:0]                 cfg_rd_axi_id,
    input  logic [1:0]                    cfg_rd_id_mode,
    input  logic [2:0]                    cfg_rd_axi_size,
    input  logic [1:0]                    cfg_rd_axi_burst,
    input  logic [31:0]                   cfg_rd_lfsr_seed,
    input  logic                          cfg_rd_data_mode,
    input  logic [31:0]                   cfg_rd_hash_seed0,
    input  logic [31:0]                   cfg_rd_hash_seed1,
    input  logic [31:0]                   cfg_rd_hash_seed2,
    input  logic [3:0]                    cfg_rd_gap,
    input  logic                          cfg_rd_start,
    output logic                          cfg_rd_done,
    output logic [31:0]                   o_actual_crc,
    output logic                          o_actual_crc_valid,
    output logic                          o_data_error,
    output logic                          o_rresp_error,
    output logic [TXN_COUNT_WIDTH-1:0]    o_beats_mismatched,

    // -------- APB CSR (BFM-driven) -------------------------------------
    input  logic                          s_apb_PSEL,
    input  logic                          s_apb_PENABLE,
    output logic                          s_apb_PREADY,
    input  logic [APB_ADDR_WIDTH-1:0]     s_apb_PADDR,
    input  logic                          s_apb_PWRITE,
    input  logic [APB_DATA_WIDTH-1:0]     s_apb_PWDATA,
    input  logic [APB_STRB_WIDTH-1:0]     s_apb_PSTRB,
    input  logic [APB_PROT_WIDTH-1:0]     s_apb_PPROT,
    output logic [APB_DATA_WIDTH-1:0]     s_apb_PRDATA,
    output logic                          s_apb_PSLVERR,

    // -------- Runtime externs ------------------------------------------
    input  memtype_e                      memtype_i,
    input  logic [7:0]                    t_phy_wrlat_i,
    input  logic [7:0]                    t_rddata_en_i,
    input  logic                          rd_in_order_i,
    input  logic [3:0]                    cap_lookahead_max_i,
    input  logic [3:0]                    cap_synth_mask_i
);

    //=========================================================================
    // PHY-side DFI bus — exposed as internal phy_dfi_* nets so the
    // DFISlavePHY BFM auto-binds with prefix=phy_dfi.
    //=========================================================================
    logic [DFI_ADDR_BUS_W-1:0]   phy_dfi_address;
    logic [DFI_BANK_BUS_W-1:0]   phy_dfi_bank;
    logic [DFI_CTRL_BUS_W-1:0]   phy_dfi_cas_n;
    logic [DFI_CTRL_BUS_W-1:0]   phy_dfi_ras_n;
    logic [DFI_CTRL_BUS_W-1:0]   phy_dfi_we_n;
    logic [DFI_CS_BUS_W-1:0]     phy_dfi_cs_n;
    logic [DFI_CS_BUS_W-1:0]     phy_dfi_cke;
    logic [DFI_CS_BUS_W-1:0]     phy_dfi_odt;
    logic [DFI_DATA_WIDTH-1:0]   phy_dfi_wrdata;
    logic [DFI_EN_WIDTH-1:0]     phy_dfi_wrdata_en;
    logic [DFI_STRB_WIDTH-1:0]   phy_dfi_wrdata_mask;
    logic [DFI_EN_WIDTH-1:0]     phy_dfi_rddata_en;
    logic [DFI_CS_BUS_W-1:0]     phy_dfi_dram_clk_disable;
    logic                        phy_dfi_init_start;
    logic                        phy_dfi_ctrlupd_req;
    logic                        phy_dfi_phyupd_ack;

    // PHY-driven (BFM-owned) inputs to the DUT
    logic [DFI_DATA_WIDTH-1:0]   phy_dfi_rddata;
    logic [DFI_VALID_WIDTH-1:0]  phy_dfi_rddata_valid;
    logic                        phy_dfi_init_complete;
    logic                        phy_dfi_ctrlupd_ack;
    logic                        phy_dfi_phyupd_req;
    logic [1:0]                  phy_dfi_phyupd_type;

    // v3+ signals — declared so the BFM's cocotb-bus binding succeeds.
    logic                        phy_dfi_error;
    logic                        phy_dfi_error_info;
    logic                        phy_dfi_crc_alert;
    logic                        phy_dfi_training_active;
    logic                        phy_dfi_training_phase;
    logic                        phy_dfi_parity_check;
    logic                        phy_dfi_freq_change_ack;
    logic                        phy_dfi_freq_change_req;
    logic                        phy_dfi_disconnect_req;
    logic                        phy_dfi_phymstr_req;

    //=========================================================================
    // DUT — the engines + controller macro
    //=========================================================================
    ddr2_char_macro #(
        .AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .AXI_USER_WIDTH  (AXI_USER_WIDTH),
        .APB_ADDR_WIDTH  (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH  (APB_DATA_WIDTH),
        .NUM_RANKS       (NUM_RANKS),
        .NUM_BANKS       (NUM_BANKS),
        .ROW_WIDTH       (ROW_WIDTH),
        .COL_WIDTH       (COL_WIDTH),
        .DFI_RATE        (DFI_RATE),
        .PAGE_POLICY     (PAGE_POLICY),
        .TXN_COUNT_WIDTH (TXN_COUNT_WIDTH),
        .INDEX_WIDTH     (INDEX_WIDTH),
        .STRIDE_WIDTH    (STRIDE_WIDTH)
    ) u_dut (
        .mc_clk                  (mc_clk),
        .mc_rst_n                (mc_rst_n),
        .pclk                    (pclk),
        .presetn                 (presetn),

        // Writer cfg
        .cfg_wr_start_addr       (cfg_wr_start_addr),
        .cfg_wr_addr_stride_0    (cfg_wr_addr_stride_0),
        .cfg_wr_addr_stride_1    (cfg_wr_addr_stride_1),
        .cfg_wr_addr_wrap_mask_0 (cfg_wr_addr_wrap_mask_0),
        .cfg_wr_addr_wrap_mask_1 (cfg_wr_addr_wrap_mask_1),
        .cfg_wr_burst_len        (cfg_wr_burst_len),
        .cfg_wr_txn_count        (cfg_wr_txn_count),
        .cfg_wr_axi_id           (cfg_wr_axi_id),
        .cfg_wr_id_mode          (cfg_wr_id_mode),
        .cfg_wr_axi_size         (cfg_wr_axi_size),
        .cfg_wr_axi_burst        (cfg_wr_axi_burst),
        .cfg_wr_lfsr_seed        (cfg_wr_lfsr_seed),
        .cfg_wr_data_mode        (cfg_wr_data_mode),
        .cfg_wr_hash_seed0       (cfg_wr_hash_seed0),
        .cfg_wr_hash_seed1       (cfg_wr_hash_seed1),
        .cfg_wr_hash_seed2       (cfg_wr_hash_seed2),
        .cfg_wr_gap              (cfg_wr_gap),
        .cfg_wr_start            (cfg_wr_start),
        .cfg_wr_done             (cfg_wr_done),
        .o_expected_crc          (o_expected_crc),
        .o_expected_crc_valid    (o_expected_crc_valid),
        .o_bresp_error           (o_bresp_error),

        // Reader cfg
        .cfg_rd_start_addr       (cfg_rd_start_addr),
        .cfg_rd_addr_stride_0    (cfg_rd_addr_stride_0),
        .cfg_rd_addr_stride_1    (cfg_rd_addr_stride_1),
        .cfg_rd_addr_wrap_mask_0 (cfg_rd_addr_wrap_mask_0),
        .cfg_rd_addr_wrap_mask_1 (cfg_rd_addr_wrap_mask_1),
        .cfg_rd_burst_len        (cfg_rd_burst_len),
        .cfg_rd_txn_count        (cfg_rd_txn_count),
        .cfg_rd_axi_id           (cfg_rd_axi_id),
        .cfg_rd_id_mode          (cfg_rd_id_mode),
        .cfg_rd_axi_size         (cfg_rd_axi_size),
        .cfg_rd_axi_burst        (cfg_rd_axi_burst),
        .cfg_rd_lfsr_seed        (cfg_rd_lfsr_seed),
        .cfg_rd_data_mode        (cfg_rd_data_mode),
        .cfg_rd_hash_seed0       (cfg_rd_hash_seed0),
        .cfg_rd_hash_seed1       (cfg_rd_hash_seed1),
        .cfg_rd_hash_seed2       (cfg_rd_hash_seed2),
        .cfg_rd_gap              (cfg_rd_gap),
        .cfg_rd_start            (cfg_rd_start),
        .cfg_rd_done             (cfg_rd_done),
        .o_actual_crc            (o_actual_crc),
        .o_actual_crc_valid      (o_actual_crc_valid),
        .o_data_error            (o_data_error),
        .o_rresp_error           (o_rresp_error),
        .o_beats_mismatched      (o_beats_mismatched),

        // APB passthrough
        .s_apb_PSEL              (s_apb_PSEL),
        .s_apb_PENABLE           (s_apb_PENABLE),
        .s_apb_PREADY            (s_apb_PREADY),
        .s_apb_PADDR             (s_apb_PADDR),
        .s_apb_PWRITE            (s_apb_PWRITE),
        .s_apb_PWDATA            (s_apb_PWDATA),
        .s_apb_PSTRB             (s_apb_PSTRB),
        .s_apb_PPROT             (s_apb_PPROT),
        .s_apb_PRDATA            (s_apb_PRDATA),
        .s_apb_PSLVERR           (s_apb_PSLVERR),

        // DFI alias — macro dfi_* ↔ phy_dfi_* (BFM-side naming)
        .dfi_address_o           (phy_dfi_address),
        .dfi_bank_o              (phy_dfi_bank),
        .dfi_cas_n_o             (phy_dfi_cas_n),
        .dfi_ras_n_o             (phy_dfi_ras_n),
        .dfi_we_n_o              (phy_dfi_we_n),
        .dfi_cs_n_o              (phy_dfi_cs_n),
        .dfi_cke_o               (phy_dfi_cke),
        .dfi_odt_o               (phy_dfi_odt),
        .dfi_wrdata_o            (phy_dfi_wrdata),
        .dfi_wrdata_en_o         (phy_dfi_wrdata_en),
        .dfi_wrdata_mask_o       (phy_dfi_wrdata_mask),
        .dfi_rddata_en_o         (phy_dfi_rddata_en),
        .dfi_rddata_i            (phy_dfi_rddata),
        .dfi_rddata_valid_i      (phy_dfi_rddata_valid),
        .dfi_dram_clk_disable_o  (phy_dfi_dram_clk_disable),
        .dfi_init_start_o        (phy_dfi_init_start),
        .dfi_init_complete_i     (phy_dfi_init_complete),
        .dfi_ctrlupd_req_o       (phy_dfi_ctrlupd_req),
        .dfi_ctrlupd_ack_i       (phy_dfi_ctrlupd_ack),
        .dfi_phyupd_req_i        (phy_dfi_phyupd_req),
        .dfi_phyupd_ack_o        (phy_dfi_phyupd_ack),
        .dfi_phyupd_type_i       (phy_dfi_phyupd_type),

        // Runtime externs
        .memtype_i               (memtype_i),
        .t_phy_wrlat_i           (t_phy_wrlat_i),
        .t_rddata_en_i           (t_rddata_en_i),
        .rd_in_order_i           (rd_in_order_i),
        .cap_lookahead_max_i     (cap_lookahead_max_i),
        .cap_synth_mask_i        (cap_synth_mask_i)
    );

    // Silence Verilator's unused-output warnings for unused phy_dfi_* lines.
    wire unused = |{ phy_dfi_error, phy_dfi_error_info, phy_dfi_crc_alert,
                     phy_dfi_training_active, phy_dfi_training_phase,
                     phy_dfi_parity_check, phy_dfi_freq_change_ack,
                     phy_dfi_freq_change_req, phy_dfi_disconnect_req,
                     phy_dfi_phymstr_req,
                     phy_dfi_init_start, phy_dfi_dram_clk_disable,
                     phy_dfi_ctrlupd_req, phy_dfi_phyupd_ack };

endmodule : ddr2_char_macro_tb_top

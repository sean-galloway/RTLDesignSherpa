// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Cocotb-side TB wrapper around ddr2_char_macro.
//
// Mirrors the pattern in projects/.../pumice_top_tb_top.sv: APB stays
// as ports (APBMaster BFM drives via prefix), DFI is aliased to internal
// phy_dfi_* nets so the DFISlavePHY BFM auto-binds. AXI is fully internal
// to the macro (writer + reader engines drive it) — only the engine cfg
// ports and the controller's runtime externs come out.

`timescale 1ns / 1ps

module ddr2_char_macro_tb_top
    import pumice_pkg::*;
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
    // BOARD GEOMETRY. The Nexys A7 carries an MT47H64M16 -- x16 -- behind a
    // 32-bit pumice DRAM beat. Both numbers matter and they are NOT the same:
    //   BL_SHIFT          = clog2(beat/device)  scales JEDEC BL into pumice beats
    //   BYTE_OFFSET_WIDTH = clog2(device/8)     sets the column granularity
    // Setting only one of them models a device the board does not have. The
    // DFI bus widths below derive from the BEAT width, not the AXI width --
    // they are different quantities and only coincided while beat == AXI.
    parameter int DRAM_BEAT_WIDTH  = 32,
    parameter int DRAM_DEVICE_WIDTH = 16,
    parameter int DRAM_BL          = 8,
    parameter int DFI_DATA_WIDTH   = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int DFI_STRB_WIDTH   = (DRAM_BEAT_WIDTH / 8) * DFI_RATE,
    parameter int DFI_EN_WIDTH     = DFI_RATE,
    parameter int DFI_VALID_WIDTH  = DFI_RATE,
    parameter int DFI_ADDR_BUS_W   = ROW_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W   = $clog2(NUM_BANKS) * DFI_RATE,
    parameter int DFI_CTRL_BUS_W   = 1 * DFI_RATE,
    parameter int DFI_CS_BUS_W     = NUM_RANKS * DFI_RATE,

    parameter int TXN_COUNT_WIDTH  = 16,
    parameter int INDEX_WIDTH      = 16,
    parameter int STRIDE_WIDTH     = 24,

    parameter int RD_DBG_FIFO_DEPTH = 0,

    // Aliases
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH
) (
    input  logic                          mc_clk,
    input  logic                          mc_rst_n,
    input  logic                          pclk,
    input  logic                          presetn,

    // -------- Generator config: a second APB window ---------------------
    // The flat cfg_wr_* / cfg_rd_* ports are gone. There are sixteen engines
    // now, so their config lives in chargen_regs inside the macro and the
    // bench programs it the way the board does -- over APB, by register name
    // through the generated regmap. That is the point of driving it this way
    // rather than poking ports: the sim exercises the SAME path the host uses,
    // so a register that decodes wrong fails here instead of on silicon.
    input  logic                          s_chargen_apb_PSEL,
    input  logic                          s_chargen_apb_PENABLE,
    output logic                          s_chargen_apb_PREADY,
    input  logic [APB_ADDR_WIDTH-1:0]     s_chargen_apb_PADDR,
    input  logic                          s_chargen_apb_PWRITE,
    input  logic [APB_DATA_WIDTH-1:0]     s_chargen_apb_PWDATA,
    input  logic [APB_STRB_WIDTH-1:0]     s_chargen_apb_PSTRB,
    input  logic [APB_PROT_WIDTH-1:0]     s_chargen_apb_PPROT,
    output logic [APB_DATA_WIDTH-1:0]     s_chargen_apb_PRDATA,
    output logic                          s_chargen_apb_PSLVERR,

    // -------- Run-level aggregates --------------------------------------
    // Per-generator status is read back over the APB window above. These are
    // the whole-run rollups, exposed as pins so a test can wait on them
    // without polling a register in a loop.
    output logic                          gen_wr_started,
    output logic                          gen_rd_started,
    output logic                          gen_wr_done,
    output logic                          gen_rd_done,
    output logic                          gen_any_error,
    output logic                          gen_crc_match,

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
    input  logic [3:0]                    cap_synth_mask_i,

    // ----- Reader-engine debug FIFO drain (only when RD_DBG_FIFO_DEPTH>0) -----
    output logic                          rd_dbg_valid,
    input  logic                          rd_dbg_ready,
    output logic [DW-1:0]                 rd_dbg_actual,
    output logic [DW-1:0]                 rd_dbg_expected,
    output logic                          rd_dbg_mismatch
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
        .DRAM_BEAT_WIDTH   (DRAM_BEAT_WIDTH),
        .DRAM_DEVICE_WIDTH (DRAM_DEVICE_WIDTH),
        .DRAM_BL         (DRAM_BL),
        .PAGE_POLICY     (PAGE_POLICY),
        .TXN_COUNT_WIDTH (TXN_COUNT_WIDTH),
        .INDEX_WIDTH     (INDEX_WIDTH),
        .STRIDE_WIDTH    (STRIDE_WIDTH),
        .RD_DBG_FIFO_DEPTH (RD_DBG_FIFO_DEPTH)
    ) u_dut (
        .mc_clk                  (mc_clk),
        .mc_rst_n                (mc_rst_n),
        .pclk                    (pclk),
        .presetn                 (presetn),

        // Writer cfg
        .s_chargen_apb_PSEL      (s_chargen_apb_PSEL),
        .s_chargen_apb_PENABLE   (s_chargen_apb_PENABLE),
        .s_chargen_apb_PREADY    (s_chargen_apb_PREADY),
        .s_chargen_apb_PADDR     (s_chargen_apb_PADDR),
        .s_chargen_apb_PWRITE    (s_chargen_apb_PWRITE),
        .s_chargen_apb_PWDATA    (s_chargen_apb_PWDATA),
        .s_chargen_apb_PSTRB     (s_chargen_apb_PSTRB),
        .s_chargen_apb_PPROT     (s_chargen_apb_PPROT),
        .s_chargen_apb_PRDATA    (s_chargen_apb_PRDATA),
        .s_chargen_apb_PSLVERR   (s_chargen_apb_PSLVERR),

        .gen_wr_started          (gen_wr_started),
        .gen_rd_started          (gen_rd_started),
        .gen_wr_done             (gen_wr_done),
        .gen_rd_done             (gen_rd_done),
        .gen_any_error           (gen_any_error),
        .gen_crc_match           (gen_crc_match),

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
        .cap_synth_mask_i        (cap_synth_mask_i),
        .rd_dbg_valid            (rd_dbg_valid),
        .rd_dbg_ready            (rd_dbg_ready),
        .rd_dbg_actual           (rd_dbg_actual),
        .rd_dbg_expected         (rd_dbg_expected),
        .rd_dbg_mismatch         (rd_dbg_mismatch),

        // Perf / latency-histogram instrumentation ports (added to
        // ddr2_char_macro for the UART characterization flow). This sim TB
        // does not exercise them — tie inputs off and leave outputs open.
        .perf_clear              (1'b0),
        .perf_freeze             (1'b0),
        .perf_wr_prod            (),
        .perf_wr_bp              (),
        .perf_wr_starv           (),
        .perf_wr_idle            (),
        .perf_rd_prod            (),
        .perf_rd_bp              (),
        .perf_rd_starv           (),
        .perf_rd_idle            (),
        .i_hist_metric           (1'b0),
        .i_hist_bin              (4'd0),
        .perf_wr_hist_count      (),
        .perf_wr_hist_total      (),
        .perf_rd_hist_count      (),
        .perf_rd_hist_total      ()
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

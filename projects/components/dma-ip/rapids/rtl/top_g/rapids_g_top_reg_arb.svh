// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// rapids_g_top_reg_arb.svh -- who pushes into the register block's command
// queue in rapids-g (rapids TASK-034), hand-written. bin/gen_rapids_g.py
// includes it in the generated rapids_g_top_base right after apb4_slave,
// whose cmd/rsp outputs it renames to host_*.
//
// Three masters share the one cmd/rsp path (MON-window guard ->
// peakrdl_to_cmdrsp -> rapids_regs): the host's APB, the SOURCE half's
// gatling and the SINK half's gatling. A gatling's address is a byte offset
// in its own half, pinned here: SRC at 0x0000, SNK at 0x1000 (paddr[12]), so
// neither can reach the other half. One access is outstanding at a time.

    logic                          host_cmd_valid, host_cmd_ready, host_cmd_pwrite;
    logic [APB_ADDR_WIDTH-1:0]     host_cmd_paddr;
    logic [APB_DATA_WIDTH-1:0]     host_cmd_pwdata;
    logic                          host_rsp_valid, host_rsp_ready, host_rsp_pslverr;
    logic [APB_DATA_WIDTH-1:0]     host_rsp_prdata;

    logic                          w_src_seq_reg_cmd_valid, w_src_seq_reg_cmd_ready, w_src_seq_reg_cmd_pwrite;
    logic [11:0]                   w_src_seq_reg_cmd_paddr;
    logic [31:0]                   w_src_seq_reg_cmd_pwdata;
    logic                          w_src_seq_reg_rsp_valid, w_src_seq_reg_rsp_ready, w_src_seq_reg_rsp_pslverr;
    logic [31:0]                   w_src_seq_reg_rsp_prdata;
    logic                          w_snk_seq_reg_cmd_valid, w_snk_seq_reg_cmd_ready, w_snk_seq_reg_cmd_pwrite;
    logic [11:0]                   w_snk_seq_reg_cmd_paddr;
    logic [31:0]                   w_snk_seq_reg_cmd_pwdata;
    logic                          w_snk_seq_reg_rsp_valid, w_snk_seq_reg_rsp_ready, w_snk_seq_reg_rsp_pslverr;
    logic [31:0]                   w_snk_seq_reg_rsp_prdata;

    logic [2:0]                    w_ra_rsp_valid;
    logic [APB_DATA_WIDTH-1:0]     w_ra_rsp_prdata;
    logic                          w_ra_rsp_pslverr;
    logic [2:0]                    w_ra_cmd_ready;

    initial begin
        if (APB_ADDR_WIDTH != 13 || APB_DATA_WIDTH != 32)
            $fatal(1, "rapids_g_top_base: the gatling register path needs a 13-bit, 32-bit APB map (the 8- and 16-channel maps both are)");
    end

    rapids_g_reg_arb #(
        .NM         (3),
        .ADDR_WIDTH (APB_ADDR_WIDTH),
        .DATA_WIDTH (APB_DATA_WIDTH)
    ) u_reg_arb (
        .clk           (aclk),
        .rst_n         (w_aresetn),
        .m_cmd_valid   ({w_snk_seq_reg_cmd_valid, w_src_seq_reg_cmd_valid, host_cmd_valid}),
        .m_cmd_ready   (w_ra_cmd_ready),
        .m_cmd_pwrite  ({w_snk_seq_reg_cmd_pwrite, w_src_seq_reg_cmd_pwrite, host_cmd_pwrite}),
        .m_cmd_paddr   ({{1'b1, w_snk_seq_reg_cmd_paddr}, {1'b0, w_src_seq_reg_cmd_paddr}, host_cmd_paddr}),
        .m_cmd_pwdata  ({w_snk_seq_reg_cmd_pwdata, w_src_seq_reg_cmd_pwdata, host_cmd_pwdata}),
        .m_rsp_valid   (w_ra_rsp_valid),
        .m_rsp_ready   ({w_snk_seq_reg_rsp_ready, w_src_seq_reg_rsp_ready, host_rsp_ready}),
        .m_rsp_prdata  (w_ra_rsp_prdata),
        .m_rsp_pslverr (w_ra_rsp_pslverr),
        .s_cmd_valid   (apb_cmd_valid),
        .s_cmd_ready   (apb_cmd_ready),
        .s_cmd_pwrite  (apb_cmd_pwrite),
        .s_cmd_paddr   (apb_cmd_paddr),
        .s_cmd_pwdata  (apb_cmd_pwdata),
        .s_rsp_valid   (apb_rsp_valid),
        .s_rsp_ready   (apb_rsp_ready),
        .s_rsp_prdata  (apb_rsp_prdata),
        .s_rsp_pslverr (apb_rsp_pslverr)
    );

    assign {w_snk_seq_reg_cmd_ready, w_src_seq_reg_cmd_ready, host_cmd_ready} = w_ra_cmd_ready;
    assign {w_snk_seq_reg_rsp_valid, w_src_seq_reg_rsp_valid, host_rsp_valid} = w_ra_rsp_valid;
    assign host_rsp_prdata           = w_ra_rsp_prdata;
    assign host_rsp_pslverr          = w_ra_rsp_pslverr;
    assign w_src_seq_reg_rsp_prdata  = w_ra_rsp_prdata;
    assign w_src_seq_reg_rsp_pslverr = w_ra_rsp_pslverr;
    assign w_snk_seq_reg_rsp_prdata  = w_ra_rsp_prdata;
    assign w_snk_seq_reg_rsp_pslverr = w_ra_rsp_pslverr;

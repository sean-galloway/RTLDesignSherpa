// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// stream_g_top_reg_arb.svh -- who pushes into the register block's command
// queue in stream-g (stream TASK-020), hand-written. bin/gen_stream_g.py
// includes it in the generated stream_g_top_ch{8,16} just BEFORE the APB
// slave's generate block, whose cmd/rsp connections it renames to host_*:
// the host_* nets are declared here, and a declaration after the instances
// leaves Vivado with implicit undriven nets (the board found that one).
//
// Two masters share the one cmd/rsp path (MON-window guard ->
// peakrdl_to_cmdrsp -> stream_regs): the host's APB and the core's gatling.
// The gatling's address is a 12-bit byte offset in the config window,
// zero-extended to the APB width here (so with a 13-bit map paddr[12] = 0: it
// cannot reach the monitor window; the 12-bit maps the tests build have none). One access is outstanding at a time: the path is SERIALIZED, one
// agent owns it from its command to its response (rapids_g_reg_arb).

    logic                          host_cmd_valid, host_cmd_ready, host_cmd_pwrite;
    logic [APB_ADDR_WIDTH-1:0]     host_cmd_paddr;
    logic [APB_DATA_WIDTH-1:0]     host_cmd_pwdata;
    logic [(APB_DATA_WIDTH/8)-1:0] host_cmd_pstrb;
    logic                          host_rsp_valid, host_rsp_ready, host_rsp_pslverr;
    logic [APB_DATA_WIDTH-1:0]     host_rsp_prdata;

    logic                          w_seq_reg_cmd_valid, w_seq_reg_cmd_ready, w_seq_reg_cmd_pwrite;
    logic [11:0]                   w_seq_reg_cmd_paddr;
    logic [31:0]                   w_seq_reg_cmd_pwdata;
    logic                          w_seq_reg_rsp_valid, w_seq_reg_rsp_ready, w_seq_reg_rsp_pslverr;
    logic [31:0]                   w_seq_reg_rsp_prdata;

    logic [1:0]                    w_ra_rsp_valid;
    logic [APB_DATA_WIDTH-1:0]     w_ra_rsp_prdata;
    logic                          w_ra_rsp_pslverr;
    logic [1:0]                    w_ra_cmd_ready;

    initial begin
        if (APB_ADDR_WIDTH < 12 || APB_DATA_WIDTH != 32)
            $fatal(1, "stream_g top: the gatling register path needs at least a 12-bit, 32-bit APB map");
    end

    // The host's strobe is whole-word on the gatling side too: every path
    // below the arbiter writes whole words (peakrdl_to_cmdrsp takes all-ones).
    assign apb_cmd_pstrb = host_cmd_pstrb;

    rapids_g_reg_arb #(
        .NM         (2),
        .ADDR_WIDTH (APB_ADDR_WIDTH),
        .DATA_WIDTH (APB_DATA_WIDTH)
    ) u_reg_arb (
        .clk           (aclk),
        .rst_n         (aresetn),
        .m_cmd_valid   ({w_seq_reg_cmd_valid, host_cmd_valid}),
        .m_cmd_ready   (w_ra_cmd_ready),
        .m_cmd_pwrite  ({w_seq_reg_cmd_pwrite, host_cmd_pwrite}),
        .m_cmd_paddr   ({APB_ADDR_WIDTH'(w_seq_reg_cmd_paddr), host_cmd_paddr}),
        .m_cmd_pwdata  ({w_seq_reg_cmd_pwdata, host_cmd_pwdata}),
        .m_rsp_valid   (w_ra_rsp_valid),
        .m_rsp_ready   ({w_seq_reg_rsp_ready, host_rsp_ready}),
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

    assign {w_seq_reg_cmd_ready, host_cmd_ready} = w_ra_cmd_ready;
    assign {w_seq_reg_rsp_valid, host_rsp_valid} = w_ra_rsp_valid;
    assign host_rsp_prdata       = w_ra_rsp_prdata;
    assign host_rsp_pslverr      = w_ra_rsp_pslverr;
    assign w_seq_reg_rsp_prdata  = w_ra_rsp_prdata;
    assign w_seq_reg_rsp_pslverr = w_ra_rsp_pslverr;

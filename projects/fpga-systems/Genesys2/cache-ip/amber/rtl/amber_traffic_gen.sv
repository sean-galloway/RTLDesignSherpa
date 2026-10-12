// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: amber_traffic_gen
// Purpose: Per-core stimulus engine for the amber pair-rig Genesys2 bring-up.
//   AXI4-Lite CSR slave (16-word regfile) drives a deterministic LFSR-based
//   cpu_req GAXI master. One outstanding transaction at a time; counts accepts
//   and responses; raises ERR_FLAG if a response never arrives.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module amber_traffic_gen
    import l1_pkg::*;
#(
    parameter int ADDR_WIDTH = AMBER_ADDR_WIDTH,
    parameter int BUS_WIDTH  = AMBER_BUS_WIDTH,
    parameter bit USE_MONITOR = 1'b1,
    localparam int STRB_W    = BUS_WIDTH / 8,
    localparam int CPU_REQ_W = ADDR_WIDTH + 1 + STRB_W + BUS_WIDTH,
    localparam int CPU_RSP_W = BUS_WIDTH
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // ------------------------------------------------------------------
    // AXIL slave (host config / status)
    // ------------------------------------------------------------------
    input  logic [31:0]             s_axil_awaddr,
    input  logic [2:0]              s_axil_awprot,
    input  logic                    s_axil_awvalid,
    output logic                    s_axil_awready,
    input  logic [31:0]             s_axil_wdata,
    input  logic [3:0]              s_axil_wstrb,
    input  logic                    s_axil_wvalid,
    output logic                    s_axil_wready,
    output logic [1:0]              s_axil_bresp,
    output logic                    s_axil_bvalid,
    input  logic                    s_axil_bready,

    input  logic [31:0]             s_axil_araddr,
    input  logic [2:0]              s_axil_arprot,
    input  logic                    s_axil_arvalid,
    output logic                    s_axil_arready,
    output logic [31:0]             s_axil_rdata,
    output logic [1:0]              s_axil_rresp,
    output logic                    s_axil_rvalid,
    input  logic                    s_axil_rready,

    // ------------------------------------------------------------------
    // cpu_req GAXI master (packed {addr, we, be, wdata})
    // ------------------------------------------------------------------
    output logic                    cpu_req_wr_valid,
    input  logic                    cpu_req_wr_ready,
    output logic [CPU_REQ_W-1:0]    cpu_req_wr_data,
    input  logic                    cpu_rsp_rd_valid,
    output logic                    cpu_rsp_rd_ready,
    input  logic [CPU_RSP_W-1:0]    cpu_rsp_rd_data,

    // ------------------------------------------------------------------
    // Status outputs to the harness aggregate
    // ------------------------------------------------------------------
    output logic                    o_done,
    output logic                    o_busy,
    output logic                    o_err_flag
);

    // ------------------------------------------------------------------
    // CSR map (32-bit word offsets)
    // ------------------------------------------------------------------
    localparam int CSR_CTRL          = 4'h0;
    localparam int CSR_SEED          = 4'h1;
    localparam int CSR_ADDR_BASE     = 4'h2;
    localparam int CSR_ADDR_MASK     = 4'h3;
    localparam int CSR_TRANS_COUNT   = 4'h4;
    localparam int CSR_STATUS        = 4'h5;
    localparam int CSR_ACC_COUNT     = 4'h6;
    localparam int CSR_RSP_COUNT     = 4'h7;
    localparam int CSR_ERR_FLAG      = 4'h8;
    localparam int CSR_RSP_CKSUM_LO  = 4'hC;   // word 12
    localparam int CSR_RSP_CKSUM_HI  = 4'hD;   // word 13
    localparam int CSR_WDATA_CKSUM_LO= 4'hE;   // word 14
    localparam int CSR_WDATA_CKSUM_HI= 4'hF;   // word 15

    localparam logic [31:0] CSR_CTRL_RUN_MASK     = 32'h0000_0001;
    localparam int          CSR_CTRL_WE_MIX_SHIFT = 8;

    // ------------------------------------------------------------------
    // CSR registers
    // ------------------------------------------------------------------
    logic [31:0] r_ctrl;
    logic [31:0] r_seed;
    logic [31:0] r_addr_base;
    logic [31:0] r_addr_mask;
    logic [31:0] r_trans_count;
    logic [31:0] r_acc_count;
    logic [31:0] r_rsp_count;
    logic        r_done;
    logic        r_busy;
    logic        r_err_flag;
    logic [BUS_WIDTH-1:0] r_rsp_cksum;
    logic [BUS_WIDTH-1:0] r_wdata_cksum;

    assign o_done     = r_done;
    assign o_busy     = r_busy;
    assign o_err_flag = r_err_flag;

    // ------------------------------------------------------------------
    // LFSR state (32-bit Galois, taps 32,22,2,1)
    // ------------------------------------------------------------------
    logic [31:0] r_lfsr;
    logic [31:0] w_lfsr_next;

    assign w_lfsr_next = {r_lfsr[30:0],
                          r_lfsr[31] ^ r_lfsr[21] ^ r_lfsr[1] ^ r_lfsr[0]};

    // ------------------------------------------------------------------
    // Stimulus FSM
    // ------------------------------------------------------------------
    typedef enum logic [1:0] {
        FSM_IDLE,
        FSM_ISSUE,
        FSM_WAIT_RSP
    } fsm_state_t;

    fsm_state_t r_fsm;

    // Timeout while waiting for response (large but finite)
    localparam int TIMEOUT_BITS = 24;
    logic [TIMEOUT_BITS-1:0] r_timeout_cnt;

    // ------------------------------------------------------------------
    // Combinational request fields (presented immediately in ISSUE)
    // ------------------------------------------------------------------
    logic [7:0]            w_we_mix;
    logic                  w_do_write;
    logic [STRB_W-1:0]     w_write_be;
    logic [BUS_WIDTH-1:0]  w_wdata;
    logic [ADDR_WIDTH-1:0] w_addr;

    assign w_we_mix   = r_ctrl[15:8];
    assign w_do_write = (r_lfsr[7:0] < w_we_mix);

    always_comb begin
        if (w_do_write) begin
            w_write_be = STRB_W'(r_lfsr);
            if (w_write_be == '0) w_write_be = {{(STRB_W-1){1'b0}}, 1'b1};
        end else begin
            w_write_be = {STRB_W{1'b1}};
        end
    end

    assign w_wdata = BUS_WIDTH'(r_lfsr);
    assign w_addr  = ADDR_WIDTH'(r_addr_base | (r_lfsr & r_addr_mask));

    assign cpu_req_wr_data = {w_addr, w_do_write, w_write_be, w_wdata};
    assign cpu_req_wr_valid = (r_fsm == FSM_ISSUE);
    assign cpu_rsp_rd_ready = (r_fsm == FSM_WAIT_RSP);

    // ------------------------------------------------------------------
    // AXIL write handling: accept AW and W independently per AXI4-Lite spec.
    // ------------------------------------------------------------------
    logic        r_bvalid;
    logic        r_aw_done;
    logic        r_w_done;
    logic [31:0] r_awaddr;
    logic [31:0] r_wdata;
    logic [3:0]  r_wstrb;

    assign s_axil_awready = ~r_bvalid & ~r_aw_done;
    assign s_axil_wready  = ~r_bvalid & ~r_w_done;
    assign s_axil_bvalid  = r_bvalid;
    assign s_axil_bresp   = 2'b00;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_bvalid      <= 1'b0;
            r_aw_done     <= 1'b0;
            r_w_done      <= 1'b0;
            r_ctrl        <= '0;
            r_seed        <= '0;
            r_addr_base   <= '0;
            r_addr_mask   <= '0;
            r_trans_count <= '0;
        end else begin
            if (s_axil_awvalid && s_axil_awready) begin
                r_aw_done <= 1'b1;
                r_awaddr  <= s_axil_awaddr;
            end
            if (s_axil_wvalid && s_axil_wready) begin
                r_w_done <= 1'b1;
                r_wdata  <= s_axil_wdata;
                r_wstrb  <= s_axil_wstrb;
            end
            if (r_aw_done && r_w_done && ~r_bvalid) begin
                r_bvalid  <= 1'b1;
                r_aw_done <= 1'b0;
                r_w_done  <= 1'b0;
                for (int b = 0; b < 4; b++) begin
                    if (r_wstrb[b]) begin
                        case (r_awaddr[5:2])
                            CSR_CTRL:        r_ctrl[8*b +: 8]        <= r_wdata[8*b +: 8];
                            CSR_SEED:        r_seed[8*b +: 8]        <= r_wdata[8*b +: 8];
                            CSR_ADDR_BASE:   r_addr_base[8*b +: 8]   <= r_wdata[8*b +: 8];
                            CSR_ADDR_MASK:   r_addr_mask[8*b +: 8]   <= r_wdata[8*b +: 8];
                            CSR_TRANS_COUNT: r_trans_count[8*b +: 8] <= r_wdata[8*b +: 8];
                            default: ;
                        endcase
                    end
                end
            end else if (s_axil_bvalid && s_axil_bready) begin
                r_bvalid <= 1'b0;
            end

            // Clear run bit when the engine starts (leaves IDLE) and when
            // it finishes. Software can read STATUS to observe completion.
            if ((r_fsm == FSM_IDLE) && (r_ctrl[0] == 1'b1)) begin
                r_ctrl[0] <= 1'b0;
            end
        end
    )

    // ------------------------------------------------------------------
    // AXIL read handling
    // ------------------------------------------------------------------
    logic        r_ar_done;
    logic [31:0] r_ar_addr;
    logic [31:0] r_rdata;

    assign s_axil_arready = ~r_ar_done;
    assign s_axil_rvalid  = r_ar_done;
    assign s_axil_rresp   = 2'b00;
    assign s_axil_rdata   = r_rdata;

    always_comb begin
        case (r_ar_addr[5:2])
            CSR_CTRL:          r_rdata = r_ctrl;
            CSR_SEED:          r_rdata = r_seed;
            CSR_ADDR_BASE:     r_rdata = r_addr_base;
            CSR_ADDR_MASK:     r_rdata = r_addr_mask;
            CSR_TRANS_COUNT:   r_rdata = r_trans_count;
            CSR_STATUS:        r_rdata = {30'b0, r_busy, r_done};
            CSR_ACC_COUNT:     r_rdata = r_acc_count;
            CSR_RSP_COUNT:     r_rdata = r_rsp_count;
            CSR_ERR_FLAG:      r_rdata = {31'b0, r_err_flag};
            CSR_RSP_CKSUM_LO:  r_rdata = r_rsp_cksum[31:0];
            CSR_RSP_CKSUM_HI:  r_rdata = r_rsp_cksum[63:32];
            CSR_WDATA_CKSUM_LO:r_rdata = r_wdata_cksum[31:0];
            CSR_WDATA_CKSUM_HI:r_rdata = r_wdata_cksum[63:32];
            default:           r_rdata = 32'hDEAD_BEEF;
        endcase
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_ar_done <= 1'b0;
            r_ar_addr <= '0;
        end else begin
            if (s_axil_arvalid && s_axil_arready) begin
                r_ar_addr <= s_axil_araddr;
                r_ar_done <= 1'b1;
            end else if (s_axil_rvalid && s_axil_rready) begin
                r_ar_done <= 1'b0;
            end
        end
    )

    // ------------------------------------------------------------------
    // FSM + counters
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_fsm         <= FSM_IDLE;
            r_lfsr        <= '0;
            r_acc_count   <= '0;
            r_rsp_count   <= '0;
            r_done        <= 1'b0;
            r_busy        <= 1'b0;
            r_err_flag    <= 1'b0;
            r_timeout_cnt <= '0;
            r_rsp_cksum   <= '0;
            r_wdata_cksum <= '0;
        end else begin
            case (r_fsm)
                FSM_IDLE: begin
                    if (r_ctrl[0]) begin
                        r_fsm       <= FSM_ISSUE;
                        r_busy      <= 1'b1;
                        r_done      <= 1'b0;
                        r_lfsr      <= r_seed;
                        r_acc_count <= '0;
                        r_rsp_count <= '0;
                        r_err_flag  <= 1'b0;
                    end
                end

                FSM_ISSUE: begin
                    if (cpu_req_wr_ready) begin
                        r_lfsr        <= w_lfsr_next;
                        r_acc_count   <= (r_acc_count == 32'hFFFF_FFFF)
                                         ? r_acc_count : r_acc_count + 1'b1;
                        r_wdata_cksum <= r_wdata_cksum ^ w_wdata;
                        r_fsm         <= FSM_WAIT_RSP;
                        r_timeout_cnt <= '0;
                    end
                end

                FSM_WAIT_RSP: begin
                    if (cpu_rsp_rd_valid) begin
                        r_rsp_count <= (r_rsp_count == 32'hFFFF_FFFF)
                                       ? r_rsp_count : r_rsp_count + 1'b1;
                        r_rsp_cksum <= r_rsp_cksum ^ cpu_rsp_rd_data;
                        if (r_rsp_count + 1'b1 >= r_trans_count) begin
                            r_fsm  <= FSM_IDLE;
                            r_done <= 1'b1;
                            r_busy <= 1'b0;
                        end else begin
                            r_fsm <= FSM_ISSUE;
                        end
                    end else begin
                        r_timeout_cnt <= r_timeout_cnt + 1'b1;
                        if (&r_timeout_cnt) begin
                            r_err_flag <= 1'b1;
                            r_fsm      <= FSM_IDLE;
                            r_done     <= 1'b1;
                            r_busy     <= 1'b0;
                        end
                    end
                end

                default: r_fsm <= FSM_IDLE;
            endcase
        end
    )

endmodule : amber_traffic_gen

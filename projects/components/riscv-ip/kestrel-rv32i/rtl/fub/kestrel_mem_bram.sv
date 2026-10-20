// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: kestrel_mem_bram
// Purpose: Registered-read (block RAM) memory system for kestrel_core: one
//          unified true-dual-port array, a fetch/exec/load sequencer that
//          holds the core with mem_wait while the synchronous reads land,
//          and the AXIL loader + run/status registers on the second port
//
// Documentation: projects/components/riscv-ip/kestrel-rv32i/docs/kestrel_mas
// Subsystem: riscv-ip/kestrel-rv32i
//
// Author: sean galloway
// Created: 2026-10-20
//
// Notes:
//   - kestrel_mem_loader keeps the core's combinational-read contract with
//     distributed RAM; this module trades it for block RAM (owner,
//     2026-10-20): every instruction takes two clocks (fetch, execute), a
//     load three (fetch, execute, load).  The core holds all state while
//     mem_wait is high, so the ISA is unchanged -- riscv-formal proves it
//     under arbitrary wait states (formal/kestrel/riscv-formal).
//   - Port A serves the core and is time-multiplexed by the sequencer:
//     FETCH reads at the PC; EXEC presents the L/S address (a store writes
//     at the end of EXEC, a load's read lands in LOAD).  The instruction word
//     is captured at the end of EXEC so it stays valid through LOAD.
//   - Port B serves the AXIL loader.  Memory writes are accepted only in
//     load mode (CTRL.run = 0, core held in reset); reads work at any time.
//   - The address map is kestrel_mem_loader's, so its host code carries
//     over: s_axil addr[17] = 1 selects the registers below, else memory
//     (one unified 128 KB space, byte address addr[16:0]).
//
//     addr[17]=1, addr[4:2]:
//       0  CTRL/STATUS  W: bit0 run (1 = release the core; 0 = back to load
//                       mode, core reset).  R: {cause[7:4], halted[1], run[0]}
//       1  CYCLES       clocks since run was set, frozen at halt
//       2  INSTRET      retired instructions (RVFI beats)
//       3  GP           the last value written to x3 (gp): the riscv-tests
//                       verdict, since the core halts on the final ecall
//       4  BUILD_ID     ASCII "KBRM"

`timescale 1ns / 1ps

`include "reset_defs.svh"

module kestrel_mem_bram #(
    parameter int AXIL_ADDR_WIDTH = 18,
    parameter int AXIL_DATA_WIDTH = 32,
    parameter int MEM_WORDS       = 32768,   // 128 KB unified
    parameter int SKID_DEPTH_AW   = 2,
    parameter int SKID_DEPTH_W    = 2,
    parameter int SKID_DEPTH_B    = 2,
    parameter int SKID_DEPTH_AR   = 2,
    parameter int SKID_DEPTH_R    = 4
) (
    input  logic                         aclk,
    input  logic                         aresetn,

    // AXIL slave (loader + registers)
    input  logic [AXIL_ADDR_WIDTH-1:0]   s_axil_awaddr,
    input  logic [2:0]                   s_axil_awprot,
    input  logic                         s_axil_awvalid,
    output logic                         s_axil_awready,
    input  logic [AXIL_DATA_WIDTH-1:0]   s_axil_wdata,
    input  logic [AXIL_DATA_WIDTH/8-1:0] s_axil_wstrb,
    input  logic                         s_axil_wvalid,
    output logic                         s_axil_wready,
    output logic [1:0]                   s_axil_bresp,
    output logic                         s_axil_bvalid,
    input  logic                         s_axil_bready,
    input  logic [AXIL_ADDR_WIDTH-1:0]   s_axil_araddr,
    input  logic [2:0]                   s_axil_arprot,
    input  logic                         s_axil_arvalid,
    output logic                         s_axil_arready,
    output logic [AXIL_DATA_WIDTH-1:0]   s_axil_rdata,
    output logic [1:0]                   s_axil_rresp,
    output logic                         s_axil_rvalid,
    input  logic                         s_axil_rready,

    // Core side (kestrel_core's memory interface + mem_wait)
    input  logic [31:0]                  imem_addr,
    output logic [31:0]                  imem_rdata,
    input  logic                         dmem_req,
    input  logic [31:0]                  dmem_addr,
    output logic [31:0]                  dmem_rdata,
    input  logic [3:0]                   dmem_wstrb,
    input  logic [31:0]                  dmem_wdata,
    output logic                         mem_wait,
    output logic                         core_rst_n,

    // Core status, for the registers
    input  logic                         halt,
    input  logic [3:0]                   halt_cause,
    input  logic                         rvfi_valid,
    input  logic [4:0]                   rvfi_rd_addr,
    input  logic [31:0]                  rvfi_rd_wdata,

    output logic                         o_run,
    output logic                         o_halted
);

    localparam int STRB_W   = AXIL_DATA_WIDTH / 8;
    localparam int IDX_W    = $clog2(MEM_WORDS);
    localparam int REG_BIT  = 17;
    localparam logic [31:0] BUILD_ID = 32'h4B42_524D;   // "KBRM"
    localparam logic [1:0]  RESP_OKAY = 2'b00;
    localparam logic [4:0]  REG_GP = 5'd3;

    // =========================================================================
    // The array: true dual port, byte writes, registered read on both ports
    // =========================================================================
`ifdef XILINX
    (* ram_style = "block" *)
`elsif SYNTH_PRAGMA
    /* synthesis ramstyle = "M10K" */
`endif
    logic [31:0] r_mem [MEM_WORDS];

    logic             a_en, b_en;
    logic [IDX_W-1:0] a_idx, b_idx;
    logic [3:0]       a_we, b_we;
    logic [31:0]      a_din, b_din, a_dout, b_dout;

    always_ff @(posedge aclk) begin
        if (a_en) begin
            for (int b = 0; b < 4; b++)
                if (a_we[b]) r_mem[a_idx][b*8 +: 8] <= a_din[b*8 +: 8];
            a_dout <= r_mem[a_idx];
        end
    end

    always_ff @(posedge aclk) begin
        if (b_en) begin
            for (int b = 0; b < 4; b++)
                if (b_we[b]) r_mem[b_idx][b*8 +: 8] <= b_din[b*8 +: 8];
            b_dout <= r_mem[b_idx];
        end
    end

    // =========================================================================
    // Run/status state
    // =========================================================================
    logic        run_q, halted_q;
    logic [3:0]  cause_q;
    logic [31:0] cycles_q, instret_q, gp_q;

    assign core_rst_n = run_q;
    assign o_run      = run_q;
    assign o_halted   = halted_q;

    // =========================================================================
    // Port A: the core sequencer (FETCH -> EXEC [-> LOAD] -> FETCH)
    // =========================================================================
    typedef enum logic [1:0] {S_FETCH, S_EXEC, S_LOAD} seq_e;
    seq_e        state_q;
    logic [31:0] insn_q;
    logic        is_load, is_store;

    assign is_load  = dmem_req && (dmem_wstrb == 4'b0000);
    assign is_store = dmem_req && (dmem_wstrb != 4'b0000);

    always_comb begin
        a_en  = run_q;
        a_we  = 4'b0000;
        a_din = dmem_wdata;
        a_idx = imem_addr[IDX_W+1:2];
        case (state_q)
            S_EXEC: begin
                a_idx = dmem_addr[IDX_W+1:2];
                a_en  = run_q && dmem_req;
                if (is_store) a_we = dmem_wstrb;
            end
            S_LOAD:  a_en = 1'b0;           // hold the load data
            default: ;                      // S_FETCH: read at the PC
        endcase
    end

    assign imem_rdata = (state_q == S_EXEC) ? a_dout : insn_q;
    assign dmem_rdata = a_dout;
    assign mem_wait   = (state_q == S_FETCH) || (state_q == S_EXEC && is_load);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            state_q <= S_FETCH;
            insn_q  <= '0;
        end else if (!run_q) begin
            state_q <= S_FETCH;
        end else begin
            case (state_q)
                S_FETCH: state_q <= S_EXEC;
                S_EXEC: begin
                    insn_q  <= a_dout;
                    state_q <= is_load ? S_LOAD : S_FETCH;
                end
                default: state_q <= S_FETCH;
            endcase
        end
    )

    // =========================================================================
    // AXIL leaf slaves
    // =========================================================================
    logic [AXIL_ADDR_WIDTH-1:0] fub_awaddr, fub_araddr;
    logic [2:0]                 fub_awprot, fub_arprot;
    logic                       fub_awvalid, fub_awready, fub_wvalid, fub_wready;
    logic [AXIL_DATA_WIDTH-1:0] fub_wdata, fub_rdata;
    logic [STRB_W-1:0]          fub_wstrb;
    logic [1:0]                 fub_bresp, fub_rresp;
    logic                       fub_bvalid, fub_bready, fub_arvalid, fub_arready;
    logic                       fub_rvalid, fub_rready;

    axil4_slave_wr #(
        .AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH), .AXIL_DATA_WIDTH(AXIL_DATA_WIDTH),
        .SKID_DEPTH_AW(SKID_DEPTH_AW), .SKID_DEPTH_W(SKID_DEPTH_W), .SKID_DEPTH_B(SKID_DEPTH_B)
    ) u_axil_wr (
        .aclk(aclk), .aresetn(aresetn),
        .s_axil_awaddr(s_axil_awaddr), .s_axil_awprot(s_axil_awprot),
        .s_axil_awvalid(s_axil_awvalid), .s_axil_awready(s_axil_awready),
        .s_axil_wdata(s_axil_wdata), .s_axil_wstrb(s_axil_wstrb),
        .s_axil_wvalid(s_axil_wvalid), .s_axil_wready(s_axil_wready),
        .s_axil_bresp(s_axil_bresp), .s_axil_bvalid(s_axil_bvalid), .s_axil_bready(s_axil_bready),
        .fub_awaddr(fub_awaddr), .fub_awprot(fub_awprot),
        .fub_awvalid(fub_awvalid), .fub_awready(fub_awready),
        .fub_wdata(fub_wdata), .fub_wstrb(fub_wstrb),
        .fub_wvalid(fub_wvalid), .fub_wready(fub_wready),
        .fub_bresp(fub_bresp), .fub_bvalid(fub_bvalid), .fub_bready(fub_bready),
        .busy());

    axil4_slave_rd #(
        .AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH), .AXIL_DATA_WIDTH(AXIL_DATA_WIDTH),
        .SKID_DEPTH_AR(SKID_DEPTH_AR), .SKID_DEPTH_R(SKID_DEPTH_R)
    ) u_axil_rd (
        .aclk(aclk), .aresetn(aresetn),
        .s_axil_araddr(s_axil_araddr), .s_axil_arprot(s_axil_arprot),
        .s_axil_arvalid(s_axil_arvalid), .s_axil_arready(s_axil_arready),
        .s_axil_rdata(s_axil_rdata), .s_axil_rresp(s_axil_rresp),
        .s_axil_rvalid(s_axil_rvalid), .s_axil_rready(s_axil_rready),
        .fub_araddr(fub_araddr), .fub_arprot(fub_arprot),
        .fub_arvalid(fub_arvalid), .fub_arready(fub_arready),
        .fub_rdata(fub_rdata), .fub_rresp(fub_rresp),
        .fub_rvalid(fub_rvalid), .fub_rready(fub_rready),
        .busy());

    // ---- write side: AW holding register + B holding bit (loader pattern) ----
    logic [AXIL_ADDR_WIDTH-1:0] wr_addr_q;
    logic                       wr_pend_q, b_pend_q;
    logic                       aw_fire, w_fire, b_fire;

    assign aw_fire     = fub_awvalid && fub_awready;
    assign w_fire      = fub_wvalid  && fub_wready;
    assign b_fire      = fub_bvalid  && fub_bready;
    assign fub_awready = !wr_pend_q || w_fire;
    assign fub_wready  = wr_pend_q && !b_pend_q;
    assign fub_bvalid  = b_pend_q;
    assign fub_bresp   = RESP_OKAY;

    logic ld_wr, reg_wr;
    assign ld_wr  = w_fire && !wr_addr_q[REG_BIT] && !run_q;
    assign reg_wr = w_fire &&  wr_addr_q[REG_BIT] && (wr_addr_q[4:2] == 3'd0) && fub_wstrb[0];

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            wr_addr_q <= '0;
            wr_pend_q <= 1'b0;
            b_pend_q  <= 1'b0;
        end else begin
            if (aw_fire) wr_addr_q <= fub_awaddr;
            case ({aw_fire, w_fire})
                2'b10:   wr_pend_q <= 1'b1;
                2'b01:   wr_pend_q <= 1'b0;
                default: ;
            endcase
            if (w_fire)      b_pend_q <= 1'b1;
            else if (b_fire) b_pend_q <= 1'b0;
        end
    )

    // ---- read side: two stages (address -> block RAM -> holding register) ----
    // Memory writes own port B in the cycle they fire, so AR is only accepted
    // when no write fires.
    logic                       rd_wait_q, rd_full_q, rd_reg_q;
    logic [2:0]                 rd_sel_q;
    logic [AXIL_DATA_WIDTH-1:0] rd_data_q, reg_rdata;
    logic                       ar_fire;

    assign fub_arready = !rd_wait_q && !rd_full_q && !ld_wr;
    assign ar_fire     = fub_arvalid && fub_arready;
    assign fub_rvalid  = rd_full_q;
    assign fub_rdata   = rd_data_q;
    assign fub_rresp   = RESP_OKAY;

    always_comb begin
        case (rd_sel_q)
            3'd0:    reg_rdata = {24'd0, cause_q, 2'b00, halted_q, run_q};
            3'd1:    reg_rdata = cycles_q;
            3'd2:    reg_rdata = instret_q;
            3'd3:    reg_rdata = gp_q;
            3'd4:    reg_rdata = BUILD_ID;
            default: reg_rdata = '0;
        endcase
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            rd_wait_q <= 1'b0;
            rd_full_q <= 1'b0;
            rd_reg_q  <= 1'b0;
            rd_sel_q  <= '0;
            rd_data_q <= '0;
        end else begin
            if (ar_fire) begin
                rd_wait_q <= 1'b1;
                rd_reg_q  <= fub_araddr[REG_BIT];
                rd_sel_q  <= fub_araddr[4:2];
            end else if (rd_wait_q) begin
                rd_wait_q <= 1'b0;
                rd_full_q <= 1'b1;
                rd_data_q <= rd_reg_q ? reg_rdata : b_dout;
            end else if (rd_full_q && fub_rready) begin
                rd_full_q <= 1'b0;
            end
        end
    )

    always_comb begin
        b_en  = ld_wr || ar_fire;
        b_we  = ld_wr ? fub_wstrb : 4'b0000;
        b_din = fub_wdata;
        b_idx = ld_wr ? wr_addr_q[IDX_W+1:2] : fub_araddr[IDX_W+1:2];
    end

    // =========================================================================
    // Run control and status
    // =========================================================================
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            run_q     <= 1'b0;
            halted_q  <= 1'b0;
            cause_q   <= '0;
            cycles_q  <= '0;
            instret_q <= '0;
            gp_q      <= '0;
        end else begin
            if (reg_wr) begin
                run_q <= fub_wdata[0];
                if (fub_wdata[0] && !run_q) begin
                    halted_q  <= 1'b0;
                    cause_q   <= '0;
                    cycles_q  <= '0;
                    instret_q <= '0;
                    gp_q      <= '0;
                end
            end else if (run_q && !halted_q) begin
                cycles_q <= cycles_q + 1'b1;
                if (rvfi_valid) begin
                    instret_q <= instret_q + 1'b1;
                    if (rvfi_rd_addr == REG_GP) gp_q <= rvfi_rd_wdata;
                end
                if (halt && !mem_wait) begin
                    halted_q <= 1'b1;
                    cause_q  <= halt_cause;
                end
            end
        end
    )

endmodule : kestrel_mem_bram

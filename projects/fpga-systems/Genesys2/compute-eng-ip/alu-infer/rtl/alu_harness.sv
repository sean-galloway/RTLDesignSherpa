// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_harness
// Purpose: Board harness for a valid/ready ALU: host-loaded command RAM,
//          full-rate issue into the ALU slot, result RAM with per-entry
//          issue/retire timestamps, CSRs over AXI4-Lite
//
// Documentation: projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/README.md
// Subsystem: fpga-systems / compute-eng-ip
//
// Author: sean galloway
// Created: 2026-10-20
//
// Notes:
//   - The device under test is `alu_slot`, a module each build provides
//     (build-infer: alu_infer_top).  The harness knows only the issue seam:
//     {op_line_a, op_line_b, threshold_imm, func_sel, acc_ctrl} + valid/ready
//     in, {result_line, result_flags} + result_valid/ready out, err_opcode.
//   - The UART cannot keep an ALU busy, so the host LOADS commands, then
//     START issues them back to back at the harness clock; results land in
//     RAM with the cycle of their issue and retire edges, which is how the
//     board measures latency and II.
//   - CSR actions are taken on their rising edge, and a command commits the
//     cycle after CMD_CTL's swmod: apb4_to_peakrdl presents every access
//     twice (converters BUG-010), which these make harmless.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module alu_harness
    import alu_harness_regs_pkg::*;
#(
    parameter int    DEPTH   = 256,
    parameter int    CLK_MHZ = 100,
    parameter string PROFILE = "FULL"
) (
    input  logic        aclk,
    input  logic        aresetn,

    // Host AXI4-Lite (from uart_axil_bridge)
    input  logic [31:0] s_axil_awaddr,
    input  logic [2:0]  s_axil_awprot,
    input  logic        s_axil_awvalid,
    output logic        s_axil_awready,
    input  logic [31:0] s_axil_wdata,
    input  logic [3:0]  s_axil_wstrb,
    input  logic        s_axil_wvalid,
    output logic        s_axil_wready,
    output logic [1:0]  s_axil_bresp,
    output logic        s_axil_bvalid,
    input  logic        s_axil_bready,
    input  logic [31:0] s_axil_araddr,
    input  logic [2:0]  s_axil_arprot,
    input  logic        s_axil_arvalid,
    output logic        s_axil_arready,
    output logic [31:0] s_axil_rdata,
    output logic [1:0]  s_axil_rresp,
    output logic        s_axil_rvalid,
    input  logic        s_axil_rready,

    output logic        o_busy,
    output logic        o_done,
    output logic        o_err_seen
);

    localparam int IW = $clog2(DEPTH);

    // =========================================================================
    // Host bus: AXI4-Lite -> APB4 (axi4_to_apb4_shim, AXI4-only fields tied
    // off) -> apb4_to_peakrdl -> the regblock
    // =========================================================================
    logic        apb_PSEL, apb_PENABLE, apb_PWRITE, apb_PREADY, apb_PSLVERR;
    logic [31:0] apb_PADDR, apb_PWDATA, apb_PRDATA;
    logic [3:0]  apb_PSTRB;
    logic [2:0]  apb_PPROT;

    axi4_to_apb4_shim #(
        .AXI_ID_WIDTH(1), .AXI_ADDR_WIDTH(32), .AXI_DATA_WIDTH(32), .AXI_USER_WIDTH(1),
        .APB_ADDR_WIDTH(32), .APB_DATA_WIDTH(32)
    ) u_axi2apb (
        .aclk(aclk), .aresetn(aresetn), .pclk(aclk), .presetn(aresetn),
        .s_axi_awid('0), .s_axi_awaddr(s_axil_awaddr), .s_axi_awlen(8'd0), .s_axi_awsize(3'd2),
        .s_axi_awburst(2'b01), .s_axi_awlock(1'b0), .s_axi_awcache(4'd0), .s_axi_awprot(s_axil_awprot),
        .s_axi_awqos(4'd0), .s_axi_awregion(4'd0), .s_axi_awuser('0),
        .s_axi_awvalid(s_axil_awvalid), .s_axi_awready(s_axil_awready),
        .s_axi_wdata(s_axil_wdata), .s_axi_wstrb(s_axil_wstrb), .s_axi_wlast(1'b1), .s_axi_wuser('0),
        .s_axi_wvalid(s_axil_wvalid), .s_axi_wready(s_axil_wready),
        .s_axi_bid(), .s_axi_bresp(s_axil_bresp), .s_axi_buser(),
        .s_axi_bvalid(s_axil_bvalid), .s_axi_bready(s_axil_bready),
        .s_axi_arid('0), .s_axi_araddr(s_axil_araddr), .s_axi_arlen(8'd0), .s_axi_arsize(3'd2),
        .s_axi_arburst(2'b01), .s_axi_arlock(1'b0), .s_axi_arcache(4'd0), .s_axi_arprot(s_axil_arprot),
        .s_axi_arqos(4'd0), .s_axi_arregion(4'd0), .s_axi_aruser('0),
        .s_axi_arvalid(s_axil_arvalid), .s_axi_arready(s_axil_arready),
        .s_axi_rid(), .s_axi_rdata(s_axil_rdata), .s_axi_rresp(s_axil_rresp), .s_axi_rlast(),
        .s_axi_ruser(), .s_axi_rvalid(s_axil_rvalid), .s_axi_rready(s_axil_rready),
        .m_apb_PSEL(apb_PSEL), .m_apb_PADDR(apb_PADDR), .m_apb_PENABLE(apb_PENABLE),
        .m_apb_PWRITE(apb_PWRITE), .m_apb_PWDATA(apb_PWDATA), .m_apb_PSTRB(apb_PSTRB),
        .m_apb_PPROT(apb_PPROT), .m_apb_PRDATA(apb_PRDATA), .m_apb_PREADY(apb_PREADY),
        .m_apb_PSLVERR(apb_PSLVERR));

    logic        w_cpuif_req, w_cpuif_req_is_wr, w_cpuif_stall_wr, w_cpuif_stall_rd;
    logic [11:0] w_cpuif_addr;
    logic [31:0] w_cpuif_wr_data, w_cpuif_wr_biten, w_cpuif_rd_data;
    logic        w_cpuif_rd_ack, w_cpuif_rd_err, w_cpuif_wr_ack, w_cpuif_wr_err;

    alu_harness_regs__in_t  hwif_in;
    alu_harness_regs__out_t hwif_out;

    apb4_to_peakrdl #(
        .ADDR_WIDTH(12), .DATA_WIDTH(32), .USE_2_PHASE_CDC(1'b1)
    ) u_apb2cpuif (
        .aclk(aclk), .aresetn(aresetn), .pclk(aclk), .presetn(aresetn),
        .s_apb_PSEL(apb_PSEL), .s_apb_PENABLE(apb_PENABLE), .s_apb_PREADY(apb_PREADY),
        .s_apb_PADDR(apb_PADDR[11:0]), .s_apb_PWRITE(apb_PWRITE), .s_apb_PWDATA(apb_PWDATA),
        .s_apb_PSTRB(apb_PSTRB), .s_apb_PPROT(apb_PPROT), .s_apb_PRDATA(apb_PRDATA),
        .s_apb_PSLVERR(apb_PSLVERR),
        .cpuif_req(w_cpuif_req), .cpuif_req_is_wr(w_cpuif_req_is_wr), .cpuif_addr(w_cpuif_addr),
        .cpuif_wr_data(w_cpuif_wr_data), .cpuif_wr_biten(w_cpuif_wr_biten),
        .cpuif_req_stall_wr(w_cpuif_stall_wr), .cpuif_req_stall_rd(w_cpuif_stall_rd),
        .cpuif_rd_ack(w_cpuif_rd_ack), .cpuif_rd_err(w_cpuif_rd_err), .cpuif_rd_data(w_cpuif_rd_data),
        .cpuif_wr_ack(w_cpuif_wr_ack), .cpuif_wr_err(w_cpuif_wr_err));

    alu_harness_regs u_regs (
        .clk(aclk), .rst(!aresetn),
        .s_cpuif_req(w_cpuif_req), .s_cpuif_req_is_wr(w_cpuif_req_is_wr),
        .s_cpuif_addr(w_cpuif_addr[ALU_HARNESS_REGS_MIN_ADDR_WIDTH-1:0]),
        .s_cpuif_wr_data(w_cpuif_wr_data), .s_cpuif_wr_biten(w_cpuif_wr_biten),
        .s_cpuif_req_stall_wr(w_cpuif_stall_wr), .s_cpuif_req_stall_rd(w_cpuif_stall_rd),
        .s_cpuif_rd_ack(w_cpuif_rd_ack), .s_cpuif_rd_err(w_cpuif_rd_err), .s_cpuif_rd_data(w_cpuif_rd_data),
        .s_cpuif_wr_ack(w_cpuif_wr_ack), .s_cpuif_wr_err(w_cpuif_wr_err),
        .hwif_in(hwif_in), .hwif_out(hwif_out));

    // =========================================================================
    // Control decode: rising edges of the singlepulse actions
    // =========================================================================
    logic r_start_d, r_clear_d, r_commit_pend;
    logic w_start, w_clear;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_start_d     <= 1'b0;
            r_clear_d     <= 1'b0;
            r_commit_pend <= 1'b0;
        end else begin
            r_start_d     <= hwif_out.CTRL.start.value;
            r_clear_d     <= hwif_out.CTRL.clear.value;
            r_commit_pend <= hwif_out.CMD_CTL.imm.swmod;
        end
    )

    assign w_start = hwif_out.CTRL.start.value && !r_start_d;
    assign w_clear = hwif_out.CTRL.clear.value && !r_clear_d;

    // =========================================================================
    // Command and result memories (distributed RAM, async read, no reset)
    // =========================================================================
    localparam int CMD_W = 32 + 32 + 16 + 9 + 2;
    localparam int RES_W = 32 + 32 + 16 + 16 + 1;

`ifdef XILINX
    (* ram_style = "distributed" *)
`elsif SYNTH_PRAGMA
    /* synthesis ramstyle = "MLAB" */
`endif
    logic [CMD_W-1:0] r_cmd [DEPTH];
`ifdef XILINX
    (* ram_style = "distributed" *)
`elsif SYNTH_PRAGMA
    /* synthesis ramstyle = "MLAB" */
`endif
    logic [RES_W-1:0] r_res [DEPTH];

    logic [IW-1:0] w_host_idx;
    assign w_host_idx = hwif_out.CMD_INDEX.index.value[IW-1:0];

    always_ff @(posedge aclk) begin
        if (r_commit_pend)
            r_cmd[w_host_idx] <= {hwif_out.CMD_A.value.value, hwif_out.CMD_B.value.value,
                                  hwif_out.CMD_CTL.imm.value, hwif_out.CMD_CTL.func_sel.value,
                                  hwif_out.CMD_CTL.acc_ctrl.value};
    end

    // =========================================================================
    // The run engine: issue from the command RAM, retire into the result RAM
    // =========================================================================
    logic [15:0]   r_issue_cnt, r_retire_cnt, r_count;
    logic [IW-1:0] r_issue_ptr, r_retire_ptr;
    logic          r_busy, r_done;
    logic [31:0]   r_cycle, r_stall, r_errs;
    logic [15:0]   r_issue_ts [DEPTH];
    logic [DEPTH-1:0] r_err_at;
    logic [15:0]   r_lfsr;
    logic          r_fill_seen;

    logic          w_valid, w_ready, w_issue;
    logic          w_res_valid, w_res_ready, w_retire;
    logic [31:0]   w_res_line, w_res_flags;
    logic          w_err;
    logic [31:0]   w_slot_info;
    logic [CMD_W-1:0] w_cmd;

    assign w_cmd   = r_cmd[r_issue_ptr];
    assign w_valid = r_busy && (r_issue_cnt < r_count);
    assign w_issue = w_valid && w_ready;
    assign w_retire = w_res_valid && w_res_ready;

    always_comb begin
        case (hwif_out.CTRL.stall_mode.value)
            2'd1:    w_res_ready = r_lfsr[0];
            // Fill: hold the consumer off until the ALU's FIFO is full (issue
            // backpressured), then drain -- one fill-and-release per run.
            2'd2:    w_res_ready = r_fill_seen;
            default: w_res_ready = 1'b1;
        endcase
    end

    alu_slot #(.PROFILE(PROFILE)) u_slot (
        .clk           (aclk),
        .aresetn       (aresetn),
        .op_line_a     (w_cmd[CMD_W-1 -: 32]),
        .op_line_b     (w_cmd[CMD_W-33 -: 32]),
        .threshold_imm (w_cmd[11 +: 16]),     // {A[90:59], B[58:27], imm[26:11], func_sel[10:2], acc_ctrl[1:0]}
        .func_sel      (w_cmd[2 +: 9]),
        .acc_ctrl      (w_cmd[1:0]),
        .valid         (w_valid),
        .ready         (w_ready),
        .result_valid  (w_res_valid),
        .result_ready  (w_res_ready),
        .result_line   (w_res_line),
        .result_flags  (w_res_flags),
        .err_opcode    (w_err),
        .slot_info     (w_slot_info)
    );

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_busy       <= 1'b0;
            r_done       <= 1'b0;
            r_issue_cnt  <= '0;
            r_retire_cnt <= '0;
            r_issue_ptr  <= '0;
            r_retire_ptr <= '0;
            r_count      <= '0;
            r_cycle      <= '0;
            r_stall      <= '0;
            r_errs       <= '0;
            r_err_at     <= '0;
            r_lfsr       <= 16'hACE1;
            r_fill_seen  <= 1'b0;
        end else begin
            r_lfsr <= {r_lfsr[14:0], r_lfsr[15] ^ r_lfsr[13] ^ r_lfsr[12] ^ r_lfsr[10]};
            if (w_clear) begin
                r_busy       <= 1'b0;
                r_done       <= 1'b0;
                r_issue_cnt  <= '0;
                r_retire_cnt <= '0;
                r_cycle      <= '0;
                r_stall      <= '0;
                r_errs       <= '0;
            end else if (w_start && !r_busy) begin
                r_busy       <= 1'b1;
                r_done       <= 1'b0;
                r_issue_cnt  <= '0;
                r_retire_cnt <= '0;
                r_issue_ptr  <= '0;
                r_retire_ptr <= '0;
                r_count      <= (hwif_out.RUN_COUNT.n.value == 16'd0) ? 16'd1 :
                                (hwif_out.RUN_COUNT.n.value > 16'(DEPTH)) ? 16'(DEPTH) :
                                hwif_out.RUN_COUNT.n.value;
                r_cycle      <= '0;
                r_stall      <= '0;
                r_errs       <= '0;
                r_err_at     <= '0;
                r_fill_seen  <= 1'b0;
            end else if (r_busy) begin
                r_cycle <= r_cycle + 1'b1;
                if (w_valid && !w_ready) begin
                    r_stall     <= r_stall + 1'b1;
                    r_fill_seen <= 1'b1;
                end
                if (r_issue_cnt == r_count) r_fill_seen <= 1'b1;   // fewer commands than the FIFO holds
                if (w_issue) begin
                    r_issue_cnt <= r_issue_cnt + 1'b1;
                    r_issue_ptr <= r_issue_ptr + 1'b1;
                    if (w_err) begin
                        r_errs <= r_errs + 1'b1;
                        r_err_at[r_issue_ptr] <= 1'b1;
                    end
                end
                if (w_retire) begin
                    r_retire_cnt <= r_retire_cnt + 1'b1;
                    r_retire_ptr <= r_retire_ptr + 1'b1;
                    if (r_retire_cnt + 1'b1 == r_count) begin
                        r_busy <= 1'b0;
                        r_done <= 1'b1;
                    end
                end
            end
        end
    )

    always_ff @(posedge aclk) begin
        if (r_busy && w_issue)
            r_issue_ts[r_issue_ptr] <= r_cycle[15:0];
        if (r_busy && w_retire)
            r_res[r_retire_ptr] <= {w_res_line, w_res_flags, r_issue_ts[r_retire_ptr],
                                    r_cycle[15:0], r_err_at[r_retire_ptr]};
        // (A result is offered no earlier than the cycle after its issue, so
        // its r_err_at / r_issue_ts entries are always written first.)
    end

    // =========================================================================
    // Status to the CSRs
    // =========================================================================
    logic [RES_W-1:0] w_res_rd;
    assign w_res_rd = r_res[w_host_idx];

    always_comb begin
        hwif_in = '{default: '0};
        hwif_in.BUILD_ID.value.next      = 32'h414C_5548;
        hwif_in.SLOT_INFO.kind.next      = w_slot_info[3:0];
        hwif_in.SLOT_INFO.en.next        = w_slot_info[10:4];
        hwif_in.SLOT_INFO.add_lat.next   = w_slot_info[14:12];
        hwif_in.SLOT_INFO.mul_lat.next   = w_slot_info[18:16];
        hwif_in.SLOT_INFO.mac_lat.next   = w_slot_info[22:20];
        hwif_in.SLOT_INFO.pipe_depth.next = w_slot_info[28:24];
        hwif_in.GEOMETRY.depth.next      = 16'(DEPTH);
        hwif_in.GEOMETRY.clk_mhz.next    = 16'(CLK_MHZ);
        hwif_in.RES_LINE.value.next      = w_res_rd[RES_W-1 -: 32];
        hwif_in.RES_FLAGS.value.next     = w_res_rd[RES_W-33 -: 32];
        hwif_in.RES_TIME.issue.next      = w_res_rd[32:17];
        hwif_in.RES_TIME.retire.next     = w_res_rd[16:1];
        hwif_in.RES_STATUS.err.next      = w_res_rd[0];
        hwif_in.STATUS.busy.next         = r_busy;
        hwif_in.STATUS.done.next         = r_done;
        hwif_in.STATUS.issued.next       = r_issue_cnt;
        hwif_in.RETIRED.value.next       = 32'(r_retire_cnt);
        hwif_in.CYCLES.value.next        = r_cycle;
        hwif_in.STALL_CYCLES.value.next  = r_stall;
        hwif_in.ERR_COUNT.value.next     = r_errs;
    end

    assign o_busy     = r_busy;
    assign o_done     = r_done;
    assign o_err_seen = (r_errs != '0);

endmodule : alu_harness

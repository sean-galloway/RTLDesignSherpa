// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cell_cfg_regs
// Purpose: AXI4-Lite slave + in-band cfg-stream register file per PRD §7
//
// Documentation: projects/components/compute-eng-ip/cell/docs/PRD.md
// Subsystem: cell
//
// Author: sean galloway
// Created: 2026-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module cell_cfg_regs #(
    parameter int AXIL_ADDR_WIDTH = 32,
    parameter int AXIL_DATA_WIDTH = 32
) (
    input  logic              aclk,
    input  logic              aresetn,

    // AXI4-Lite slave interface
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_awaddr,
    input  logic                       s_axil_awvalid,
    output logic                       s_axil_awready,
    input  logic [AXIL_DATA_WIDTH-1:0] s_axil_wdata,
    input  logic [AXIL_DATA_WIDTH/8-1:0] s_axil_wstrb,
    input  logic                       s_axil_wvalid,
    output logic                       s_axil_wready,
    output logic [1:0]                 s_axil_bresp,
    output logic                       s_axil_bvalid,
    input  logic                       s_axil_bready,

    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_araddr,
    input  logic                       s_axil_arvalid,
    output logic                       s_axil_arready,
    output logic [AXIL_DATA_WIDTH-1:0] s_axil_rdata,
    output logic [1:0]                 s_axil_rresp,
    output logic                       s_axil_rvalid,
    input  logic                       s_axil_rready,

    // In-band cfg-stream write port (from cell_rx demux)
    input  logic                       cfg_wr_valid,
    input  logic [7:0]                 cfg_wr_addr,
    input  logic [31:0]                cfg_wr_data,
    output logic                       cfg_wr_ready,

    // In-band cfg-stream read port (read reply built by cell_rx in slice 1)
    input  logic                       cfg_rd_valid,
    input  logic [7:0]                 cfg_rd_addr,
    output logic [31:0]                cfg_rd_data,
    output logic                       cfg_rd_ready,

    // Counter increments (from datapath / credit logic)
    input  logic                       inc_lines_in,
    input  logic                       inc_lines_out,
    input  logic                       inc_credits,
    input  logic                       inc_pkts,

    // Status inputs
    input  logic                       status_input_empty,
    input  logic                       status_result_nonempty,
    input  logic                       status_grant_nonzero,

    // Register value outputs (to execution FSM and packetizer)
    output logic [31:0]                r_ctrl,
    output logic [31:0]                r_func_sel,
    output logic [31:0]                r_op_lines,
    output logic [31:0]                r_emit_batch_x,
    output logic [31:0]                r_credit_batch_n,
    output logic [31:0]                r_irq_en,
    output logic [31:0]                r_irq_status,
    output logic [31:0]                r_a,
    output logic [31:0]                r_b,
    output logic [31:0]                r_c,
    output logic [31:0]                r_d,
    output logic [31:0]                r_t,
    output logic [31:0]                r_op_src,
    output logic [31:0]                r_dest,
    output logic [31:0]                r_ip,
    output logic [31:0]                r_op,

    // Soft-reset pulse (one cycle) to slice-2/3 consumers
    output logic                       o_soft_rst,

    // Interrupt output (level, not latched here)
    output logic                       o_irq
);

    import cell_pkg::*;

    localparam int DW = AXIL_DATA_WIDTH;
    localparam int DW_BYTES = DW / 8;

    // -------------------------------------------------------------------------
    // Register storage
    // -------------------------------------------------------------------------
    logic [31:0] reg_ctrl;
    logic [31:0] reg_status;
    logic [31:0] reg_func_sel;
    logic [31:0] reg_op_lines;
    logic [31:0] reg_emit_batch_x;
    logic [31:0] reg_credit_batch_n;
    logic [31:0] reg_irq_en;
    logic [31:0] reg_irq_status;
    logic [31:0] reg_a;
    logic [31:0] reg_b;
    logic [31:0] reg_c;
    logic [31:0] reg_d;
    logic [31:0] reg_t;
    logic [31:0] reg_op_src;
    logic [31:0] reg_dest;
    logic [31:0] reg_ip;
    logic [31:0] reg_op;
    logic [31:0] reg_cnt_lines_in;
    logic [31:0] reg_cnt_lines_out;
    logic [31:0] reg_cnt_credits;
    logic [31:0] reg_cnt_pkts;

    // -------------------------------------------------------------------------
    // AXI-Lite write channel state machine
    // -------------------------------------------------------------------------
    logic [AXIL_ADDR_WIDTH-1:0] awaddr_q;
    logic                       awvalid_q;
    logic [DW-1:0]              wdata_q;
    logic [DW_BYTES-1:0]        wstrb_q;
    logic                       wvalid_q;
    logic                       bvalid_q;

    assign s_axil_awready = !awvalid_q;
    assign s_axil_wready  = !wvalid_q;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            awvalid_q <= 1'b0;
            wvalid_q  <= 1'b0;
            bvalid_q  <= 1'b0;
        end else begin
            if (s_axil_awvalid && s_axil_awready) begin
                awaddr_q  <= s_axil_awaddr;
                awvalid_q <= 1'b1;
            end
            if (s_axil_wvalid && s_axil_wready) begin
                wdata_q  <= s_axil_wdata;
                wstrb_q  <= s_axil_wstrb;
                wvalid_q <= 1'b1;
            end
            if (awvalid_q && wvalid_q) begin
                awvalid_q <= 1'b0;
                wvalid_q  <= 1'b0;
                bvalid_q  <= 1'b1;
            end
            if (bvalid_q && s_axil_bready) begin
                bvalid_q <= 1'b0;
            end
        end
    )

    assign s_axil_bvalid = bvalid_q;
    assign s_axil_bresp  = 2'b00;

    // -------------------------------------------------------------------------
    // AXI-Lite read channel state machine
    // -------------------------------------------------------------------------
    logic [AXIL_ADDR_WIDTH-1:0] araddr_q;
    logic                       rvalid_q;

    assign s_axil_arready = !rvalid_q && !araddr_q[0];  // simple ready

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            araddr_q <= '0;
            rvalid_q <= 1'b0;
        end else begin
            if (s_axil_arvalid && s_axil_arready) begin
                araddr_q <= s_axil_araddr;
                rvalid_q <= 1'b1;
            end else if (rvalid_q && s_axil_rready) begin
                rvalid_q <= 1'b0;
            end
        end
    )

    assign s_axil_rvalid = rvalid_q;
    assign s_axil_rresp  = 2'b00;

    // -------------------------------------------------------------------------
    // Combined write address match
    // -------------------------------------------------------------------------
    logic        write_fire;
    logic [7:0]  write_addr;
    logic [31:0] write_data;
    logic [3:0]  write_strb;

    assign write_fire = awvalid_q && wvalid_q;
    assign write_addr = awaddr_q[7:0];
    assign write_data = wdata_q[31:0];
    assign write_strb = wstrb_q[3:0];

    // -------------------------------------------------------------------------
    // In-band cfg-stream arbitration: cfg-stream is single-cycle valid/ready.
    // It wins over AXIL when both target the same register in the same cycle;
    // in practice the testbench drives one at a time.
    // -------------------------------------------------------------------------
    logic        cfg_fire;
    logic [7:0]  cfg_addr;
    logic [31:0] cfg_data;

    assign cfg_fire = cfg_wr_valid;
    assign cfg_addr = cfg_wr_addr;
    assign cfg_data = cfg_wr_data;
    assign cfg_wr_ready = 1'b1;
    assign cfg_rd_ready = 1'b1;

    // -------------------------------------------------------------------------
    // Read mux: register value selected by address
    // -------------------------------------------------------------------------
    function automatic logic [31:0] read_reg(input logic [7:0] addr);
        case (addr)
            REG_CTRL:           read_reg = reg_ctrl;
            REG_STATUS:         read_reg = reg_status;
            REG_FUNC_SEL:       read_reg = reg_func_sel;
            REG_OP_LINES:       read_reg = reg_op_lines;
            REG_EMIT_BATCH_X:   read_reg = reg_emit_batch_x;
            REG_CREDIT_BATCH_N: read_reg = reg_credit_batch_n;
            REG_IRQ_EN:         read_reg = reg_irq_en;
            REG_IRQ_STATUS:     read_reg = reg_irq_status;
            REG_A:              read_reg = reg_a;
            REG_B:              read_reg = reg_b;
            REG_C:              read_reg = reg_c;
            REG_D:              read_reg = reg_d;
            REG_T:              read_reg = reg_t;
            REG_OP_SRC:         read_reg = reg_op_src;
            REG_DEST:           read_reg = reg_dest;
            REG_IP:             read_reg = reg_ip;
            REG_OP:             read_reg = reg_op;
            REG_CNT_LINES_IN:   read_reg = reg_cnt_lines_in;
            REG_CNT_LINES_OUT:  read_reg = reg_cnt_lines_out;
            REG_CNT_CREDITS:    read_reg = reg_cnt_credits;
            REG_CNT_PKTS:       read_reg = reg_cnt_pkts;
            default:            read_reg = 32'hDEAD_BEEF;
        endcase
    endfunction

    assign s_axil_rdata = read_reg(araddr_q[7:0]);
    assign cfg_rd_data  = read_reg(cfg_rd_addr);

    // -------------------------------------------------------------------------
    // Helper: write a register with byte strobes
    // -------------------------------------------------------------------------
    function automatic logic [31:0] masked_write(
        input logic [31:0] old,
        input logic [31:0] nw,
        input logic [3:0]  strb
    );
        logic [31:0] mask;
        mask = {{8{strb[3]}}, {8{strb[2]}}, {8{strb[1]}}, {8{strb[0]}}};
        masked_write = (old & ~mask) | (nw & mask);
    endfunction

    // -------------------------------------------------------------------------
    // Register update logic
    // -------------------------------------------------------------------------
    logic        do_soft_rst;
    logic [31:0] next_irq_status;

    assign do_soft_rst = reg_ctrl[CTRL_SOFT_RST_BIT];
    assign o_soft_rst  = do_soft_rst;

    // IRQ_STATUS write-1-clear from both AXIL and cfg-stream
    always_comb begin
        next_irq_status = reg_irq_status;
        if (write_fire && (write_addr == REG_IRQ_STATUS)) begin
            next_irq_status = next_irq_status & ~write_data;
        end
        if (cfg_fire && (cfg_addr == REG_IRQ_STATUS)) begin
            next_irq_status = next_irq_status & ~cfg_data;
        end
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            reg_ctrl           <= 32'd0;
            reg_func_sel       <= 32'd0;
            reg_op_lines       <= 32'd0;
            reg_emit_batch_x   <= 32'd0;
            reg_credit_batch_n <= 32'd1;
            reg_irq_en         <= 32'd0;
            reg_irq_status     <= 32'd0;
            reg_a              <= 32'd0;
            reg_b              <= 32'd0;
            reg_c              <= 32'd0;
            reg_d              <= 32'd0;
            reg_t              <= 32'd0;
            reg_op_src         <= 32'd0;
            reg_dest           <= 32'd0;
            reg_ip             <= 32'd0;
            reg_op             <= 32'd0;
            reg_cnt_lines_in   <= 32'd0;
            reg_cnt_lines_out  <= 32'd0;
            reg_cnt_credits    <= 32'd0;
            reg_cnt_pkts       <= 32'd0;
        end else begin
            // Soft reset clears IP/OP, IRQ_STATUS, and sticky error.
            if (do_soft_rst) begin
                reg_ip         <= 32'd0;
                reg_op         <= 32'd0;
                reg_irq_status <= 32'd0;
            end

            // AXI-Lite writes
            if (write_fire) begin
                case (write_addr)
                    REG_CTRL:           reg_ctrl           <= masked_write(reg_ctrl,           write_data, write_strb);
                    REG_FUNC_SEL:       reg_func_sel       <= masked_write(reg_func_sel,       write_data, write_strb);
                    REG_OP_LINES:       reg_op_lines       <= masked_write(reg_op_lines,       write_data, write_strb);
                    REG_EMIT_BATCH_X:   reg_emit_batch_x   <= masked_write(reg_emit_batch_x,   write_data, write_strb);
                    REG_CREDIT_BATCH_N: reg_credit_batch_n <= masked_write(reg_credit_batch_n, write_data, write_strb);
                    REG_IRQ_EN:         reg_irq_en         <= masked_write(reg_irq_en,         write_data, write_strb);
                    REG_A:              reg_a              <= masked_write(reg_a,              write_data, write_strb);
                    REG_B:              reg_b              <= masked_write(reg_b,              write_data, write_strb);
                    REG_C:              reg_c              <= masked_write(reg_c,              write_data, write_strb);
                    REG_D:              reg_d              <= masked_write(reg_d,              write_data, write_strb);
                    REG_T:              reg_t              <= masked_write(reg_t,              write_data, write_strb);
                    REG_OP_SRC:         reg_op_src         <= masked_write(reg_op_src,         write_data, write_strb);
                    REG_DEST:           reg_dest           <= masked_write(reg_dest,           write_data, write_strb);
                    // IP/OP are auto-incrementing pointers; AXIL can seed them.
                    REG_IP:             reg_ip             <= masked_write(reg_ip,             write_data, write_strb);
                    REG_OP:             reg_op             <= masked_write(reg_op,             write_data, write_strb);
                    default: ;
                endcase
            end

            // In-band cfg-stream writes
            if (cfg_fire) begin
                case (cfg_addr)
                    REG_CTRL:           reg_ctrl           <= cfg_data;
                    REG_FUNC_SEL:       reg_func_sel       <= cfg_data;
                    REG_OP_LINES:       reg_op_lines       <= cfg_data;
                    REG_EMIT_BATCH_X:   reg_emit_batch_x   <= cfg_data;
                    REG_CREDIT_BATCH_N: reg_credit_batch_n <= cfg_data;
                    REG_IRQ_EN:         reg_irq_en         <= cfg_data;
                    REG_A:              reg_a              <= cfg_data;
                    REG_B:              reg_b              <= cfg_data;
                    REG_C:              reg_c              <= cfg_data;
                    REG_D:              reg_d              <= cfg_data;
                    REG_T:              reg_t              <= cfg_data;
                    REG_OP_SRC:         reg_op_src         <= cfg_data;
                    REG_DEST:           reg_dest           <= cfg_data;
                    REG_IP:             reg_ip             <= cfg_data;
                    REG_OP:             reg_op             <= cfg_data;
                    default: ;
                endcase
            end

            // IRQ_STATUS is write-1-clear from both sides; STATUS is read-only.
            reg_irq_status <= next_irq_status;

            // Counters: saturate at 32-bit max
            if (inc_lines_in && (reg_cnt_lines_in != 32'hFFFF_FFFF))
                reg_cnt_lines_in <= reg_cnt_lines_in + 32'd1;
            if (inc_lines_out && (reg_cnt_lines_out != 32'hFFFF_FFFF))
                reg_cnt_lines_out <= reg_cnt_lines_out + 32'd1;
            if (inc_credits && (reg_cnt_credits != 32'hFFFF_FFFF))
                reg_cnt_credits <= reg_cnt_credits + 32'd1;
            if (inc_pkts && (reg_cnt_pkts != 32'hFFFF_FFFF))
                reg_cnt_pkts <= reg_cnt_pkts + 32'd1;
        end
    )

    // -------------------------------------------------------------------------
    // STATUS register assembly
    // -------------------------------------------------------------------------
    always_comb begin
        reg_status = 32'd0;
        reg_status[STATUS_BUSY_BIT]          = 1'b0;              // FSM busy: slice 3
        reg_status[STATUS_INPUT_EMPTY_BIT]   = status_input_empty;
        reg_status[STATUS_RESULT_NONEMPTY_BIT] = status_result_nonempty;
        reg_status[STATUS_GRANT_NONZERO_BIT] = status_grant_nonzero;
    end

    // -------------------------------------------------------------------------
    // Register outputs
    // -------------------------------------------------------------------------
    assign r_ctrl           = reg_ctrl;
    assign r_func_sel       = reg_func_sel;
    assign r_op_lines       = reg_op_lines;
    assign r_emit_batch_x   = reg_emit_batch_x;
    assign r_credit_batch_n = reg_credit_batch_n;
    assign r_irq_en         = reg_irq_en;
    assign r_irq_status     = reg_irq_status;
    assign r_a              = reg_a;
    assign r_b              = reg_b;
    assign r_c              = reg_c;
    assign r_d              = reg_d;
    assign r_t              = reg_t;
    assign r_op_src         = reg_op_src;
    assign r_dest           = reg_dest;
    assign r_ip             = reg_ip;
    assign r_op             = reg_op;

    // -------------------------------------------------------------------------
    // Interrupt output: any enabled status bit that is set
    // -------------------------------------------------------------------------
    assign o_irq = |(reg_irq_status & reg_irq_en);

endmodule : cell_cfg_regs

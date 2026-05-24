// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_master_stub
// Purpose: Apb Master Stub module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module apb_master_stub #(
    parameter int CMD_DEPTH         = 6,
    parameter int RSP_DEPTH         = 6,
    parameter int DATA_WIDTH        = 32,
    parameter int ADDR_WIDTH        = 32,
    parameter int STRB_WIDTH        = DATA_WIDTH / 8,
    parameter int CMD_PACKET_WIDTH  = ADDR_WIDTH + DATA_WIDTH + STRB_WIDTH + 3 + 1 + 1 + 1,
                                        // addr, data, strb, prot, pwrite, first, last
    parameter int RESP_PACKET_WIDTH = DATA_WIDTH + 1 + 1 +  1, // data, pslverr, first, last
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int CPW = CMD_PACKET_WIDTH,
    parameter int RPW = RESP_PACKET_WIDTH
) (
    // Clock and Reset
    input  logic                         pclk,
    input  logic                         presetn,

    // APB interface
    output logic                         m_apb_PSEL,
    output logic                         m_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0]        m_apb_PADDR,
    output logic                         m_apb_PWRITE,
    output logic [DATA_WIDTH-1:0]        m_apb_PWDATA,
    output logic [STRB_WIDTH-1:0]        m_apb_PSTRB,
    output logic [2:0]                   m_apb_PPROT,
    input  logic [DATA_WIDTH-1:0]        m_apb_PRDATA,
    input  logic                         m_apb_PSLVERR,
    input  logic                         m_apb_PREADY,

    // Command Packet (packed)
    input  logic                         cmd_valid,
    output logic                         cmd_ready,
    input  logic [CMD_PACKET_WIDTH-1:0]  cmd_data,

    // Read Return interface (packed)
    output logic                         rsp_valid,
    input  logic                         rsp_ready,
    output logic [RESP_PACKET_WIDTH-1:0] rsp_data
);

    // Unpack command packet
    logic [DW-1:0]       cmd_pwdata;
    logic [AW-1:0]       cmd_paddr;
    logic [SW-1:0]       cmd_pstrb;
    logic [2:0]          cmd_pprot;
    logic                cmd_pwrite;
    logic                cmd_first;
    logic                cmd_last;

    assign {cmd_last, cmd_first, cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata} = cmd_data;

    // Response signals from apb_master
    logic [DW-1:0]       rsp_prdata;
    logic                rsp_pslverr;

    // -----------------------------------------------------------------
    // first/last flag side FIFO
    //
    // apb_master takes cmd_pwrite/paddr/pwdata/pstrb/pprot only — it
    // doesn't carry first/last through its internal cmd→rsp pipeline.
    // The old code tapped {cmd_last, cmd_first} combinationally from
    // the LIVE cmd_data input and packed it into rsp_data alongside
    // rsp_prdata/rsp_pslverr. That's correct only when cmd_data is
    // still holding the same command whose response just arrived —
    // which is rarely true when the upstream (axi4_to_apb_convert)
    // pipelines commands ahead of responses. As soon as the cmd FIFO
    // inside apb_master accepts cmd N+1, the user advances cmd_data
    // to cmd N+1; meanwhile cmd N's rsp_prdata is still draining out
    // of the rsp FIFO and gets paired with cmd N+1's first/last bits.
    //
    // Symptom in the wider system: axi4_to_apb_convert's RSP_IDLE
    // state waits for r_apb_rsp_pkt_first=1 to advance. Cmd N+1's
    // first=0 stomps over cmd N+1's response (which should have
    // had first=1 itself, but got cmd N+2's first=0 stamped on it,
    // etc.). RSP_IDLE never sees first=1 again and the convert FSM
    // hangs forever. Surfaces in the bridge as a TimeoutError on the
    // master AXI4 R channel.
    //
    // Fix: enqueue {cmd_last, cmd_first} into a small FIFO on every
    // cmd-side handshake, dequeue on every rsp-side handshake. The
    // FIFO mirrors the depth of the apb_master cmd FIFO so it never
    // backpressures the cmd path more than the cmd FIFO itself.
    // -----------------------------------------------------------------
    logic [1:0]          fl_in_data;
    logic [1:0]          fl_out_data;
    logic                fl_in_ready;
    logic                fl_out_valid;
    logic                out_cmd_last;
    logic                out_cmd_first;

    assign fl_in_data = {cmd_last, cmd_first};
    assign {out_cmd_last, out_cmd_first} = fl_out_data;

    gaxi_fifo_sync #(
        .DATA_WIDTH (2),
        .DEPTH      (CMD_DEPTH)
    ) u_first_last_fifo (
        .axi_aclk    (pclk),
        .axi_aresetn (presetn),
        .wr_valid    (cmd_valid && cmd_ready),
        .wr_ready    (fl_in_ready),
        .wr_data     (fl_in_data),
        .rd_valid    (fl_out_valid),
        .rd_ready    (rsp_valid && rsp_ready),
        .rd_data     (fl_out_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Pack response packet with the first/last bits that belong to the
    // command whose response is being emitted right now (not whatever
    // cmd is currently presented on the cmd_data input).
    assign rsp_data = {out_cmd_last, out_cmd_first, rsp_pslverr, rsp_prdata};

    // Instantiate fully-tested apb_master
    apb_master #(
        .ADDR_WIDTH  (ADDR_WIDTH),
        .DATA_WIDTH  (DATA_WIDTH),
        .CMD_DEPTH   (CMD_DEPTH),
        .RSP_DEPTH   (RSP_DEPTH)
    ) u_apb_master (
        .pclk           (pclk),
        .presetn        (presetn),
        // APB interface
        .m_apb_PSEL     (m_apb_PSEL),
        .m_apb_PENABLE  (m_apb_PENABLE),
        .m_apb_PADDR    (m_apb_PADDR),
        .m_apb_PWRITE   (m_apb_PWRITE),
        .m_apb_PWDATA   (m_apb_PWDATA),
        .m_apb_PSTRB    (m_apb_PSTRB),
        .m_apb_PPROT    (m_apb_PPROT),
        .m_apb_PRDATA   (m_apb_PRDATA),
        .m_apb_PSLVERR  (m_apb_PSLVERR),
        .m_apb_PREADY   (m_apb_PREADY),
        // Command interface (unpacked)
        .cmd_valid      (cmd_valid),
        .cmd_ready      (cmd_ready),
        .cmd_pwrite     (cmd_pwrite),
        .cmd_paddr      (cmd_paddr),
        .cmd_pwdata     (cmd_pwdata),
        .cmd_pstrb      (cmd_pstrb),
        .cmd_pprot      (cmd_pprot),
        // Response interface (unpacked)
        .rsp_valid      (rsp_valid),
        .rsp_ready      (rsp_ready),
        .rsp_prdata     (rsp_prdata),
        .rsp_pslverr    (rsp_pslverr)
    );

endmodule : apb_master_stub

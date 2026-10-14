// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: hive_descriptor_gen
// Purpose: HIVE-C descriptor assembly + injection queue (Block 1 submodule)
//          Firmware writes an 8-word descriptor record into a mailbox register
//          file and pulses the doorbell; this block assembles the 256-bit CDA
//          beat per HAS §4.2, pushes it into a small FIFO, and exposes a
//          firmware-visible stall while the FIFO is full.
//
//          Doorbell-while-full policy: the doorbell is IGNORED while stall is
//          high.  No descriptor is dropped or overwritten; firmware must poll
//          stall and re-ring the doorbell after draining.
//
// Documentation: projects/components/compute-eng-ip/hive-serv/docs/hive_has/ch04_interfaces/02_packet_formats.md
//                projects/components/compute-eng-ip/hive-serv/docs/hive_mas/ch02_blocks/02_hive_c_controller.md
// Subsystem: hive-serv
//
// Author: sean galloway
// Created: 2026-10-13

`timescale 1ns / 1ps

`include "reset_defs.svh"

module hive_descriptor_gen #(
    parameter int QUEUE_DEPTH = 8
)(
    input  logic         clk,
    input  logic         rst_n,

    // Mailbox register-file write port (integration: driven by AXIL window / core bus)
    input  logic         mbox_we,
    input  logic [3:0]   mbox_addr,   // 0..7 field words, 8 = doorbell
    input  logic [31:0]  mbox_wdata,

    // CDA descriptor queue output (to the injection path)
    output logic         q_valid,
    input  logic         q_ready,
    output logic [255:0] q_desc,
    output logic         stall          // queue full; firmware-visible, never drops a doorbell
);

    // Mailbox field words (HAS §4.2)
    //   word0/1 = src[63:0] (lo,hi)
    //   word2/3 = dst[63:0] (lo,hi)
    //   word4   = length[31:0]
    //   word5   = 2D stride
    //   word6   = control flags
    //   word7   = next-descriptor pointer
    logic [31:0] mbox_regs [0:7];

    // Assembled 256-bit CDA descriptor beat
    logic [255:0] assembled_desc;

    // FIFO push control
    logic fifo_full;
    logic fifo_empty;
    logic fifo_wr;

    // Field assembly into the HAS §4.2 bit map:
    //   [255:192] src, [191:128] dst, [127:96] length, [95:64] stride,
    //   [63:32] flags, [31:0] next pointer
    assign assembled_desc = {mbox_regs[1], mbox_regs[0],   // src (hi, lo)
                             mbox_regs[3], mbox_regs[2],   // dst (hi, lo)
                             mbox_regs[4],                  // length
                             mbox_regs[5],                  // stride
                             mbox_regs[6],                  // flags
                             mbox_regs[7]};                 // next pointer

    // Doorbell push: accepted only when there is space.  A doorbell while full
    // is ignored and leaves stall asserted for firmware to see.
    assign fifo_wr = mbox_we && (mbox_addr == 4'd8) && !fifo_full;
    assign stall   = fifo_full;
    assign q_valid = !fifo_empty;

    // Mailbox register-file writes
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int i = 0; i < 8; i++) begin
                mbox_regs[i] <= '0;
            end
        end else begin
            if (mbox_we && (mbox_addr < 4'd8)) begin
                mbox_regs[mbox_addr[2:0]] <= mbox_wdata;
            end
        end
    )

    // Descriptor injection FIFO.  Mux-mode output: q_desc is the current head
    // combinationally, so a consumer sampling q_valid and q_desc in the cycle
    // it raises q_ready sees the beat that handshake will pop (0-latency read).
    // The downstream axis4_master registers accepted beats, so no additional
    // output register is needed here.
    fifo_sync #(
        .REGISTERED (0),
        .DATA_WIDTH (256),
        .DEPTH      (QUEUE_DEPTH)
    ) u_desc_fifo (
        .clk              (clk),
        .rst_n            (rst_n),
        .write            (fifo_wr),
        .wr_data          (assembled_desc),
        .wr_full          (fifo_full),
        .wr_almost_full   (),
        .read             (q_valid && q_ready),
        .rd_data          (q_desc),
        .rd_empty         (fifo_empty),
        .rd_almost_empty  ()
    );

endmodule : hive_descriptor_gen

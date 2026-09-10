// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: smbus_trans_decode
// Purpose: The SMBus 2.0 transaction table, as combinational logic.
//
// "What does transaction type N consist of" is a specification lookup, not a
// state machine, and it is the answer the sequencer needs in five different
// places. Keeping it here means the protocol is stated ONCE: no arm of the
// FSM gets to have its own opinion about whether a Read Word needs a repeated
// START or how many data bytes a Write Byte sends.
//
// The full table is in rtl/smbus/README.md. The two rules worth restating
// where the logic lives:
//
//   A READ THAT CARRIES A COMMAND CODE NEEDS THE REPEATED START. The slave
//   must be addressed for write to receive the command, then addressed again
//   for read. Only Receive Byte, which has no command code, addresses for
//   read straight away.
//
//   data_bytes IS PER TRANSACTION TYPE. block_count governs the block
//   transfers and nothing else - a Write Byte sends exactly one data byte
//   whatever block_count happens to hold from a previous transfer. (GitHub
//   #58 item 10: this used to be `bytes_total <= block_count` with no case
//   on the type at all.)

`timescale 1ns / 1ps

module smbus_trans_decode #(
    parameter int FIFO_DEPTH = 32
) (
    input  wire [3:0] trans_type,
    input  wire [5:0] block_count,

    output wire       has_cmd,        // sends a command byte after the address
    output wire       is_read,        // data flows slave -> master
    output wire       needs_restart,  // read that must re-address after Sr
    output wire       tx_from_fifo,   // transmitted data comes from the TX FIFO
    output wire       sends_count,    // sends a byte-count byte (block write)
    output wire       recvs_count,    // receives a byte-count byte (block read)
    output wire [5:0] data_bytes      // data bytes, excluding count and PEC
);

    localparam logic [3:0] TRANS_QUICK_CMD   = 4'h0;
    localparam logic [3:0] TRANS_SEND_BYTE   = 4'h1;
    localparam logic [3:0] TRANS_RECV_BYTE   = 4'h2;
    localparam logic [3:0] TRANS_WRITE_BYTE  = 4'h3;
    localparam logic [3:0] TRANS_READ_BYTE   = 4'h4;
    localparam logic [3:0] TRANS_WRITE_WORD  = 4'h5;
    localparam logic [3:0] TRANS_READ_WORD   = 4'h6;
    localparam logic [3:0] TRANS_BLOCK_WRITE = 4'h7;
    localparam logic [3:0] TRANS_BLOCK_READ  = 4'h8;
    localparam logic [3:0] TRANS_BLOCK_PROC  = 4'h9;
    // The read-direction Quick Command. The R/W bit IS the payload of a
    // quick command, so both directions have to be reachable; giving the
    // read form its own code keeps SMBUS_COMMAND's layout unchanged and
    // avoids an rw bit that would be meaningless for every other type
    // (RLB-011).
    localparam logic [3:0] TRANS_QUICK_CMD_RD = 4'hA;

    localparam logic [5:0] FIFO_DEPTH_6B = 6'(FIFO_DEPTH);

    logic [5:0] w_block_clamped;
    logic [5:0] w_data_bytes;

    // A block count of 0 is not a legal SMBus block length (1..32); clamping
    // it to 1 keeps the FSM's "more bytes?" arithmetic from wrapping.
    //
    // The over-length clamp only EXISTS when the depth is under 63: the field
    // is six bits, so at 63 it cannot name a longer block and the comparison
    // would be constant. Writing that as a generate says so, rather than
    // leaving a lint warning that has to be re-diagnosed at every depth.
    generate
        if (FIFO_DEPTH < 63) begin : g_clamp_depth
            assign w_block_clamped = (block_count == 6'd0)         ? 6'd1 :
                                     (block_count > FIFO_DEPTH_6B) ? FIFO_DEPTH_6B :
                                                                     block_count;
        end else begin : g_clamp_zero_only
            assign w_block_clamped = (block_count == 6'd0) ? 6'd1 : block_count;
        end
    endgenerate

    assign has_cmd = (trans_type == TRANS_WRITE_BYTE)  ||
                     (trans_type == TRANS_READ_BYTE)   ||
                     (trans_type == TRANS_WRITE_WORD)  ||
                     (trans_type == TRANS_READ_WORD)   ||
                     (trans_type == TRANS_BLOCK_WRITE) ||
                     (trans_type == TRANS_BLOCK_READ)  ||
                     (trans_type == TRANS_BLOCK_PROC);

    assign is_read = (trans_type == TRANS_RECV_BYTE) ||
                     (trans_type == TRANS_READ_BYTE) ||
                     (trans_type == TRANS_READ_WORD) ||
                     (trans_type == TRANS_BLOCK_READ) ||
                     (trans_type == TRANS_QUICK_CMD_RD);

    assign needs_restart = (trans_type == TRANS_READ_BYTE)  ||
                           (trans_type == TRANS_READ_WORD)  ||
                           (trans_type == TRANS_BLOCK_READ) ||
                           (trans_type == TRANS_BLOCK_PROC);

    assign tx_from_fifo = (trans_type == TRANS_WRITE_WORD)  ||
                          (trans_type == TRANS_BLOCK_WRITE) ||
                          (trans_type == TRANS_BLOCK_PROC);

    assign sends_count = (trans_type == TRANS_BLOCK_WRITE) ||
                         (trans_type == TRANS_BLOCK_PROC);

    assign recvs_count = (trans_type == TRANS_BLOCK_READ) ||
                         (trans_type == TRANS_BLOCK_PROC);

    always_comb begin
        unique case (trans_type)
            TRANS_QUICK_CMD:   w_data_bytes = 6'd0;
            TRANS_QUICK_CMD_RD: w_data_bytes = 6'd0;
            TRANS_SEND_BYTE:   w_data_bytes = 6'd1;
            TRANS_RECV_BYTE:   w_data_bytes = 6'd1;
            TRANS_WRITE_BYTE:  w_data_bytes = 6'd1;
            TRANS_READ_BYTE:   w_data_bytes = 6'd1;
            TRANS_WRITE_WORD:  w_data_bytes = 6'd2;
            TRANS_READ_WORD:   w_data_bytes = 6'd2;
            TRANS_BLOCK_WRITE: w_data_bytes = w_block_clamped;
            // Block Read's real count comes from the slave and replaces this
            // seed; the seed is the FIFO depth so a slave that never sends a
            // count cannot make the FSM think it is already finished.
            TRANS_BLOCK_READ:  w_data_bytes = FIFO_DEPTH_6B;
            TRANS_BLOCK_PROC:  w_data_bytes = w_block_clamped;
            default:           w_data_bytes = 6'd0;
        endcase
    end

    assign data_bytes = w_data_bytes;

endmodule

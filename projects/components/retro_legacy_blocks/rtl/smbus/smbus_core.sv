// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: smbus_core
// Purpose: SMBus 2.0 master transaction sequencer.
// This module owns the TRANSACTION: which bytes go out, in what order, with
// what R/W bit, where the repeated START goes, which byte is ACKed, what the
// PEC covers, and when it is done. It owns no bit timing and touches neither
// SCL nor SDA - every line movement is a request to smbus_bit_phy.
// THE CONTRACTS THIS MODULE OBEYS ARE STATED IN FULL IN rtl/smbus/README.md -
// the transaction table, where each byte comes from, what the PEC covers, and
// what busy / completion / recovery mean. Each is repeated once, at the logic
// that obeys it. Three shape the whole FSM:
//   EVERY READ WITH A COMMAND CODE HAS A REPEATED START; SMBUS_BLOCK_COUNT
//   governs block transfers only.
//   EVERY EXIT RUNS THROUGH A STOP (bus recovery first if SDA is stuck);
//   busy=0 always coincides with both lines released.
//
`timescale 1ns / 1ps

`include "reset_defs.svh"

module smbus_core #(
    parameter int FIFO_DEPTH = 32   // TX/RX FIFO depth (32 bytes per SMBus 2.0)
) (
    input wire clk,              // System clock
    input wire rst_n,            // Active-low reset (house convention)
    //--- SMBus Physical Interface
    input  wire smb_scl_i,
    output wire smb_scl_o,
    output wire smb_scl_t,
    input  wire smb_sda_i,
    output wire smb_sda_o,
    output wire smb_sda_t,
    //--- Configuration from Registers
    input wire        cfg_master_en,
    input wire        cfg_slave_en,
    input wire        cfg_pec_en,
    input wire        cfg_fast_mode,
    input wire        cfg_fifo_reset,
    input wire        cfg_soft_reset,
    input wire [15:0] cfg_clk_div,
    input wire [23:0] cfg_timeout,
    input wire [6:0]  cfg_own_addr,
    input wire        cfg_own_addr_en,
    input wire        cfg_slave_gc_en,
    input wire        cfg_slave_nack_all,
    input wire        cfg_slave_pec_en,
    input wire        cfg_slave_stretch_en,
    input wire [3:0]  cmd_trans_type,
    input wire [7:0]  cmd_code,
    input wire [6:0]  cmd_slave_addr,
    input wire        cmd_start,
    input wire        cmd_stop,
    input wire [7:0]  cmd_data_byte,
    input wire [5:0]  cmd_block_count,
    output wire       status_busy,
    output wire       status_bus_error,
    output wire       status_timeout_error,
    output wire       status_pec_error,
    output wire       status_arb_lost,
    output wire       status_nak_received,
    output wire       status_slave_addressed,
    output wire       status_slave_rd_not_wr,
    output wire       status_slave_stretching,
    output wire       status_slave_pec_error,
    output wire [7:0] status_slave_pec_value,
    output wire       status_complete,
    output wire [3:0] status_fsm_state,
    output wire [7:0] int_status,   // sticky, cleared by a decoded W1C
    input  wire [7:0] sw_clr_int_status,
    output wire [7:0] data_byte_out,     // received byte for SMBUS_DATA
    output wire       data_byte_we,      // ... written only when there is one
    // Block count writeback: a Block Read learns its count from the slave
    output wire [5:0] block_count_out,
    output wire       block_count_we,
    input  wire [7:0] tx_fifo_wdata,
    input  wire       tx_fifo_wr,
    output wire [5:0] tx_fifo_level,
    output wire       tx_fifo_full,
    output wire       tx_fifo_empty,
    output wire [7:0] rx_fifo_rdata,
    input  wire       rx_fifo_rd,
    output wire [5:0] rx_fifo_level,
    output wire       rx_fifo_full,
    output wire       rx_fifo_empty,
    output wire [7:0] pec_wr_data,   // what SMBUS_PEC should show
    output wire       pec_we
);
    //--- Master FSM States - the encoding is ABI (SMBUS_STATUS.fsm_state)
    typedef enum logic [3:0] {
        M_IDLE          = 4'h0,
        M_START         = 4'h1,
        M_ADDR          = 4'h2,
        M_ADDR_ACK      = 4'h3,
        M_CMD           = 4'h4,
        M_CMD_ACK       = 4'h5,
        M_DATA_WR       = 4'h6,
        M_DATA_WR_ACK   = 4'h7,
        M_DATA_RD       = 4'h8,
        M_DATA_RD_ACK   = 4'h9,
        M_PEC_WR        = 4'hA,
        M_PEC_WR_ACK    = 4'hB,
        M_PEC_RD        = 4'hC,
        M_STOP          = 4'hD,
        M_ERROR         = 4'hE,
        M_RESTART       = 4'hF
    } master_state_t;
    //--- PHY primitive encoding - must match smbus_bit_phy
    localparam logic [2:0] PHY_OP_START   = 3'd0;
    localparam logic [2:0] PHY_OP_RESTART = 3'd1;
    localparam logic [2:0] PHY_OP_STOP    = 3'd2;
    localparam logic [2:0] PHY_OP_TX      = 3'd3;
    localparam logic [2:0] PHY_OP_RX      = 3'd4;
    //--- Declarations
    master_state_t r_master_state;

    logic        r_busy;
    logic        r_bus_error;
    logic        r_timeout_error;
    logic        r_pec_error;
    logic        r_nak_received;
    logic        r_complete;
    logic [3:0]  r_bit_counter;
    logic [7:0]  r_shift_reg;
    logic [7:0]  r_tx_byte;      // unshifted copy of the byte being sent
    logic        r_ack_bit;
    logic        r_ack_valid;
    logic        r_bit_go;       // a bit is queued for the PHY
    logic [5:0]  r_byte_counter;
    logic [5:0]  r_bytes_total;
    logic [3:0]  r_trans_type;
    logic [6:0]  r_slave_addr;
    logic [7:0]  r_cmd_code;
    logic        r_pec_en;
    logic        r_count_sent;      // block-write count byte has gone out
    logic        r_count_rcvd;      // block-read count byte has come back
    logic        r_was_count_byte;  // the byte just received WAS the count
    logic        r_pec_phase;       // the byte in flight is the PEC byte
    logic        r_read_phase;      // data direction of the current phase
    logic        r_started;         // a START has been put on the wire
    logic [2:0]  r_phy_op;
    logic        r_phy_req;
    logic        r_phy_abort;
    logic        r_phy_recover;  // ... and start it with bus recovery
    logic        r_phy_tmo_ack;  // the timeout report has been taken
    logic        w_abort_active;
    logic        w_abort_done;
    logic        w_quiescent;
    logic        r_phy_tx_bit;
    logic [7:0]  r_data_byte_out;
    logic        r_data_byte_we;
    logic [5:0]  r_block_count_out;
    logic        r_block_count_we;
    logic        r_pec_we;
    logic [7:0]  r_pec_rx_byte;
    logic        r_pec_rx_valid;

    logic        w_tx_fifo_rd;
    //--- Slave engine, and the wired-AND of the two engines' pull-downs
    logic        w_slv_sda_low;
    logic        w_slv_scl_low;
    logic        w_slv_addressed;
    logic        w_slv_rd_not_wr;
    logic        w_slv_stretching;
    logic        w_slv_done;
    logic        w_slv_pec_error;
    logic [7:0]  w_slv_pec_value;
    logic [7:0]  w_slv_rx_wdata;
    logic        w_slv_rx_wr;
    logic        w_slv_tx_rd;
    logic        w_master_active;
    logic        w_mst_scl_o;
    logic        w_mst_scl_t;
    logic        w_mst_sda_o;
    logic        w_mst_sda_t;
    logic [7:0]  w_tx_fifo_rdata;
    logic        r_rx_fifo_wr;
    logic [7:0]  r_rx_fifo_wdata;
    // The LIVE running CRC. Named, not a port: the DV suite reads it.
    /* verilator lint_off UNUSEDSIGNAL */
    logic [7:0]  pec_value;
    /* verilator lint_on UNUSEDSIGNAL */
    logic        w_pec_clear;
    logic [7:0]  w_pec_data;
    logic        w_pec_valid;
    logic [7:0]  w_pec_out;
    logic        w_phy_done;
    logic        w_phy_rx_bit;
    logic        w_phy_busy;
    logic        w_phy_timeout;
    logic        w_phy_arb_lost;
    logic        r_arb_lost;
    logic        w_recover_failed;
    logic        w_sda_sync;
    logic        w_scl_sync;
    logic        w_pre_start_recoverable;
    logic        w_error_next;
    logic        w_start_req;
    logic        w_abort_req;
    logic        w_has_cmd;
    logic        w_is_read;
    logic        w_needs_restart;
    logic [3:0]  w_dec_trans_type;
    logic [5:0]  w_data_bytes;
    logic        w_tx_from_fifo;
    logic        w_sends_count;
    logic        w_recvs_count;
    logic        w_byte_tx_state;
    logic        w_byte_rx_state;
    logic        w_ack_state;
    logic [3:0]  w_tx_ack_state;
    logic        w_byte_last_bit;
    logic [7:0]  w_rx_byte;
    logic [7:0]  w_next_tx_byte;
    logic [5:0]  w_rx_count_clamped;
    logic        w_more_data;
    logic        w_send_ack;
    logic        w_tx_underrun;
    logic [7:0]  w_pec_wr_data;
    logic        w_int_cond_error;
    // BEFORE ANYTHING OF OURS IS FRAMED, recovery only suits a stuck SDA on a
    // quiet bus: if SCL is low too, somebody else is mid-transfer.
    assign w_pre_start_recoverable = !w_sda_sync && w_scl_sync;

    // ONE ENGINE ON THE WIRE AT A TIME. A master START while this block's own
    // target half is answering would put the block on the bus twice, so the
    // request is refused rather than queued: software sees the command not
    // take and can retry, which is the same shape as losing arbitration.
    // The claim is "our target is ANSWERING", not "the bus is busy" - see the
    // note on `addressed` in smbus_slave_engine.
    assign w_start_req = cmd_start && cfg_master_en && !w_slv_addressed;

    // EVERY error term, including ones landing on this very edge.
    assign w_error_next = r_pec_error || r_bus_error || r_nak_received ||
                          r_timeout_error || r_arb_lost || w_phy_arb_lost ||
                          (w_phy_done && w_recover_failed) ||
                          (w_phy_done && w_phy_timeout);

    // Stop WITHOUT start, while running, is an abort; with start, a no-op.
    assign w_abort_req = cmd_stop && !cmd_start && r_busy;

    // The protocol table, once: the LIVE command register in M_IDLE (sizing
    // the transfer as cmd_start is accepted), the LATCHED type after.
    assign w_dec_trans_type = (r_master_state == M_IDLE) ? cmd_trans_type
                                                         : r_trans_type;

    smbus_trans_decode #(
        .FIFO_DEPTH (FIFO_DEPTH)
    ) u_trans_decode (
        .trans_type    (w_dec_trans_type),
        .block_count   (cmd_block_count),
        .has_cmd       (w_has_cmd),
        .is_read       (w_is_read),
        .needs_restart (w_needs_restart),
        .tx_from_fifo  (w_tx_from_fifo),
        .sends_count   (w_sends_count),
        .recvs_count   (w_recvs_count),
        .data_bytes    (w_data_bytes)
    );
    smbus_flow_rules #(
        .FIFO_DEPTH (FIFO_DEPTH)
    ) u_flow (
        .master_state     (r_master_state),
        .bit_counter      (r_bit_counter),
        .shift_reg        (r_shift_reg),
        .phy_rx_bit       (w_phy_rx_bit),
        .byte_counter     (r_byte_counter),
        .bytes_total      (r_bytes_total),
        .ack_valid        (r_ack_valid),
        .ack_bit          (r_ack_bit),
        .pec_en           (r_pec_en),
        .pec_phase        (r_pec_phase),
        .count_sent       (r_count_sent),
        .sends_count      (w_sends_count),
        .needs_restart    (w_needs_restart),
        .tx_from_fifo     (w_tx_from_fifo),
        .tx_fifo_empty    (tx_fifo_empty),
        .byte_tx_state    (w_byte_tx_state),
        .byte_rx_state    (w_byte_rx_state),
        .ack_state        (w_ack_state),
        .tx_ack_state     (w_tx_ack_state),
        .byte_last_bit    (w_byte_last_bit),
        .rx_byte          (w_rx_byte),
        .next_tx_byte     (w_next_tx_byte),
        .rx_count_clamped (w_rx_count_clamped),
        .more_data        (w_more_data),
        .send_ack         (w_send_ack),
        .tx_underrun      (w_tx_underrun),
        .tx_fifo_rd       (w_tx_fifo_rd)
    );
    smbus_byte_fifos #(
        .FIFO_DEPTH (FIFO_DEPTH)
    ) u_fifos (
        .clk        (clk),
        .rst_n      (rst_n),
        .soft_reset (cfg_soft_reset),
        .fifo_reset (cfg_fifo_reset),
        .tx_wdata   (tx_fifo_wdata),
        .tx_wr      (tx_fifo_wr),
        .tx_rd      (w_tx_fifo_rd | w_slv_tx_rd),
        .tx_rdata   (w_tx_fifo_rdata),
        .tx_level   (tx_fifo_level),
        .tx_full    (tx_fifo_full),
        .tx_empty   (tx_fifo_empty),
        .rx_wdata   (w_slv_rx_wr ? w_slv_rx_wdata : r_rx_fifo_wdata),
        .rx_wr      (r_rx_fifo_wr | w_slv_rx_wr),
        .rx_rd      (rx_fifo_rd),
        .rx_rdata   (rx_fifo_rdata),
        .rx_level   (rx_fifo_level),
        .rx_full    (rx_fifo_full),
        .rx_empty   (rx_fifo_empty)
    );
    //--- PEC engine, cleared ONLY on the START request.
    assign w_pec_clear = cfg_soft_reset ||
                         (r_master_state == M_IDLE && w_start_req);

    assign w_pec_valid = (w_phy_done && w_byte_last_bit) &&
                         ((w_byte_tx_state && (r_master_state != M_PEC_WR)) ||
                          (w_byte_rx_state && (r_master_state != M_PEC_RD)));
    assign w_pec_data  = w_byte_tx_state ? r_tx_byte : w_rx_byte;

    smbus_pec u_pec (
        .clk        (clk),
        .rst_n      (rst_n),
        .enable     (1'b1),
        .clear      (w_pec_clear),
        .data_in    (w_pec_data),
        .data_valid (w_pec_valid),
        .crc_out    (w_pec_out)
    );

    assign pec_value = w_pec_out;
    assign w_pec_wr_data = r_pec_rx_valid ? r_pec_rx_byte : w_pec_out;
    assign pec_wr_data   = w_pec_wr_data;
    smbus_bit_phy u_bit_phy (
        .clk            (clk),
        .rst_n          (rst_n),
        .smb_scl_i      (smb_scl_i),
        .smb_scl_o      (w_mst_scl_o),
        .smb_scl_t      (w_mst_scl_t),
        .smb_sda_i      (smb_sda_i),
        .smb_sda_o      (w_mst_sda_o),
        .smb_sda_t      (w_mst_sda_t),
        .cfg_clk_div    (cfg_clk_div),
        .cfg_fast_mode  (cfg_fast_mode),
        .cfg_timeout    (cfg_timeout),
        .cfg_soft_reset (cfg_soft_reset),
        .op             (r_phy_op),
        .op_req         (r_phy_req),
        .abort_req      (r_phy_abort),
        .abort_recover  (r_phy_recover),
        .tx_bit         (r_phy_tx_bit),
        .op_done        (w_phy_done),
        .rx_bit         (w_phy_rx_bit),
        .arb_lost       (w_phy_arb_lost),
        .phy_busy       (w_phy_busy),
        .phy_timeout    (w_phy_timeout),
        .recover_failed (w_recover_failed),
        .sda_sync       (w_sda_sync),
        .scl_sync       (w_scl_sync),
        .timeout_ack    (r_phy_tmo_ack)
    );
    smbus_abort_track u_abort (
        .clk          (clk),
        .rst_n        (rst_n),
        .soft_reset   (cfg_soft_reset),
        .abort_req    (r_phy_abort),
        .phy_busy     (w_phy_busy),
        .phy_done     (w_phy_done),
        .phy_req      (r_phy_req),
        .abort_active (w_abort_active),
        .abort_done   (w_abort_done),
        .quiescent    (w_quiescent)
    );
    //--- Master transaction sequencer
    `ALWAYS_FF_RST(clk, rst_n,
        // SOFT RESET IS THE SAME RESET, SYNCHRONOUSLY: engine, PHY, PEC and
        // both FIFOs restart; the register file is untouched. One list.
        if (`RST_ASSERTED(rst_n) || cfg_soft_reset) begin
            r_master_state    <= M_IDLE;
            r_busy            <= 1'b0;
            r_bus_error       <= 1'b0;
            r_timeout_error   <= 1'b0;
            r_pec_error       <= 1'b0;
            r_nak_received    <= 1'b0;
            r_arb_lost        <= 1'b0;
            r_complete        <= 1'b0;
            r_bit_counter     <= 4'd0;
            r_shift_reg       <= 8'h00;
            r_tx_byte         <= 8'h00;
            r_ack_bit         <= 1'b1;
            r_ack_valid       <= 1'b0;
            r_bit_go          <= 1'b0;
            r_byte_counter    <= 6'd0;
            r_bytes_total     <= 6'd0;
            r_trans_type      <= 4'h0;
            r_slave_addr      <= 7'h00;
            r_cmd_code        <= 8'h00;
            r_pec_en          <= 1'b0;
            r_count_sent      <= 1'b0;
            r_count_rcvd      <= 1'b0;
            r_was_count_byte  <= 1'b0;
            r_pec_phase       <= 1'b0;
            r_read_phase      <= 1'b0;
            r_started         <= 1'b0;
            r_phy_op          <= PHY_OP_START;
            r_phy_req         <= 1'b0;
            r_phy_abort       <= 1'b0;
            r_phy_recover     <= 1'b0;
            r_phy_tmo_ack     <= 1'b0;
            r_phy_tx_bit      <= 1'b1;
            r_data_byte_out   <= 8'h00;
            r_data_byte_we    <= 1'b0;
            r_block_count_out <= 6'd0;
            r_block_count_we  <= 1'b0;
            r_pec_we          <= 1'b0;
            r_pec_rx_byte     <= 8'h00;
            r_pec_rx_valid    <= 1'b0;
            r_rx_fifo_wr      <= 1'b0;
            r_rx_fifo_wdata   <= 8'h00;
        end else begin
            r_phy_req        <= 1'b0;
            r_phy_abort      <= 1'b0;
            r_phy_recover    <= 1'b0;
            r_phy_tmo_ack    <= 1'b0;

                    if (w_phy_done && w_recover_failed) r_bus_error <= 1'b1;

            r_data_byte_we   <= 1'b0;
            r_block_count_we <= 1'b0;
            r_pec_we         <= 1'b0;
            r_rx_fifo_wr     <= 1'b0;

            if ((w_byte_tx_state || w_byte_rx_state) && w_phy_done) begin
                r_shift_reg   <= w_byte_rx_state ? w_rx_byte : w_next_tx_byte;
                r_bit_counter <= r_bit_counter + 4'd1;
                r_bit_go      <= !w_byte_last_bit;
                // On the last bit the FSM below takes over.
            end

            // Qualified with the state as well as r_bit_go, so a stray queued
            // bit is unreachable by construction, not by inspection.
            if (r_bit_go && (w_byte_tx_state || w_byte_rx_state) &&
                !w_phy_busy && !r_phy_req && !w_phy_done) begin
                r_bit_go     <= 1'b0;
                r_phy_req    <= 1'b1;
                r_phy_op     <= w_byte_rx_state ? PHY_OP_RX : PHY_OP_TX;
                r_phy_tx_bit <= w_byte_rx_state ? 1'b1 : r_shift_reg[7];
                if (r_bit_counter == 4'd0) begin
                    r_tx_byte <= r_shift_reg;
                end
            end

            // A transmitted byte is finished when the bit counter reaches 8;
            // it then waits for the ACK. One rule, four states.
            if (w_byte_tx_state && (r_bit_counter == 4'd8)) begin
                r_bit_counter  <= 4'd0;
                r_ack_valid    <= 1'b0;
                r_phy_req      <= 1'b1;
                r_phy_op       <= PHY_OP_RX;
                r_master_state <= master_state_t'(w_tx_ack_state);
            end

            // ACK sampling for all four ACK states; the DECISION is a cycle
            // later, on the REGISTERED r_ack_bit.
            if (w_ack_state && w_phy_done) begin
                r_ack_bit   <= w_phy_rx_bit;
                r_ack_valid <= 1'b1;
            end

            // Global aborts - all end in M_ERROR, which always ends with both
            // lines released. THE ABORT USES r_phy_abort, NOT r_phy_req
            // (op_req is only sampled while the PHY is idle). A NAK IS AN
            // ABORT WHEREVER IT ARRIVES. EVERY STATE THAT CAN WAIT ON SCL IS
            // TIMEOUT-COVERED, M_STOP included.
            // LOSING ARBITRATION IS NOT AN ERROR OF OURS. Another master
            // was transmitting at the same time and won; the bus now belongs
            // to it. The PHY has already released both lines - re-driving
            // them, including to frame a STOP, would corrupt the winner's
            // transfer - so this reports and goes idle, and software retries
            // after the bus is free again. The bus-free wait before START is
            // what makes that retry safe.
            if (w_phy_arb_lost) begin
                r_arb_lost     <= 1'b1;
                r_master_state <= M_IDLE;
                r_busy         <= 1'b0;
                r_ack_valid    <= 1'b0;
            end else if (w_ack_state && r_ack_valid && r_ack_bit) begin
                r_ack_valid    <= 1'b0;
                r_nak_received <= 1'b1;
                r_master_state <= M_ERROR;
                r_phy_abort    <= 1'b1;
            end else if ((r_master_state != M_IDLE) && w_phy_timeout &&
                         !w_abort_active) begin
                r_timeout_error <= 1'b1;
                r_phy_tmo_ack <= 1'b1;   // the report is consumed here
                if ((r_master_state == M_STOP) ||
                    (!r_started && !w_pre_start_recoverable)) begin
                    // YOU ONLY STOP SOMETHING YOU STARTED, and RECOVERY IS
                    // FOR A STUCK SDA on a quiet SCL - see
                    // w_pre_start_recoverable. Everything else here has
                    // already had both lines released by the PHY.
                    r_busy         <= 1'b0;
                    r_master_state <= M_IDLE;
                end else begin
                    // A TIMEOUT ABORT RECOVERS FIRST: whatever stopped
                    // the transfer is still holding something.
                    r_master_state <= M_ERROR;
                    r_phy_abort    <= 1'b1;
                    r_phy_recover  <= 1'b1;
                end
            end else if ((r_master_state != M_IDLE) && (r_master_state != M_ERROR) &&
                         w_abort_req) begin
                r_bus_error    <= 1'b1;
                r_master_state <= M_ERROR;
                r_phy_abort    <= 1'b1;
            end else begin
                unique case (r_master_state)
                M_IDLE: begin
                    if (w_start_req) begin
                        r_busy          <= 1'b1;
                        r_complete      <= 1'b0;
                        r_bus_error     <= 1'b0;
                        r_timeout_error <= 1'b0;
                        r_pec_error     <= 1'b0;
                        r_nak_received  <= 1'b0;
                        r_arb_lost      <= 1'b0;

                        r_trans_type    <= cmd_trans_type;
                        r_slave_addr    <= cmd_slave_addr;
                        r_cmd_code      <= cmd_code;
                        r_pec_en        <= cfg_pec_en;
                        r_bytes_total   <= w_data_bytes;
                        r_byte_counter  <= 6'd0;
                        r_count_sent    <= 1'b0;
                        r_count_rcvd    <= 1'b0;
                        r_pec_phase     <= 1'b0;
                        r_pec_rx_valid  <= 1'b0;
                        r_ack_valid     <= 1'b0;
                        // Per TRANSACTION: "this one has framed something".
                        // Left latched it sent a stuck-SCL START down the
                        // abort path, five stall windows instead of one.
                        r_started       <= 1'b0;

                        r_phy_req       <= 1'b1;
                        r_phy_op        <= PHY_OP_START;
                        r_master_state  <= M_START;
                    end
                end
                M_START: begin
                    if (w_phy_done) begin
                        r_started      <= 1'b1;
                        // A read with a command code is addressed for WRITE
                        // here; Addr+R follows the Sr.
                        r_shift_reg    <= {r_slave_addr,
                                           w_needs_restart ? 1'b0 : w_is_read};
                        r_bit_counter  <= 4'd0;
                        r_read_phase   <= w_needs_restart ? 1'b0 : w_is_read;
                        r_bit_go       <= 1'b1;
                        r_master_state <= M_ADDR;
                    end
                end
                M_RESTART: begin
                    if (w_phy_done) begin
                        r_shift_reg      <= {r_slave_addr, 1'b1};
                        r_bit_counter    <= 4'd0;
                        r_read_phase     <= 1'b1;
                        r_bit_go         <= 1'b1;
                        r_byte_counter   <= 6'd0;
                        r_count_rcvd     <= 1'b0;
                        r_was_count_byte <= 1'b0;
                        if (w_recvs_count) begin
                            r_bytes_total <= 6'(FIFO_DEPTH);
                        end
                        r_master_state   <= M_ADDR;
                    end
                end
                M_ADDR_ACK: begin
                    if (r_ack_valid) begin
                        r_ack_valid <= 1'b0;
                        if (r_read_phase) begin
                            r_bit_counter  <= 4'd0;
                            r_bit_go       <= 1'b1;
                            r_master_state <= M_DATA_RD;
                        end else if (w_has_cmd) begin
                            r_shift_reg    <= r_cmd_code;
                            r_bit_counter  <= 4'd0;
                            r_bit_go       <= 1'b1;
                            r_master_state <= M_CMD;
                        end else if (r_bytes_total != 6'd0) begin
                            r_shift_reg    <= cmd_data_byte;
                            r_bit_counter  <= 4'd0;
                            r_bit_go       <= 1'b1;
                            r_master_state <= M_DATA_WR;
                        end else begin
                                r_phy_req      <= 1'b1;
                            r_phy_op       <= PHY_OP_STOP;
                            r_master_state <= M_STOP;
                        end
                    end
                end
                M_CMD_ACK: begin
                    if (r_ack_valid) begin
                        r_ack_valid <= 1'b0;
                        // w_sends_count FIRST: Block Process Call sets both
                        // it and w_needs_restart, and writes before it reads.
                        if (w_sends_count) begin
                            r_shift_reg    <= {2'b00, r_bytes_total};
                            r_bit_counter  <= 4'd0;
                            r_bit_go       <= 1'b1;
                            r_master_state <= M_DATA_WR;
                        end else if (w_needs_restart) begin
                            r_phy_req      <= 1'b1;
                            r_phy_op       <= PHY_OP_RESTART;
                            r_master_state <= M_RESTART;
                        end else if (w_tx_underrun) begin
                            r_bus_error    <= 1'b1;
                            r_phy_abort    <= 1'b1;
                            r_master_state <= M_ERROR;
                        end else begin
                            r_shift_reg    <= w_tx_from_fifo ? w_tx_fifo_rdata :
                                                               cmd_data_byte;
                            r_bit_counter  <= 4'd0;
                            r_bit_go       <= 1'b1;
                            r_master_state <= M_DATA_WR;
                        end
                    end
                end
                M_DATA_WR_ACK: begin
                    if (r_ack_valid) begin
                        r_ack_valid <= 1'b0;
                        if (w_tx_underrun) begin
                            r_bus_error    <= 1'b1;
                            r_phy_abort    <= 1'b1;
                            r_master_state <= M_ERROR;
                        end else if (w_sends_count && !r_count_sent) begin
                            r_count_sent   <= 1'b1;
                            r_shift_reg    <= w_tx_fifo_rdata;
                            r_bit_counter  <= 4'd0;
                            r_bit_go       <= 1'b1;
                            r_master_state <= M_DATA_WR;
                        end else if (w_more_data) begin
                            r_byte_counter <= r_byte_counter + 6'd1;
                            r_shift_reg    <= w_tx_fifo_rdata;
                            r_bit_counter  <= 4'd0;
                            r_bit_go       <= 1'b1;
                            r_master_state <= M_DATA_WR;
                        end else if (w_needs_restart && !r_read_phase) begin
                            r_byte_counter <= r_byte_counter + 6'd1;
                            r_phy_req      <= 1'b1;
                            r_phy_op       <= PHY_OP_RESTART;
                            r_master_state <= M_RESTART;
                        end else begin
                            r_byte_counter <= r_byte_counter + 6'd1;
                            if (r_pec_en) begin
                                r_shift_reg    <= w_pec_out;
                                r_bit_counter  <= 4'd0;
                                r_pec_phase    <= 1'b1;
                                r_bit_go       <= 1'b1;
                                r_master_state <= M_PEC_WR;
                            end else begin
                                r_phy_req      <= 1'b1;
                                r_phy_op       <= PHY_OP_STOP;
                                r_master_state <= M_STOP;
                            end
                        end
                    end
                end
                M_PEC_WR_ACK: begin
                    if (r_ack_valid) begin
                        r_ack_valid    <= 1'b0;
                        r_phy_req      <= 1'b1;
                        r_phy_op       <= PHY_OP_STOP;
                        r_master_state <= M_STOP;
                    end
                end
                M_DATA_RD: begin
                    if (w_phy_done && w_byte_last_bit) begin
                        // WHAT THIS BYTE WAS is latched here and read a cycle
                        // later by the ACK decision.
                        r_was_count_byte <= w_recvs_count && !r_count_rcvd;
                        if (w_recvs_count && !r_count_rcvd) begin
                            r_count_rcvd      <= 1'b1;
                            r_bytes_total     <= w_rx_count_clamped;
                            r_block_count_out <= w_rx_count_clamped;
                            r_block_count_we  <= 1'b1;
                        end else if (rx_fifo_full) begin
                            // RX OVERRUN, checked for EVERY data byte, the
                            // last included: a full FIFO drops the write
                            // silently.
                            r_bus_error     <= 1'b1;
                        end else begin
                            r_rx_fifo_wr    <= 1'b1;
                            r_rx_fifo_wdata <= w_rx_byte;
                            r_data_byte_out <= w_rx_byte;
                            r_data_byte_we  <= 1'b1;
                        end
                    end else if (r_bit_counter == 4'd8) begin
                        // ACK the count byte and any byte with more to follow.
                        r_bit_counter  <= 4'd0;
                        r_phy_req      <= 1'b1;
                        r_phy_op       <= PHY_OP_TX;
                        // NAK on overrun, whatever w_send_ack would say.
                        r_phy_tx_bit   <= r_was_count_byte ? 1'b0 :
                                          (r_bus_error ? 1'b1 : ~w_send_ack);
                        r_pec_phase    <= 1'b0;
                        r_master_state <= M_DATA_RD_ACK;
                    end
                end
                M_PEC_RD: begin
                    if (w_phy_done && w_byte_last_bit) begin
                        // Compare, do NOT fold the PEC byte into the CRC -
                        // it is the thing being checked.
                        r_pec_error    <= (w_rx_byte != w_pec_out);
                        r_pec_rx_byte  <= w_rx_byte;
                        r_pec_rx_valid <= 1'b1;
                    end else if (r_bit_counter == 4'd8) begin
                        r_bit_counter  <= 4'd0;
                        r_phy_req      <= 1'b1;
                        r_phy_op       <= PHY_OP_TX;
                        r_phy_tx_bit   <= 1'b1;    // always NAK the PEC byte
                        r_pec_phase    <= 1'b1;
                        r_master_state <= M_DATA_RD_ACK;
                    end
                end
                M_DATA_RD_ACK: begin
                    if (w_phy_done) begin
                        if (r_pec_phase) begin
                            r_phy_req      <= 1'b1;
                            r_phy_op       <= PHY_OP_STOP;
                            r_master_state <= M_STOP;
                        end else if (r_bus_error) begin
                            r_phy_req      <= 1'b1;
                            r_phy_op       <= PHY_OP_STOP;
                            r_master_state <= M_STOP;
                        end else if (r_was_count_byte) begin
                            r_bit_counter  <= 4'd0;
                            r_bit_go       <= 1'b1;
                            r_master_state <= M_DATA_RD;
                        end else if (w_more_data) begin
                            r_byte_counter <= r_byte_counter + 6'd1;
                            r_bit_counter  <= 4'd0;
                            r_bit_go       <= 1'b1;
                            r_master_state <= M_DATA_RD;
                        end else begin
                            r_byte_counter <= r_byte_counter + 6'd1;
                            if (r_pec_en) begin
                                r_bit_counter  <= 4'd0;
                                r_bit_go       <= 1'b1;
                                r_master_state <= M_PEC_RD;
                            end else begin
                                r_phy_req      <= 1'b1;
                                r_phy_op       <= PHY_OP_STOP;
                                r_master_state <= M_STOP;
                            end
                        end
                    end
                end
                M_STOP: begin
                    if (w_phy_done) begin
                        r_busy         <= 1'b0;
                        // COMPLETE FROM THE NEXT-STATE ERROR TERMS: the
                        // registered ones are pre-edge, so an error raised ON
                        // this edge - a recovery that just failed - would be
                        // missed, and complete and bus_error would land
                        // together with nothing on the wire.
                        r_complete     <= !w_error_next;
                        r_pec_we       <= 1'b1;
                        r_master_state <= M_IDLE;
                    end
                end
                M_ERROR: begin
                    // Leave on the ABORT'S OWN STOP finishing (see
                    // smbus_abort_track), or on a quiet bus if nothing ran.
                    if (w_abort_done || w_quiescent) begin
                        if (w_phy_timeout) begin
                            r_timeout_error <= 1'b1;
                        end
                        r_busy         <= 1'b0;
                        r_master_state <= M_IDLE;
                    end
                end

                // M_ADDR / M_CMD / M_DATA_WR / M_PEC_WR have no arm: they are
                // driven by the hoisted byte engine above. Falling through to
                // an unconditional M_IDLE here dragged the FSM back to idle
                // every cycle it spent transmitting a byte. Anything ELSE
                // reaching this arm is an illegal encoding.
                default: if (!w_byte_tx_state) r_master_state <= M_IDLE;
                endcase
            end
        end
    )
    // A NAK IS AN ERROR FOR INTERRUPT PURPOSES. It is reported in its own
    // status bit, but it is still a transaction that failed, and software
    // that enabled the error interrupt and then never hears about a NAK has
    // to poll - which is the whole thing the interrupt exists to avoid.
    assign w_int_cond_error = r_bus_error || r_timeout_error || r_pec_error ||
                              r_nak_received;

    // THE TARGET HALF. It shares the synchronized lines, the TX and RX FIFOs
    // and the pins with the master engine, and is inhibited while the master
    // owns the wire.
    assign w_master_active = (r_master_state != M_IDLE) || w_phy_busy;

    smbus_slave_engine u_slave (
        .clk                  (clk),
        .rst_n                (rst_n),
        .sda_sync             (w_sda_sync),
        .scl_sync             (w_scl_sync),
        .sda_drive_low        (w_slv_sda_low),
        .scl_drive_low        (w_slv_scl_low),
        .cfg_slave_en         (cfg_slave_en),
        .cfg_own_addr         (cfg_own_addr),
        .cfg_own_addr_en      (cfg_own_addr_en),
        .cfg_gc_en            (cfg_slave_gc_en),
        .cfg_nack_all         (cfg_slave_nack_all),
        .cfg_pec_en           (cfg_slave_pec_en),
        .cfg_stretch_en       (cfg_slave_stretch_en),
        .cfg_soft_reset       (cfg_soft_reset),
        .master_active        (w_master_active),
        .rx_wdata             (w_slv_rx_wdata),
        .rx_wr                (w_slv_rx_wr),
        .rx_full              (rx_fifo_full),
        .tx_rdata             (w_tx_fifo_rdata),
        .tx_empty             (tx_fifo_empty),
        .tx_rd                (w_slv_tx_rd),
        .addressed            (w_slv_addressed),
        .rd_not_wr            (w_slv_rd_not_wr),
        .stretching           (w_slv_stretching),
        .done                 (w_slv_done),
        .pec_error            (w_slv_pec_error),
        .pec_value            (w_slv_pec_value)
    );

    // OPEN-DRAIN MERGE. Both engines only ever pull DOWN, so the pin is the
    // wired-AND of their releases - the same rule the bus itself obeys, which
    // is why this needs no ownership mux to be electrically correct. The
    // ownership rules above are about protocol, not about drive conflict.
    assign smb_scl_o = w_mst_scl_o && !w_slv_scl_low;
    assign smb_scl_t = w_mst_scl_t && !w_slv_scl_low;
    assign smb_sda_o = w_mst_sda_o && !w_slv_sda_low;
    assign smb_sda_t = w_mst_sda_t && !w_slv_sda_low;

    smbus_int_status u_int_status (
        .clk             (clk),
        // One reset list: soft_reset restarts the engine, and sticky status
        // left over from the transfer it just abandoned is not "the engine
        // started over".
        .rst_n           (rst_n),
        .clear           (cfg_soft_reset),
        .cond_complete   (r_complete),
        .cond_error      (w_int_cond_error),
        .cond_tx_thresh  (tx_fifo_empty),
        .cond_rx_thresh  (!rx_fifo_empty),
        .cond_slave_addr (w_slv_addressed),
        .cond_slave_rx   (w_slv_rx_wr),
        .cond_slave_tx   (w_slv_stretching),
        .cond_slave_done (w_slv_done),
        .sw_clr          (sw_clr_int_status),
        .int_status      (int_status)
    );
    //--- Slave mode / outputs
    assign status_slave_addressed  = w_slv_addressed;
    assign status_slave_rd_not_wr  = w_slv_rd_not_wr;
    assign status_slave_stretching = w_slv_stretching;
    assign status_slave_pec_error  = w_slv_pec_error;
    assign status_slave_pec_value  = w_slv_pec_value;
    assign status_arb_lost        = r_arb_lost;
    assign status_busy           = r_busy;
    assign status_bus_error      = r_bus_error;
    assign status_timeout_error  = r_timeout_error;
    assign status_pec_error      = r_pec_error;
    assign status_nak_received   = r_nak_received;
    assign status_complete       = r_complete;
    assign status_fsm_state      = r_master_state;

    assign data_byte_out         = r_data_byte_out;
    assign data_byte_we          = r_data_byte_we;
    assign block_count_out       = r_block_count_out;
    assign block_count_we        = r_block_count_we;
    assign pec_we                = r_pec_we;

endmodule

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: smbus_config_regs
// Purpose: Configuration register wrapper for SMBus - PeakRDL Wrapper
//
// Wrapper that instantiates PeakRDL-generated register block and adapter,
// mapping between the generated hwif signals and the SMBus core interface.
//
// ARCHITECTURE:
//   cmd/rsp --> peakrdl_to_cmdrsp adapter --> smbus_regs (PeakRDL) --> hwif --> mapping --> SMBus core
//
// Follows HPET pattern exactly - uses existing peakrdl_to_cmdrsp from converters/rtl/
//
//==============================================================================
// STRICT DECODE
//==============================================================================
//   Only the fifteen mapped registers decode. Everything else in the 4 KB APB
//   window is DROPPED: no internal strobe fires, the read returns 0, and the
//   access is acknowledged locally with PSLVERR. The generated block sees only
//   six address bits, so without this every unmapped address aliases onto a
//   real register 64 bytes below it - 0x040 would write SMBUS_CONTROL.
//
//   The acknowledge is combinational and local (w_drop_ack), the same shape
//   the register block uses, because the adapter holds its request until it
//   is acked; a dropped access that is never acked hangs the bus.
//
//==============================================================================
// W1C, AND WHY IT IS DECODED HERE
//==============================================================================
//   smbus_core owns the sticky SMBUS_INT_STATUS bits; the generated field is
//   a live MIRROR of them. Software's write-1-to-clear is therefore decoded
//   HERE and forwarded as a one-cycle per-bit clear:
//
//     clear mask = regblk_wr_data & regblk_wr_biten, at the register's own
//     address, on the RISING EDGE of the request
//
//   Both halves matter. The byte enables are in the mask because a byte-
//   strobed write must not clear bits outside the bytes it wrote. The edge is
//   there because the adapter HOLDS the request for two cycles: a level would
//   clear twice, and the second clear would undo a set the core accepted in
//   between.
//
//   The decode compares the same address bits the generated block compares,
//   so the mirror cannot drift onto a different register than the one
//   software actually wrote. Nothing in the RTL cross-checks that; the guard
//   is the DV suite's W1C tests.
//
//==============================================================================
// TX FIFO PUSH
//==============================================================================
//   The push takes its byte from the WRITE DATA of the access that causes it
//   (regblk_wr_data & regblk_wr_biten), not from the stored field. The
//   adapter holds the request for two cycles and the field storage updates a
//   cycle after that, so pushing the field on the request edge enqueues the
//   PREVIOUS byte - every write shifted by one, and the last one never sent
//   (GitHub #58 item 4). One or the other, never both: the push is a
//   single-cycle edge, so back-to-back writes each push exactly once.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module smbus_config_regs
    import smbus_regs_pkg::*;
(
    input logic clk,
    input logic rst_n,  // Active-low reset

    // Command/Response Interface (from apb4_slave)
    input  logic        cmd_valid,
    output logic        cmd_ready,
    input  logic        cmd_pwrite,
    input  logic [11:0] cmd_paddr,
    input  logic [31:0] cmd_pwdata,
    input  logic [3:0]  cmd_pstrb,

    output logic        rsp_valid,
    input  logic        rsp_ready,
    output logic [31:0] rsp_prdata,
    output logic        rsp_pslverr,

    // SMBus Core Interface - Configuration Outputs
    output logic        cfg_master_en,
    output logic        cfg_slave_en,
    output logic        cfg_pec_en,
    output logic        cfg_fast_mode,
    output logic        cfg_fifo_reset,
    output logic        cfg_soft_reset,
    output logic [15:0] cfg_clk_div,
    output logic [23:0] cfg_timeout,
    output logic [6:0]  cfg_own_addr,
    output logic        cfg_own_addr_en,

    // Command interface outputs
    output logic [3:0]  cmd_trans_type,
    output logic [7:0]  cmd_code,
    output logic [6:0]  cmd_slave_addr,
    output logic        cmd_start,
    output logic        cmd_stop,
    output logic [7:0]  cmd_data_byte,
    output logic [5:0]  cmd_block_count,

    // Status inputs (from smbus_core)
    input  logic        status_busy,
    input  logic        status_bus_error,
    input  logic        status_timeout_error,
    input  logic        status_pec_error,
    input  logic        status_arb_lost,
    input  logic        status_nak_received,
    input  logic        status_slave_addressed,
    input  logic        status_complete,
    input  logic [3:0]  status_fsm_state,

    // Data byte interface: data_byte_in is a RECEIVED byte, written back into
    // SMBUS_DATA only when data_byte_we is high. What software left in
    // SMBUS_DATA leaves through cmd_data_byte with the rest of the command.
    input  logic [7:0]  data_byte_in,
    input  logic        data_byte_we,

    // Block count writeback (Block Read learns its count from the slave)
    input  logic [5:0]  block_count_in,
    input  logic        block_count_we,

    // Sticky interrupt status, owned by smbus_core
    input  logic [4:0]  int_status,
    output logic [4:0]  sw_clr_int_status,

    // TX FIFO interface
    output logic [7:0]  tx_fifo_wdata,
    output logic        tx_fifo_wr,
    input  logic [5:0]  tx_fifo_level,
    input  logic        tx_fifo_full,
    input  logic        tx_fifo_empty,

    // RX FIFO interface
    input  logic [7:0]  rx_fifo_rdata,
    output logic        rx_fifo_rd,
    input  logic [5:0]  rx_fifo_level,
    input  logic        rx_fifo_full,
    input  logic        rx_fifo_empty,

    // PEC interface
    input  logic [7:0]  pec_wr_data,
    input  logic        pec_we,

    // Interrupt enables
    output logic        int_complete_en,
    output logic        int_error_en,
    output logic        int_tx_thresh_en,
    output logic        int_rx_thresh_en,
    output logic        int_slave_addr_en
);

    //========================================================================
    // Internal Signals for PeakRDL Passthrough Interface
    //========================================================================

    logic                regblk_req;
    logic                regblk_req_is_wr;
    logic [5:0]          regblk_addr;
    logic [31:0]         regblk_wr_data;
    logic [31:0]         regblk_wr_biten;
    logic                regblk_req_stall_wr;
    logic                regblk_req_stall_rd;
    logic                regblk_rd_ack;
    logic                regblk_rd_err;
    logic [31:0]         regblk_rd_data;
    logic                regblk_wr_ack;
    logic                regblk_wr_err;

    // Adapter-side copies, so the drop path can answer without the block
    logic                adapter_req;
    logic                adapter_req_is_wr;
    logic [11:0]         adapter_addr;
    logic [31:0]         adapter_wr_data;
    logic [31:0]         adapter_wr_biten;
    logic                adapter_req_stall_wr;
    logic                adapter_req_stall_rd;
    logic                adapter_rd_ack;
    logic                adapter_rd_err;
    logic [31:0]         adapter_rd_data;
    logic                adapter_wr_ack;
    logic                adapter_wr_err;

    logic                w_addr_mapped;
    logic                w_drop;
    logic                w_drop_ack;

    logic                w_int_status_wr;
    logic                r_int_status_wr_d;
    logic                w_int_status_evt;

    logic                w_tx_fifo_write_req;
    logic                r_tx_fifo_wr_prev;

    logic                w_rx_fifo_read_req;
    logic                r_rx_fifo_rd_prev;

    // Mapped register offsets - the same six bits the generated block decodes
    localparam logic [11:0] ADDR_CONTROL     = 12'h000;
    localparam logic [11:0] ADDR_STATUS      = 12'h004;
    localparam logic [11:0] ADDR_COMMAND     = 12'h008;
    localparam logic [11:0] ADDR_SLAVE_ADDR  = 12'h00C;
    localparam logic [11:0] ADDR_DATA        = 12'h010;
    localparam logic [11:0] ADDR_TX_FIFO     = 12'h014;
    localparam logic [11:0] ADDR_RX_FIFO     = 12'h018;
    localparam logic [11:0] ADDR_FIFO_STATUS = 12'h01C;
    localparam logic [11:0] ADDR_CLK_DIV     = 12'h020;
    localparam logic [11:0] ADDR_TIMEOUT     = 12'h024;
    localparam logic [11:0] ADDR_OWN_ADDR    = 12'h028;
    localparam logic [11:0] ADDR_INT_ENABLE  = 12'h02C;
    localparam logic [11:0] ADDR_INT_STATUS  = 12'h030;
    localparam logic [11:0] ADDR_PEC         = 12'h034;
    localparam logic [11:0] ADDR_BLOCK_COUNT = 12'h038;

    //========================================================================
    // Hardware Interface Structs
    //========================================================================

    smbus_regs__in_t  hwif_in;
    smbus_regs__out_t hwif_out;

    //========================================================================
    // Instantiate Protocol Adapter (from converters/rtl/)
    //========================================================================

    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH(12),
        .DATA_WIDTH(32)
    ) u_adapter (
        .aclk               (clk),
        .aresetn            (rst_n),

        // CMD/RSP interface (external)
        .cmd_valid          (cmd_valid),
        .cmd_ready          (cmd_ready),
        .cmd_pwrite         (cmd_pwrite),
        .cmd_paddr          (cmd_paddr),
        .cmd_pwdata         (cmd_pwdata),
        .cmd_pstrb          (cmd_pstrb),

        .rsp_valid          (rsp_valid),
        .rsp_ready          (rsp_ready),
        .rsp_prdata         (rsp_prdata),
        .rsp_pslverr        (rsp_pslverr),

        // PeakRDL passthrough interface - through the strict decode below
        .regblk_req         (adapter_req),
        .regblk_req_is_wr   (adapter_req_is_wr),
        .regblk_addr        (adapter_addr),
        .regblk_wr_data     (adapter_wr_data),
        .regblk_wr_biten    (adapter_wr_biten),
        .regblk_req_stall_wr(adapter_req_stall_wr),
        .regblk_req_stall_rd(adapter_req_stall_rd),
        .regblk_rd_ack      (adapter_rd_ack),
        .regblk_rd_err      (adapter_rd_err),
        .regblk_rd_data     (adapter_rd_data),
        .regblk_wr_ack      (adapter_wr_ack),
        .regblk_wr_err      (adapter_wr_err)
    );

    //========================================================================
    // Strict Address Decode
    //========================================================================

    always_comb begin
        w_addr_mapped = (adapter_addr == ADDR_CONTROL)     ||
                        (adapter_addr == ADDR_STATUS)      ||
                        (adapter_addr == ADDR_COMMAND)     ||
                        (adapter_addr == ADDR_SLAVE_ADDR)  ||
                        (adapter_addr == ADDR_DATA)        ||
                        (adapter_addr == ADDR_TX_FIFO)     ||
                        (adapter_addr == ADDR_RX_FIFO)     ||
                        (adapter_addr == ADDR_FIFO_STATUS) ||
                        (adapter_addr == ADDR_CLK_DIV)     ||
                        (adapter_addr == ADDR_TIMEOUT)     ||
                        (adapter_addr == ADDR_OWN_ADDR)    ||
                        (adapter_addr == ADDR_INT_ENABLE)  ||
                        (adapter_addr == ADDR_INT_STATUS)  ||
                        (adapter_addr == ADDR_PEC)         ||
                        (adapter_addr == ADDR_BLOCK_COUNT);
    end

    assign w_drop     = !w_addr_mapped;
    assign w_drop_ack = adapter_req && w_drop;

    assign regblk_req        = adapter_req && !w_drop;
    assign regblk_req_is_wr  = adapter_req_is_wr;
    assign regblk_addr       = adapter_addr[5:0];
    assign regblk_wr_data    = adapter_wr_data;
    assign regblk_wr_biten   = adapter_wr_biten;

    assign adapter_req_stall_wr = regblk_req_stall_wr;
    assign adapter_req_stall_rd = regblk_req_stall_rd;
    assign adapter_rd_ack  = regblk_rd_ack | (w_drop_ack & ~adapter_req_is_wr);
    assign adapter_rd_err  = regblk_rd_err | (w_drop_ack & ~adapter_req_is_wr);
    assign adapter_rd_data = w_drop_ack ? 32'h0 : regblk_rd_data;
    assign adapter_wr_ack  = regblk_wr_ack | (w_drop_ack & adapter_req_is_wr);
    assign adapter_wr_err  = regblk_wr_err | (w_drop_ack & adapter_req_is_wr);

    //========================================================================
    // Instantiate PeakRDL-Generated Register Block
    //========================================================================

    smbus_regs u_smbus_regs (
        .clk                (clk),
        .rst                (~rst_n),  // PeakRDL uses active-high reset

        // Passthrough CPU interface
        .s_cpuif_req        (regblk_req),
        .s_cpuif_req_is_wr  (regblk_req_is_wr),
        .s_cpuif_addr       (regblk_addr),  // strict decode above guarantees no alias
        .s_cpuif_wr_data    (regblk_wr_data),
        .s_cpuif_wr_biten   (regblk_wr_biten),
        .s_cpuif_req_stall_wr(regblk_req_stall_wr),
        .s_cpuif_req_stall_rd(regblk_req_stall_rd),
        .s_cpuif_rd_ack     (regblk_rd_ack),
        .s_cpuif_rd_err     (regblk_rd_err),
        .s_cpuif_rd_data    (regblk_rd_data),
        .s_cpuif_wr_ack     (regblk_wr_ack),
        .s_cpuif_wr_err     (regblk_wr_err),

        // Hardware interface
        .hwif_in            (hwif_in),
        .hwif_out           (hwif_out)
    );

    //========================================================================
    // Map PeakRDL hwif Outputs to SMBus Core Configuration Inputs
    //========================================================================

    // Control register
    assign cfg_master_en  = hwif_out.SMBUS_CONTROL.master_en.value;
    assign cfg_slave_en   = hwif_out.SMBUS_CONTROL.slave_en.value;
    assign cfg_pec_en     = hwif_out.SMBUS_CONTROL.pec_en.value;
    assign cfg_fast_mode  = hwif_out.SMBUS_CONTROL.fast_mode.value;
    assign cfg_fifo_reset = hwif_out.SMBUS_CONTROL.fifo_reset.value;
    assign cfg_soft_reset = hwif_out.SMBUS_CONTROL.soft_reset.value;

    // Clock and timeout
    assign cfg_clk_div    = hwif_out.SMBUS_CLK_DIV.clk_div.value;
    assign cfg_timeout    = hwif_out.SMBUS_TIMEOUT.timeout.value;

    // Slave address
    assign cfg_own_addr     = hwif_out.SMBUS_OWN_ADDR.own_addr.value;
    assign cfg_own_addr_en  = hwif_out.SMBUS_OWN_ADDR.addr_en.value;

    // Command interface
    assign cmd_trans_type  = hwif_out.SMBUS_COMMAND.trans_type.value;
    assign cmd_code        = hwif_out.SMBUS_COMMAND.cmd_code.value;
    assign cmd_start       = hwif_out.SMBUS_COMMAND.start.value;
    assign cmd_stop        = hwif_out.SMBUS_COMMAND.stop.value;
    assign cmd_slave_addr  = hwif_out.SMBUS_SLAVE_ADDR.slave_addr.value;
    assign cmd_data_byte   = hwif_out.SMBUS_DATA.data.value;
    assign cmd_block_count = hwif_out.SMBUS_BLOCK_COUNT.block_count.value;

    // Interrupt enables
    assign int_complete_en   = hwif_out.SMBUS_INT_ENABLE.complete_en.value;
    assign int_error_en      = hwif_out.SMBUS_INT_ENABLE.error_en.value;
    assign int_tx_thresh_en  = hwif_out.SMBUS_INT_ENABLE.tx_thresh_en.value;
    assign int_rx_thresh_en  = hwif_out.SMBUS_INT_ENABLE.rx_thresh_en.value;
    assign int_slave_addr_en = hwif_out.SMBUS_INT_ENABLE.slave_addr_en.value;

    //========================================================================
    // FIFO port strobes and the W1C decode
    //========================================================================
    // All three are the same shape: decode the register's own address on the
    // held request, and take the RISING EDGE so a two-cycle request produces
    // exactly one push, one pop, one clear.

    // The BYTE ENABLE is part of the decode, not just of the data. A write to
    // SMBUS_TX_FIFO with the data lane disabled (PSTRB=4'b0010, say) is not a
    // FIFO push at all; masking the data but pushing anyway enqueued 0x00.
    assign w_tx_fifo_write_req = regblk_req && regblk_req_is_wr &&
                                 (adapter_addr == ADDR_TX_FIFO) &&
                                 adapter_wr_biten[0];
    assign w_rx_fifo_read_req  = regblk_req && !regblk_req_is_wr &&
                                 (adapter_addr == ADDR_RX_FIFO);
    assign w_int_status_wr     = regblk_req && regblk_req_is_wr &&
                                 (adapter_addr == ADDR_INT_STATUS);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_tx_fifo_wr_prev <= 1'b0;
            r_rx_fifo_rd_prev <= 1'b0;
            r_int_status_wr_d <= 1'b0;
        end else begin
            r_tx_fifo_wr_prev <= w_tx_fifo_write_req;
            r_rx_fifo_rd_prev <= w_rx_fifo_read_req;
            r_int_status_wr_d <= w_int_status_wr;
        end
    )

    assign tx_fifo_wr  = w_tx_fifo_write_req && !r_tx_fifo_wr_prev;
    assign rx_fifo_rd  = w_rx_fifo_read_req  && !r_rx_fifo_rd_prev;

    // THE BYTE WRITTEN BY THIS ACCESS, not the stored field: the field
    // storage is a cycle behind the request, so the field still holds the
    // PREVIOUS byte when the push fires.
    assign tx_fifo_wdata = adapter_wr_data[7:0] & adapter_wr_biten[7:0];

    assign w_int_status_evt  = w_int_status_wr && !r_int_status_wr_d;
    assign sw_clr_int_status = w_int_status_evt ?
                               (adapter_wr_data[4:0] & adapter_wr_biten[4:0]) : 5'h00;

    //========================================================================
    // Map SMBus Core Outputs to PeakRDL hwif Inputs
    //========================================================================

    // Status register inputs (hardware writes)
    assign hwif_in.SMBUS_STATUS.busy.next = status_busy;
    assign hwif_in.SMBUS_STATUS.bus_error.next = status_bus_error;
    assign hwif_in.SMBUS_STATUS.timeout_error.next = status_timeout_error;
    assign hwif_in.SMBUS_STATUS.pec_error.next = status_pec_error;
    assign hwif_in.SMBUS_STATUS.arb_lost.next = status_arb_lost;
    assign hwif_in.SMBUS_STATUS.nak_received.next = status_nak_received;
    assign hwif_in.SMBUS_STATUS.slave_addressed.next = status_slave_addressed;
    assign hwif_in.SMBUS_STATUS.complete.next = status_complete;
    assign hwif_in.SMBUS_STATUS.fsm_state.next = status_fsm_state;

    // RX FIFO data (hardware writes)
    assign hwif_in.SMBUS_RX_FIFO.rx_data.next = rx_fifo_rdata;

    // FIFO status (hardware writes)
    assign hwif_in.SMBUS_FIFO_STATUS.tx_level.next = tx_fifo_level;
    assign hwif_in.SMBUS_FIFO_STATUS.tx_full.next = tx_fifo_full;
    assign hwif_in.SMBUS_FIFO_STATUS.tx_empty.next = tx_fifo_empty;
    assign hwif_in.SMBUS_FIFO_STATUS.rx_level.next = rx_fifo_level;
    assign hwif_in.SMBUS_FIFO_STATUS.rx_full.next = rx_fifo_full;
    assign hwif_in.SMBUS_FIFO_STATUS.rx_empty.next = rx_fifo_empty;

    // Hardware writes, each QUALIFIED. Without the we the generated hardware
    // path overwrites the field every clock and no software write survives.
    assign hwif_in.SMBUS_PEC.pec.next = pec_wr_data;
    assign hwif_in.SMBUS_PEC.pec.we   = pec_we;

    assign hwif_in.SMBUS_DATA.data.next = data_byte_in;
    assign hwif_in.SMBUS_DATA.data.we   = data_byte_we;

    assign hwif_in.SMBUS_BLOCK_COUNT.block_count.next = block_count_in;
    assign hwif_in.SMBUS_BLOCK_COUNT.block_count.we   = block_count_we;

    //========================================================================
    // Interrupt status: the field is a LIVE MIRROR of smbus_core's sticky bit
    //========================================================================
    // The stickiness lives in hardware (smbus_int_status.sv) and the W1C is
    // decoded above. Feeding an edge PULSE into a woclr field - what this used
    // to do - relies on the field itself to latch, and then the level bits
    // (which were fed the live FIFO flags) re-assert on the clock after
    // software clears them.

    assign hwif_in.SMBUS_INT_STATUS.complete_int.next   = int_status[0];
    assign hwif_in.SMBUS_INT_STATUS.error_int.next      = int_status[1];
    assign hwif_in.SMBUS_INT_STATUS.tx_thresh_int.next  = int_status[2];
    assign hwif_in.SMBUS_INT_STATUS.rx_thresh_int.next  = int_status[3];
    assign hwif_in.SMBUS_INT_STATUS.slave_addr_int.next = int_status[4];

    //========================================================================
    // Self-clearing strobes (fifo_reset, soft_reset, start, stop)
    //========================================================================
    // Each reads back 0: they are commands, not state.

    assign hwif_in.SMBUS_CONTROL.fifo_reset.next = 1'b0;
    assign hwif_in.SMBUS_CONTROL.soft_reset.next = 1'b0;
    assign hwif_in.SMBUS_COMMAND.start.next = 1'b0;
    assign hwif_in.SMBUS_COMMAND.stop.next = 1'b0;

endmodule

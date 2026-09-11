// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb4_smbus
// Purpose: APB wrapper for SMBus 2.0 Controller
//
// Top-level integration module providing:
// - APB4 slave interface
// - SMBus 2.0 protocol, MASTER MODE. Slave mode is a stub: the register
//   surface exists but no slave FSM runs and this block never answers as a
//   target. ARA, Host Notify and SMBALERT# are not implemented (RLB-011).
// - All standard transaction types (Quick, Byte, Word, Block)
// - Packet Error Checking (PEC) with CRC-8
// - TX/RX FIFOs, FIFO_DEPTH bytes each (parameter, 2..63; 32 by default)
// - Bus timeout, SMBUS_TIMEOUT core clocks (~25 ms default); worst case
//   from 'SCL wedges' to busy=0 is five times that
// - Configurable clock: 100 kHz standard, 390.6 kHz fast, same divider
// - Interrupt generation (complete, error, FIFO thresholds, slave addressed)
//
// RESETS MUST ARRIVE ALREADY SYNCHRONIZED. presetn and smbus_resetn are
// asserted asynchronously and must be DE-asserted synchronously to their own
// clock by the integrator: this block instantiates no reset synchronizer, and
// rst_n feeds a flop whose output lands on an asynchronous reset net inside
// simple_fifo. Every other RLB block assumes the same.
//
// Follows 3-layer architecture:
//   Layer 1: apb4_smbus (this module) - APB interface
//   Layer 2: smbus_config_regs - Register wrapper with status feedback
//   Layer 3: smbus_core - SMBus protocol implementation
//
// Register Map (32-bit aligned):
//   0x000: SMBUS_CONTROL     - Global control (enable, mode, PEC)
//   0x004: SMBUS_STATUS      - Status flags (busy, errors, state)
//   0x008: SMBUS_COMMAND     - Transaction command and trigger
//   0x00C: SMBUS_SLAVE_ADDR  - Target slave address
//   0x010: SMBUS_DATA        - Single byte data register
//   0x014: SMBUS_TX_FIFO     - Transmit FIFO write port
//   0x018: SMBUS_RX_FIFO     - Receive FIFO read port
//   0x01C: SMBUS_FIFO_STATUS - FIFO levels and flags
//   0x020: SMBUS_CLK_DIV     - Clock divider configuration
//   0x024: SMBUS_TIMEOUT     - Timeout threshold
//   0x028: SMBUS_OWN_ADDR    - Own slave address (slave mode)
//   0x02C: SMBUS_INT_ENABLE  - Interrupt enable mask
//   0x030: SMBUS_INT_STATUS  - Interrupt status (W1C)
//   0x034: SMBUS_PEC         - PEC value register
//   0x038: SMBUS_BLOCK_COUNT - Block transfer count

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb4_smbus #(
    parameter int FIFO_DEPTH = 32,  // TX/RX FIFO depth (32 bytes per SMBus 2.0)
    // 0 = one clock domain (apb4_slave), 1 = pclk and smbus_clk are
    // independent (apb4_slave_cdc). Only 0 and 1 are legal - see param_check.
    parameter int CDC_ENABLE = 0,
    // Async-FIFO pointer encoding, forwarded to the CDC block: 0 = Gray
    // (power-of-2 depth only), 1 = Johnson (any depth, DEPTH-bit pointers).
    // Gray by default -- Johnson is opt-in.
    parameter int USE_JOHNSON = 0
) (
    //========================================================================
    // Clock and Reset
    //========================================================================
    input  wire                    pclk,           // APB clock
    input  wire                    presetn,        // APB reset (active low)
    input  wire                    smbus_clk,      // SMBus clock (same as pclk when CDC_ENABLE=0)
    // SMBus reset (same as presetn when CDC_ENABLE=0)
    input  wire                    smbus_resetn,

    //========================================================================
    // APB4 Slave Interface
    //========================================================================
    input  wire                    s_apb_PSEL,
    input  wire                    s_apb_PENABLE,
    output wire                    s_apb_PREADY,
    input  wire [11:0]             s_apb_PADDR,    // Fixed 12-bit addressing
    input  wire                    s_apb_PWRITE,
    input  wire [31:0]             s_apb_PWDATA,
    input  wire [3:0]              s_apb_PSTRB,
    input  wire [2:0]              s_apb_PPROT,
    output wire [31:0]             s_apb_PRDATA,
    output wire                    s_apb_PSLVERR,

    //========================================================================
    // SMBus Physical Interface
    //========================================================================
    input  wire                    smb_scl_i,      // SCL input
    output wire                    smb_scl_o,      // SCL output
    output wire                    smb_scl_t,      // SCL tristate enable (1=input)
    input  wire                    smb_sda_i,      // SDA input
    output wire                    smb_sda_o,      // SDA output
    output wire                    smb_sda_t,      // SDA tristate enable (1=input)

    //========================================================================
    // Interrupt Output
    //========================================================================
    output wire                    smb_interrupt   // Aggregated interrupt
);

    // ONE decode of CDC_ENABLE, used everywhere. It used to be tested as
    // `!= 0` in one place and `[0]` in two others; those disagree for any
    // value with bit 0 clear, which would have built the CDC APB slave and
    // then clocked the core from pclk.
    localparam logic CDC_SEL = (CDC_ENABLE != 0);

    // Elaboration-time guards. FIFO_DEPTH is carried in six-bit level and
    // count fields, so 63 is the ceiling; the floor is 2 because fifo_sync
    // addresses with $clog2(DEPTH), and $clog2(1) is 0 - a depth of 1 does
    // not elaborate at all.
    initial begin : param_check
        if (CDC_ENABLE != 0 && CDC_ENABLE != 1) begin
            $fatal(1, "apb4_smbus: CDC_ENABLE must be 0 or 1, got %0d", CDC_ENABLE);
        end
        if (FIFO_DEPTH < 2 || FIFO_DEPTH > 63) begin
            $fatal(1, "apb4_smbus: FIFO_DEPTH must be 2..63, got %0d", FIFO_DEPTH);
        end
    end

    //========================================================================
    // CMD/RSP Interface Signals
    //========================================================================

    logic        w_cmd_valid;
    logic        w_cmd_ready;
    logic        w_cmd_pwrite;
    logic [11:0] w_cmd_paddr;
    logic [31:0] w_cmd_pwdata;
    logic [3:0]  w_cmd_pstrb;

    logic        w_rsp_valid;
    logic        w_rsp_ready;
    logic [31:0] w_rsp_prdata;
    logic        w_rsp_pslverr;

    //========================================================================
    // APB Slave - CDC or Non-CDC based on parameter (Following HPET pattern)
    //========================================================================
    generate
        if (CDC_SEL) begin : g_apb4_slave_cdc
            // Clock Domain Crossing version for async clocks
            apb4_slave_cdc #(
                .ADDR_WIDTH(12),
                .DATA_WIDTH(32),
                .STRB_WIDTH(4),
                .PROT_WIDTH(3),
                .DEPTH(2),
                .USE_JOHNSON (USE_JOHNSON)
            ) u_apb4_slave_cdc (
                // APB Clock Domain
                .pclk                 (pclk),
                .presetn              (presetn),

                // SMBus Clock Domain
                .aclk                 (smbus_clk),
                .aresetn              (smbus_resetn),

                // APB Interface (pclk domain)
                .s_apb_PSEL           (s_apb_PSEL),
                .s_apb_PENABLE        (s_apb_PENABLE),
                .s_apb_PREADY         (s_apb_PREADY),
                .s_apb_PADDR          (s_apb_PADDR),
                .s_apb_PWRITE         (s_apb_PWRITE),
                .s_apb_PWDATA         (s_apb_PWDATA),
                .s_apb_PSTRB          (s_apb_PSTRB),
                .s_apb_PPROT          (s_apb_PPROT),
                .s_apb_PRDATA         (s_apb_PRDATA),
                .s_apb_PSLVERR        (s_apb_PSLVERR),

                // Command Interface (smbus_clk domain)
                .cmd_valid            (w_cmd_valid),
                .cmd_ready            (w_cmd_ready),
                .cmd_pwrite           (w_cmd_pwrite),
                .cmd_paddr            (w_cmd_paddr),
                .cmd_pwdata           (w_cmd_pwdata),
                .cmd_pstrb            (w_cmd_pstrb),
                .cmd_pprot            (),

                // Response Interface (smbus_clk domain)
                .rsp_valid            (w_rsp_valid),
                .rsp_ready            (w_rsp_ready),
                .rsp_prdata           (w_rsp_prdata),
                .rsp_pslverr          (w_rsp_pslverr)
            );
        end else begin : g_apb4_slave_no_cdc
            // Non-CDC version for same clock domain (pclk == smbus_clk)
            apb4_slave #(
                .ADDR_WIDTH(12),
                .DATA_WIDTH(32),
                .STRB_WIDTH(4),
                .PROT_WIDTH(3)
            ) u_apb4_slave (
                // Single clock domain (use pclk for both APB and cmd/rsp)
                .pclk                 (pclk),
                .presetn              (presetn),

                // APB Interface
                .s_apb_PSEL           (s_apb_PSEL),
                .s_apb_PENABLE        (s_apb_PENABLE),
                .s_apb_PREADY         (s_apb_PREADY),
                .s_apb_PADDR          (s_apb_PADDR),
                .s_apb_PWRITE         (s_apb_PWRITE),
                .s_apb_PWDATA         (s_apb_PWDATA),
                .s_apb_PSTRB          (s_apb_PSTRB),
                .s_apb_PPROT          (s_apb_PPROT),
                .s_apb_PRDATA         (s_apb_PRDATA),
                .s_apb_PSLVERR        (s_apb_PSLVERR),

                // Command Interface (same pclk domain)
                .cmd_valid            (w_cmd_valid),
                .cmd_ready            (w_cmd_ready),
                .cmd_pwrite           (w_cmd_pwrite),
                .cmd_paddr            (w_cmd_paddr),
                .cmd_pwdata           (w_cmd_pwdata),
                .cmd_pstrb            (w_cmd_pstrb),
                .cmd_pprot            (),  // Unused

                // Response Interface (same pclk domain)
                .rsp_valid            (w_rsp_valid),
                .rsp_ready            (w_rsp_ready),
                .rsp_prdata           (w_rsp_prdata),
                .rsp_pslverr          (w_rsp_pslverr)
            );
        end
    endgenerate

    //========================================================================
    // Configuration Register Interface Signals
    //========================================================================

    // Configuration outputs
    wire        w_cfg_master_en;
    wire        w_cfg_slave_en;
    wire        w_cfg_pec_en;
    wire        w_cfg_fast_mode;
    wire        w_cfg_fifo_reset;
    wire [15:0] w_cfg_clk_div;
    wire [23:0] w_cfg_timeout;
    wire [6:0]  w_cfg_own_addr;
    wire        w_cfg_own_addr_en;
    wire        w_cfg_slave_gc_en;
    wire        w_cfg_slave_nack_all;
    wire        w_cfg_slave_pec_en;
    wire        w_cfg_slave_stretch_en;

    // Command interface
    wire [3:0]  w_cmd_trans_type;
    wire [7:0]  w_cmd_code;
    wire [6:0]  w_cmd_slave_addr;
    wire        w_cmd_start;
    wire        w_cmd_stop;
    wire [7:0]  w_cmd_data_byte;
    wire [5:0]  w_cmd_block_count;

    // Status inputs
    wire        w_status_busy;
    wire        w_status_bus_error;
    wire        w_status_timeout_error;
    wire        w_status_pec_error;
    wire        w_status_arb_lost;
    wire        w_status_nak_received;
    wire        w_status_slave_addressed;
    wire        w_status_slave_rd_not_wr;
    wire        w_status_slave_stretching;
    wire        w_status_slave_pec_error;
    wire [7:0]  w_status_slave_pec_value;
    wire        w_status_complete;
    wire [3:0]  w_status_fsm_state;

    // Data byte interface
    wire [7:0]  w_data_byte_in;

    // TX FIFO interface
    wire [7:0]  w_tx_fifo_wdata;
    wire        w_tx_fifo_wr;
    wire [5:0]  w_tx_fifo_level;
    wire        w_tx_fifo_full;
    wire        w_tx_fifo_empty;

    // RX FIFO interface
    wire [7:0]  w_rx_fifo_rdata;
    wire        w_rx_fifo_rd;
    wire [5:0]  w_rx_fifo_level;
    wire        w_rx_fifo_full;
    wire        w_rx_fifo_empty;

    // PEC interface
    wire [7:0]  w_pec_wr_data;
    wire        w_pec_we;
    wire        w_cfg_soft_reset;
    wire        w_data_byte_we;
    wire [5:0]  w_block_count_in;
    wire        w_block_count_we;
    wire [7:0]  w_int_status;
    wire [7:0]  w_sw_clr_int_status;
    wire [7:0]  w_int_enable;
    wire        w_int_pending_src;
    wire        w_int_pending_pclk;
    logic       r_interrupt;

    // Interrupt enables
    wire        w_int_complete_en;
    wire        w_int_error_en;
    wire        w_int_tx_thresh_en;
    wire        w_int_rx_thresh_en;
    wire        w_int_slave_addr_en;
    wire        w_int_slave_rx_en;
    wire        w_int_slave_tx_en;
    wire        w_int_slave_done_en;

    //========================================================================
    // Configuration Registers Module
    // CDC_ENABLE=0: Uses pclk (same clock as APB)
    // CDC_ENABLE=1: Uses smbus_clk (async clock)
    //========================================================================

    smbus_config_regs u_config_regs (
        .clk                   (CDC_SEL ? smbus_clk : pclk),
        .rst_n                 (CDC_SEL ? smbus_resetn : presetn),

        // CMD/RSP interface
        .cmd_valid             (w_cmd_valid),
        .cmd_ready             (w_cmd_ready),
        .cmd_pwrite            (w_cmd_pwrite),
        .cmd_paddr             (w_cmd_paddr),
        .cmd_pwdata            (w_cmd_pwdata),
        .cmd_pstrb             (w_cmd_pstrb),

        .rsp_valid             (w_rsp_valid),
        .rsp_ready             (w_rsp_ready),
        .rsp_prdata            (w_rsp_prdata),
        .rsp_pslverr           (w_rsp_pslverr),

        // Configuration outputs
        .cfg_master_en         (w_cfg_master_en),
        .cfg_slave_en          (w_cfg_slave_en),
        .cfg_pec_en            (w_cfg_pec_en),
        .cfg_fast_mode         (w_cfg_fast_mode),
        .cfg_fifo_reset        (w_cfg_fifo_reset),
        .cfg_soft_reset        (w_cfg_soft_reset),
        .cfg_clk_div           (w_cfg_clk_div),
        .cfg_timeout           (w_cfg_timeout),
        .cfg_own_addr          (w_cfg_own_addr),
        .cfg_own_addr_en       (w_cfg_own_addr_en),
        .cfg_slave_gc_en       (w_cfg_slave_gc_en),
        .cfg_slave_nack_all    (w_cfg_slave_nack_all),
        .cfg_slave_pec_en      (w_cfg_slave_pec_en),
        .cfg_slave_stretch_en  (w_cfg_slave_stretch_en),

        // Command interface
        .cmd_trans_type        (w_cmd_trans_type),
        .cmd_code              (w_cmd_code),
        .cmd_slave_addr        (w_cmd_slave_addr),
        .cmd_start             (w_cmd_start),
        .cmd_stop              (w_cmd_stop),
        .cmd_data_byte         (w_cmd_data_byte),
        .cmd_block_count       (w_cmd_block_count),

        // Status inputs
        .status_busy           (w_status_busy),
        .status_bus_error      (w_status_bus_error),
        .status_timeout_error  (w_status_timeout_error),
        .status_pec_error      (w_status_pec_error),
        .status_arb_lost       (w_status_arb_lost),
        .status_nak_received   (w_status_nak_received),
        .status_slave_addressed(w_status_slave_addressed),
        .status_slave_rd_not_wr(w_status_slave_rd_not_wr),
        .status_slave_stretching(w_status_slave_stretching),
        .status_slave_pec_error(w_status_slave_pec_error),
        .status_slave_pec_value(w_status_slave_pec_value),
        .status_complete       (w_status_complete),
        .status_fsm_state      (w_status_fsm_state),

        // Data byte interface
        .data_byte_in          (w_data_byte_in),
        .data_byte_we          (w_data_byte_we),
        .block_count_in        (w_block_count_in),
        .block_count_we        (w_block_count_we),

        // TX FIFO interface
        .tx_fifo_wdata         (w_tx_fifo_wdata),
        .tx_fifo_wr            (w_tx_fifo_wr),
        .tx_fifo_level         (w_tx_fifo_level),
        .tx_fifo_full          (w_tx_fifo_full),
        .tx_fifo_empty         (w_tx_fifo_empty),

        // RX FIFO interface
        .rx_fifo_rdata         (w_rx_fifo_rdata),
        .rx_fifo_rd            (w_rx_fifo_rd),
        .rx_fifo_level         (w_rx_fifo_level),
        .rx_fifo_full          (w_rx_fifo_full),
        .rx_fifo_empty         (w_rx_fifo_empty),

        // PEC interface
        .pec_wr_data           (w_pec_wr_data),
        .pec_we                (w_pec_we),

        // Interrupt enables
        .int_complete_en       (w_int_complete_en),
        .int_error_en          (w_int_error_en),
        .int_tx_thresh_en      (w_int_tx_thresh_en),
        .int_rx_thresh_en      (w_int_rx_thresh_en),
        .int_slave_addr_en     (w_int_slave_addr_en),
        .int_slave_rx_en       (w_int_slave_rx_en),
        .int_slave_tx_en       (w_int_slave_tx_en),
        .int_slave_done_en     (w_int_slave_done_en),

        // Sticky interrupt status lives in smbus_core; the field mirrors it
        .int_status            (w_int_status),
        .sw_clr_int_status     (w_sw_clr_int_status)
    );

    //========================================================================
    // SMBus Core (Protocol Engine)
    // CDC_ENABLE=0: Uses pclk (same clock as APB)
    // CDC_ENABLE=1: Uses smbus_clk (async clock)
    //========================================================================

    smbus_core #(
        .FIFO_DEPTH(FIFO_DEPTH)
    ) u_smbus_core (
        .clk                   (CDC_SEL ? smbus_clk : pclk),
        .rst_n                 (CDC_SEL ? smbus_resetn : presetn),

        // SMBus Physical Interface
        .smb_scl_i             (smb_scl_i),
        .smb_scl_o             (smb_scl_o),
        .smb_scl_t             (smb_scl_t),
        .smb_sda_i             (smb_sda_i),
        .smb_sda_o             (smb_sda_o),
        .smb_sda_t             (smb_sda_t),

        // Configuration from registers
        .cfg_master_en         (w_cfg_master_en),
        .cfg_slave_en          (w_cfg_slave_en),
        .cfg_pec_en            (w_cfg_pec_en),
        .cfg_fast_mode         (w_cfg_fast_mode),
        .cfg_fifo_reset        (w_cfg_fifo_reset),
        .cfg_soft_reset        (w_cfg_soft_reset),
        .cfg_clk_div           (w_cfg_clk_div),
        .cfg_timeout           (w_cfg_timeout),
        .cfg_own_addr          (w_cfg_own_addr),
        .cfg_own_addr_en       (w_cfg_own_addr_en),
        .cfg_slave_gc_en       (w_cfg_slave_gc_en),
        .cfg_slave_nack_all    (w_cfg_slave_nack_all),
        .cfg_slave_pec_en      (w_cfg_slave_pec_en),
        .cfg_slave_stretch_en  (w_cfg_slave_stretch_en),

        // Command interface
        .cmd_trans_type        (w_cmd_trans_type),
        .cmd_code              (w_cmd_code),
        .cmd_slave_addr        (w_cmd_slave_addr),
        .cmd_start             (w_cmd_start),
        .cmd_stop              (w_cmd_stop),
        .cmd_data_byte         (w_cmd_data_byte),
        .cmd_block_count       (w_cmd_block_count),

        // Status outputs
        .status_busy           (w_status_busy),
        .status_bus_error      (w_status_bus_error),
        .status_timeout_error  (w_status_timeout_error),
        .status_pec_error      (w_status_pec_error),
        .status_arb_lost       (w_status_arb_lost),
        .status_nak_received   (w_status_nak_received),
        .status_slave_addressed(w_status_slave_addressed),
        .status_slave_rd_not_wr(w_status_slave_rd_not_wr),
        .status_slave_stretching(w_status_slave_stretching),
        .status_slave_pec_error(w_status_slave_pec_error),
        .status_slave_pec_value(w_status_slave_pec_value),
        .status_complete       (w_status_complete),
        .status_fsm_state      (w_status_fsm_state),

        // Data byte interface
        .data_byte_out         (w_data_byte_in),
        .data_byte_we          (w_data_byte_we),
        // Block count writeback
        .block_count_out       (w_block_count_in),
        .block_count_we        (w_block_count_we),

        // Sticky interrupt status
        .int_status            (w_int_status),
        .sw_clr_int_status     (w_sw_clr_int_status),

        // TX FIFO interface
        .tx_fifo_wdata         (w_tx_fifo_wdata),
        .tx_fifo_wr            (w_tx_fifo_wr),
        .tx_fifo_level         (w_tx_fifo_level),
        .tx_fifo_full          (w_tx_fifo_full),
        .tx_fifo_empty         (w_tx_fifo_empty),

        // RX FIFO interface
        .rx_fifo_rdata         (w_rx_fifo_rdata),
        .rx_fifo_rd            (w_rx_fifo_rd),
        .rx_fifo_level         (w_rx_fifo_level),
        .rx_fifo_full          (w_rx_fifo_full),
        .rx_fifo_empty         (w_rx_fifo_empty),

        // PEC interface
        .pec_wr_data           (w_pec_wr_data),
        .pec_we                (w_pec_we)
    );

    //========================================================================
    // Interrupt Aggregation
    //========================================================================
    // THE PIN IS (SMBUS_INT_STATUS & SMBUS_INT_ENABLE) != 0, REGISTERED.
    // Not the live status: building it from the raw status wires - what this
    // used to do - means a software W1C on SMBUS_INT_STATUS has no effect on
    // the pin at all, and the only thing that can deassert it is the
    // underlying condition going away by itself. With a level-sensitive
    // interrupt controller upstream, that is an interrupt storm.
    //
    // Both operands come from the register/core domain. With CDC_ENABLE=1
    // that is smbus_clk and the pin is in pclk, so the masked vector - a
    // LEVEL, and quasi-static between events - crosses through the house
    // level synchronizer (cdc.md: sync_pulse for events,
    // glitch_free_n_dff_arn for levels; never a hand-rolled pair of flops).
    // Its destination side takes presetn, the reset of the domain it lands
    // in: the source is sticky and re-presents itself after any reset on
    // either side, so no event can be manufactured or lost by the crossing.

    assign w_int_enable = {w_int_slave_done_en, w_int_slave_tx_en,
                           w_int_slave_rx_en, w_int_slave_addr_en,
                           w_int_rx_thresh_en, w_int_tx_thresh_en,
                           w_int_error_en, w_int_complete_en};

    assign w_int_pending_src = |(w_int_status & w_int_enable);

    generate
        if (CDC_SEL) begin : g_int_cdc
            glitch_free_n_dff_arn #(
                .FLOP_COUNT (3),
                .WIDTH      (1)
            ) u_int_sync (
                .clk   (pclk),
                .rst_n (presetn),
                .d     (w_int_pending_src),
                .q     (w_int_pending_pclk)
            );
        end else begin : g_int_same_clock
            assign w_int_pending_pclk = w_int_pending_src;
        end
    endgenerate

    `ALWAYS_FF_RST(pclk, presetn,
        if (`RST_ASSERTED(presetn)) begin
            r_interrupt <= 1'b0;
        end else begin
            r_interrupt <= w_int_pending_pclk;
        end
    )

    assign smb_interrupt = r_interrupt;

endmodule

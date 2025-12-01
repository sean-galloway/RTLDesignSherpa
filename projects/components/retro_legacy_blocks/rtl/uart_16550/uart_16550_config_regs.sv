// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: uart_16550_config_regs
// Purpose: UART 16550 Configuration Registers - Connects PeakRDL to Core
//
// Description:
//   Wrapper connecting PeakRDL-generated registers to UART core.
//   Handles the hwif (hardware interface) signal mapping.
//
// Architecture:
//   APB -> apb_slave -> CMD/RSP -> peakrdl_to_cmdrsp -> regblk_* -> uart_16550_regs (PeakRDL) -> hwif -> uart_16550_core
//
// Documentation: projects/components/retro_legacy_blocks/rtl/uart_16550/README.md
// Created: 2025-11-29
// Updated: 2025-11-30 - Changed to 32-bit data width

`timescale 1ns / 1ps

`include "reset_defs.svh"

module uart_16550_config_regs
    import uart_16550_regs_pkg::*;
#(
    parameter int FIFO_DEPTH = 16,
    parameter int SYNC_STAGES = 2,
    parameter int ADDR_WIDTH = 12,
    parameter int DATA_WIDTH = 32
) (
    // Clock and Reset
    input  logic                    clk,
    input  logic                    rst_n,

    // PeakRDL regblock interface (from peakrdl_to_cmdrsp)
    input  logic                    regblk_req,
    input  logic                    regblk_req_is_wr,
    input  logic [ADDR_WIDTH-1:0]   regblk_addr,
    input  logic [DATA_WIDTH-1:0]   regblk_wr_data,
    input  logic [DATA_WIDTH-1:0]   regblk_wr_biten,
    output logic                    regblk_req_stall_wr,
    output logic                    regblk_req_stall_rd,
    output logic                    regblk_rd_ack,
    output logic                    regblk_rd_err,
    output logic [DATA_WIDTH-1:0]   regblk_rd_data,
    output logic                    regblk_wr_ack,
    output logic                    regblk_wr_err,

    // Serial Interface
    input  logic        uart_rx,
    output logic        uart_tx,

    // Modem Control Inputs (directly from pins, active low)
    input  logic        cts_n,
    input  logic        dsr_n,
    input  logic        ri_n,
    input  logic        dcd_n,

    // Modem Control Outputs
    output logic        dtr_n,
    output logic        rts_n,
    output logic        out1_n,
    output logic        out2_n,

    // Interrupt
    output logic        irq
);

    // PeakRDL hardware interface signals
    uart_16550_regs_pkg::uart_16550_regs__in_t  hwif_in;
    uart_16550_regs_pkg::uart_16550_regs__out_t hwif_out;

    // Internal signals
    logic [7:0]  w_rx_data;
    logic        w_tx_write;
    logic        w_rx_read;

    // TX write detection (edge on tx_data register write)
    logic [7:0]  r_tx_data_prev;
    logic        r_cmd_we_prev;

    // Status signals from core
    logic        w_sts_data_ready;
    logic        w_sts_overrun_error;
    logic        w_sts_parity_error;
    logic        w_sts_framing_error;
    logic        w_sts_break_interrupt;
    logic        w_sts_tx_holding_empty;
    logic        w_sts_tx_empty;
    logic        w_sts_rx_fifo_error;
    logic        w_sts_delta_cts;
    logic        w_sts_delta_dsr;
    logic        w_sts_trailing_ri;
    logic        w_sts_delta_dcd;
    logic        w_sts_cts;
    logic        w_sts_dsr;
    logic        w_sts_ri;
    logic        w_sts_dcd;
    logic [1:0]  w_sts_fifo_status;
    logic        w_int_not_pending;
    logic [1:0]  w_int_id;
    logic        w_int_timeout;

    // ========================================================================
    // PeakRDL Register Block
    // ========================================================================
    uart_16550_regs u_uart_regs (
        .clk        (clk),
        .rst        (~rst_n),

        // PeakRDL cpuif interface (from peakrdl_to_cmdrsp)
        .s_cpuif_req            (regblk_req),
        .s_cpuif_req_is_wr      (regblk_req_is_wr),
        .s_cpuif_addr           (regblk_addr[5:0]),  // 6-bit address (44 bytes)
        .s_cpuif_wr_data        (regblk_wr_data),
        .s_cpuif_wr_biten       (regblk_wr_biten),
        .s_cpuif_req_stall_wr   (regblk_req_stall_wr),
        .s_cpuif_req_stall_rd   (regblk_req_stall_rd),
        .s_cpuif_rd_ack         (regblk_rd_ack),
        .s_cpuif_rd_err         (regblk_rd_err),
        .s_cpuif_rd_data        (regblk_rd_data),
        .s_cpuif_wr_ack         (regblk_wr_ack),
        .s_cpuif_wr_err         (regblk_wr_err),

        // Hardware interface
        .hwif_in    (hwif_in),
        .hwif_out   (hwif_out)
    );

    // ========================================================================
    // TX Write Edge Detection and RX Read Edge Detection
    // ========================================================================
    // Track if we're doing a UART_DATA register read or write
    logic w_uart_data_read;
    logic w_uart_data_write;
    assign w_uart_data_read = regblk_req && !regblk_req_is_wr && (regblk_addr[5:0] == 6'h00);
    assign w_uart_data_write = regblk_req && regblk_req_is_wr && (regblk_addr[5:0] == 6'h00);

    // One-shot for TX write: generate single pulse per write transaction
    // CRITICAL: PeakRDL registers update one cycle AFTER the cpuif write request.
    // So we must delay the tx_write pulse by one cycle to align with valid tx_data.
    //
    // Strategy: Detect falling edge of w_uart_data_write AND verify we saw wr_ack.
    // This ensures tx_write fires AFTER the PeakRDL register has updated.
    //
    // One-shot for RX read: generate single pulse per read transaction
    // We want to advance the FIFO pointer exactly once per read, after the data
    // has been captured by the response pipeline.
    //
    // Strategy: Detect falling edge of w_uart_data_read (NOT just !regblk_req).
    // This handles back-to-back transactions where regblk_req stays high but
    // the address changes (e.g., LSR read followed by UART_DATA read).
    //
    // Timing: regblk_rd_ack fires when PeakRDL captures the read data.
    // We wait for the UART_DATA read to complete (w_uart_data_read falls)
    // then fire rx_read ONE cycle later to advance the FIFO pointer.
    logic r_uart_data_read_prev;    // Previous cycle's w_uart_data_read
    logic r_uart_data_read_acked;   // Saw regblk_rd_ack during UART_DATA read
    logic r_uart_data_write_prev;   // Previous cycle's w_uart_data_write
    logic r_uart_data_write_acked;  // Saw regblk_wr_ack during UART_DATA write

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_tx_data_prev <= '0;
            r_cmd_we_prev  <= 1'b0;
            r_uart_data_read_prev <= 1'b0;
            r_uart_data_read_acked <= 1'b0;
            r_uart_data_write_prev <= 1'b0;
            r_uart_data_write_acked <= 1'b0;
        end else begin
            r_tx_data_prev <= hwif_out.UART_DATA.tx_data.value;
            r_cmd_we_prev  <= w_uart_data_write;

            // Track previous cycle's UART_DATA read state
            r_uart_data_read_prev <= w_uart_data_read;

            // Track if we've seen an ack during a UART_DATA read
            if (w_uart_data_read && regblk_rd_ack) begin
                r_uart_data_read_acked <= 1'b1;
            end else if (!w_uart_data_read) begin
                // Clear acked flag when UART_DATA read ends
                r_uart_data_read_acked <= 1'b0;
            end

            // Track previous cycle's UART_DATA write state
            r_uart_data_write_prev <= w_uart_data_write;

            // Track if we've seen an ack during a UART_DATA write
            if (w_uart_data_write && regblk_wr_ack) begin
                r_uart_data_write_acked <= 1'b1;
            end else if (!w_uart_data_write) begin
                // Clear acked flag when UART_DATA write ends
                r_uart_data_write_acked <= 1'b0;
            end
        end
    )

    // Write to TX on falling edge of UART_DATA write IF we saw wr_ack
    // This fires ONE cycle after the PeakRDL register updates, ensuring tx_data is valid
    assign w_tx_write = r_uart_data_write_prev && !w_uart_data_write && r_uart_data_write_acked;

    // Read from RX - fires on falling edge of w_uart_data_read IF we saw an ack
    // This means we only advance the pointer after a successful read that saw regblk_rd_ack
    assign w_rx_read = r_uart_data_read_prev && !w_uart_data_read && r_uart_data_read_acked;

    // ========================================================================
    // UART Core Instance
    // ========================================================================
    uart_16550_core #(
        .FIFO_DEPTH     (FIFO_DEPTH),
        .SYNC_STAGES    (SYNC_STAGES)
    ) u_uart_core (
        .clk            (clk),
        .rst_n          (rst_n),

        // Serial interface
        .uart_rx        (uart_rx),
        .uart_tx        (uart_tx),

        // Modem inputs
        .cts_n          (cts_n),
        .dsr_n          (dsr_n),
        .ri_n           (ri_n),
        .dcd_n          (dcd_n),

        // Modem outputs
        .dtr_n          (dtr_n),
        .rts_n          (rts_n),
        .out1_n         (out1_n),
        .out2_n         (out2_n),

        // Configuration
        .cfg_divisor        ({hwif_out.UART_DLM.dlm.value, hwif_out.UART_DLL.dll.value}),
        .cfg_word_length    (hwif_out.UART_LCR.word_length.value),
        .cfg_stop_bits      (hwif_out.UART_LCR.stop_bits.value),
        .cfg_parity_enable  (hwif_out.UART_LCR.parity_enable.value),
        .cfg_even_parity    (hwif_out.UART_LCR.even_parity.value),
        .cfg_stick_parity   (hwif_out.UART_LCR.stick_parity.value),
        .cfg_set_break      (hwif_out.UART_LCR.set_break.value),
        .cfg_fifo_enable    (hwif_out.UART_FCR.fifo_enable.value),
        .cfg_rx_trigger     (hwif_out.UART_FCR.rx_trigger.value),
        .cfg_dtr            (hwif_out.UART_MCR.dtr.value),
        .cfg_rts            (hwif_out.UART_MCR.rts.value),
        .cfg_out1           (hwif_out.UART_MCR.out1.value),
        .cfg_out2           (hwif_out.UART_MCR.out2.value),
        .cfg_loopback       (hwif_out.UART_MCR.loopback.value),

        // FIFO commands
        .cmd_rx_fifo_reset  (hwif_out.UART_FCR.rx_fifo_reset.value),
        .cmd_tx_fifo_reset  (hwif_out.UART_FCR.tx_fifo_reset.value),

        // TX data
        .tx_data            (hwif_out.UART_DATA.tx_data.value),
        .tx_write           (w_tx_write),

        // RX data
        .rx_data            (w_rx_data),
        .rx_read            (w_rx_read),

        // Status outputs
        .sts_data_ready     (w_sts_data_ready),
        .sts_overrun_error  (w_sts_overrun_error),
        .sts_parity_error   (w_sts_parity_error),
        .sts_framing_error  (w_sts_framing_error),
        .sts_break_interrupt(w_sts_break_interrupt),
        .sts_tx_holding_empty(w_sts_tx_holding_empty),
        .sts_tx_empty       (w_sts_tx_empty),
        .sts_rx_fifo_error  (w_sts_rx_fifo_error),
        .sts_delta_cts      (w_sts_delta_cts),
        .sts_delta_dsr      (w_sts_delta_dsr),
        .sts_trailing_ri    (w_sts_trailing_ri),
        .sts_delta_dcd      (w_sts_delta_dcd),
        .sts_cts            (w_sts_cts),
        .sts_dsr            (w_sts_dsr),
        .sts_ri             (w_sts_ri),
        .sts_dcd            (w_sts_dcd),
        .sts_fifo_status    (w_sts_fifo_status),

        // Status clear (W1C from register writes - handled by PeakRDL)
        .clr_overrun_error  (1'b0),
        .clr_parity_error   (1'b0),
        .clr_framing_error  (1'b0),
        .clr_break_interrupt(1'b0),
        .clr_delta_cts      (1'b0),
        .clr_delta_dsr      (1'b0),
        .clr_trailing_ri    (1'b0),
        .clr_delta_dcd      (1'b0),

        // Interrupt
        .int_not_pending    (w_int_not_pending),
        .int_id             (w_int_id),
        .int_timeout        (w_int_timeout),
        .irq                (irq)
    );

    // ========================================================================
    // Connect Status to hwif_in
    // ========================================================================
    // RX data
    assign hwif_in.UART_DATA.rx_data.next = w_rx_data;

    // IIR
    assign hwif_in.UART_IIR.int_not_pending.next = w_int_not_pending;
    assign hwif_in.UART_IIR.int_id.next = w_int_id;
    assign hwif_in.UART_IIR.timeout_pending.next = w_int_timeout;
    assign hwif_in.UART_IIR.fifo_status.next = w_sts_fifo_status;

    // LSR
    assign hwif_in.UART_LSR.data_ready.next = w_sts_data_ready;
    assign hwif_in.UART_LSR.overrun_error.next = w_sts_overrun_error;
    assign hwif_in.UART_LSR.overrun_error.hwset = w_sts_overrun_error;
    assign hwif_in.UART_LSR.parity_error.next = w_sts_parity_error;
    assign hwif_in.UART_LSR.parity_error.hwset = w_sts_parity_error;
    assign hwif_in.UART_LSR.framing_error.next = w_sts_framing_error;
    assign hwif_in.UART_LSR.framing_error.hwset = w_sts_framing_error;
    assign hwif_in.UART_LSR.break_interrupt.next = w_sts_break_interrupt;
    assign hwif_in.UART_LSR.break_interrupt.hwset = w_sts_break_interrupt;
    assign hwif_in.UART_LSR.tx_holding_empty.next = w_sts_tx_holding_empty;
    assign hwif_in.UART_LSR.tx_empty.next = w_sts_tx_empty;
    assign hwif_in.UART_LSR.rx_fifo_error.next = w_sts_rx_fifo_error;

    // MSR
    assign hwif_in.UART_MSR.delta_cts.next = w_sts_delta_cts;
    assign hwif_in.UART_MSR.delta_cts.hwset = w_sts_delta_cts;
    assign hwif_in.UART_MSR.delta_dsr.next = w_sts_delta_dsr;
    assign hwif_in.UART_MSR.delta_dsr.hwset = w_sts_delta_dsr;
    assign hwif_in.UART_MSR.trailing_ri.next = w_sts_trailing_ri;
    assign hwif_in.UART_MSR.trailing_ri.hwset = w_sts_trailing_ri;
    assign hwif_in.UART_MSR.delta_dcd.next = w_sts_delta_dcd;
    assign hwif_in.UART_MSR.delta_dcd.hwset = w_sts_delta_dcd;
    assign hwif_in.UART_MSR.cts.next = w_sts_cts;
    assign hwif_in.UART_MSR.dsr.next = w_sts_dsr;
    assign hwif_in.UART_MSR.ri.next = w_sts_ri;
    assign hwif_in.UART_MSR.dcd.next = w_sts_dcd;

endmodule : uart_16550_config_regs

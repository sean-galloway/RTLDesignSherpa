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
//   APB -> apb4_slave -> CMD/RSP -> peakrdl_to_cmdrsp -> regblk_* ->
//     -> uart_16550_regs (PeakRDL) -> hwif -> uart_16550_core
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
    output logic        irq,
    output logic        rxrdy_n,
    output logic        txrdy_n
);

    // PeakRDL hardware interface signals
    uart_16550_regs_pkg::uart_16550_regs__in_t  hwif_in;
    uart_16550_regs_pkg::uart_16550_regs__out_t hwif_out;

    // Internal signals
    logic [7:0]  w_rx_data;
    logic        w_tx_write;
    logic        w_rx_read;

    // Strict decode: the adapter's side of the passthrough, so an unmapped
    // access can be answered locally without ever reaching the register block.
    logic                    w_addr_mapped;
    // DLAB remapping. The map is flat - DLL and DLM have their own offsets at
    // 0x24 and 0x28 and always work - but a driver written against a standard
    // 16550 expects 0x00 and 0x04 to become the divisor latches while LCR[7]
    // is set. Both forms are supported: the remap is applied to the address
    // the register block sees, and every strobe below decodes the SAME
    // remapped address, so a divisor write can never be mistaken for a THR
    // push or an IER write (RLB-013).
    logic                    w_dlab;
    logic [5:0]              w_reg_addr;
    logic                    w_drop;
    logic                    w_drop_ack;
    logic                    w_blk_req;
    logic                    w_blk_rd_ack;
    logic                    w_blk_rd_err;
    logic [DATA_WIDTH-1:0]   w_blk_rd_data;
    logic                    w_blk_wr_ack;
    logic                    w_blk_wr_err;

    // Read-clear strobes (16550: LSR errors clear on a read of LSR, MSR
    // deltas clear on a read of MSR).
    logic        w_lsr_read;
    logic        w_msr_read;
    logic        w_iir_read;
    logic        r_lsr_read_d;
    logic        r_msr_read_d;
    logic        r_iir_read_d;
    logic        w_lsr_read_evt;
    logic        w_msr_read_evt;
    logic        w_iir_read_evt;

    // Mapped register offsets - the same six bits the register block decodes.
    localparam logic [5:0] ADDR_DATA = 6'h00;
    localparam logic [5:0] ADDR_IER  = 6'h04;
    localparam logic [5:0] ADDR_IIR  = 6'h08;
    localparam logic [5:0] ADDR_FCR  = 6'h0C;
    localparam logic [5:0] ADDR_LCR  = 6'h10;
    localparam logic [5:0] ADDR_MCR  = 6'h14;
    localparam logic [5:0] ADDR_LSR  = 6'h18;
    localparam logic [5:0] ADDR_MSR  = 6'h1C;
    localparam logic [5:0] ADDR_SCR  = 6'h20;
    localparam logic [5:0] ADDR_DLL  = 6'h24;
    localparam logic [5:0] ADDR_DLM  = 6'h28;

    assign w_dlab = hwif_out.UART_LCR.dlab.value;
    always_comb begin
        w_reg_addr = regblk_addr[5:0];
        if (w_dlab) begin
            if (regblk_addr[5:0] == ADDR_DATA) w_reg_addr = ADDR_DLL;
            else if (regblk_addr[5:0] == ADDR_IER) w_reg_addr = ADDR_DLM;
        end
    end

    // TX write detection (edge on tx_data register write)

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
    // PeakRDL's regblock takes an ACTIVE-HIGH reset whatever the build
    // uses. Ask the macro whether reset is asserted rather than
    // inverting rst_n by hand: `~rst_n` is correct only while the
    // build is active-low, and under -DRESET_ACTIVE_HIGH it held the
    // whole register file in reset forever (RLB-012).
    uart_16550_regs u_uart_regs (
        .clk        (clk),
        .rst        (`RST_ASSERTED(rst_n)),
        // PeakRDL cpuif interface (from peakrdl_to_cmdrsp)
        .s_cpuif_req            (w_blk_req),
        .s_cpuif_req_is_wr      (regblk_req_is_wr),
        .s_cpuif_addr           (w_reg_addr),  // 6-bit address, DLAB-remapped
        .s_cpuif_wr_data        (regblk_wr_data),
        .s_cpuif_wr_biten       (regblk_wr_biten),
        .s_cpuif_req_stall_wr   (regblk_req_stall_wr),
        .s_cpuif_req_stall_rd   (regblk_req_stall_rd),
        .s_cpuif_rd_ack         (w_blk_rd_ack),
        .s_cpuif_rd_err         (w_blk_rd_err),
        .s_cpuif_rd_data        (w_blk_rd_data),
        .s_cpuif_wr_ack         (w_blk_wr_ack),
        .s_cpuif_wr_err         (w_blk_wr_err),

        // Hardware interface
        .hwif_in    (hwif_in),
        .hwif_out   (hwif_out)
    );

    // ========================================================================
    // Strict Address Decode
    // ========================================================================
    // ONLY THE ELEVEN MAPPED REGISTERS DECODE. Everything else in the window
    // is dropped: no internal strobe fires, the read returns 0, and the access
    // is acknowledged locally with PSLVERR. The register block sees six
    // address bits, so without this every unmapped address aliases onto a real
    // register 64 bytes below it. The acknowledge is combinational and local,
    // the same shape the block itself uses, because the adapter holds its
    // request until it is acked - a dropped access that is never acked hangs
    // the bus.
    always_comb begin
        w_addr_mapped = (regblk_addr[5:0] == ADDR_DATA) ||
                        (regblk_addr[5:0] == ADDR_IER)  ||
                        (regblk_addr[5:0] == ADDR_IIR)  ||
                        (regblk_addr[5:0] == ADDR_FCR)  ||
                        (regblk_addr[5:0] == ADDR_LCR)  ||
                        (regblk_addr[5:0] == ADDR_MCR)  ||
                        (regblk_addr[5:0] == ADDR_LSR)  ||
                        (regblk_addr[5:0] == ADDR_MSR)  ||
                        (regblk_addr[5:0] == ADDR_SCR)  ||
                        (regblk_addr[5:0] == ADDR_DLL)  ||
                        (regblk_addr[5:0] == ADDR_DLM);
        w_addr_mapped = w_addr_mapped && (regblk_addr[ADDR_WIDTH-1:6] == '0);
    end

    assign w_drop     = !w_addr_mapped;
    assign w_drop_ack = regblk_req && w_drop;
    assign w_blk_req  = regblk_req && !w_drop;

    assign regblk_rd_ack  = w_blk_rd_ack | (w_drop_ack & ~regblk_req_is_wr);
    assign regblk_rd_err  = w_blk_rd_err | (w_drop_ack & ~regblk_req_is_wr);
    assign regblk_rd_data = w_drop_ack ? '0 : w_blk_rd_data;
    assign regblk_wr_ack  = w_blk_wr_ack | (w_drop_ack & regblk_req_is_wr);
    assign regblk_wr_err  = w_blk_wr_err | (w_drop_ack & regblk_req_is_wr);

    // ========================================================================
    // Read-clear strobes
    // ========================================================================
    // 16550 semantics: reading LSR clears its error bits, reading MSR clears
    // its delta bits, and reading IIR clears the THR-empty interrupt when THR
    // empty is the source being reported. Edge-detected because the bridge
    // holds the request for two cycles and a level would clear twice - the
    // second clear would swallow an event the core accepted in between.
    assign w_lsr_read = w_blk_req && !regblk_req_is_wr && (w_reg_addr == ADDR_LSR);
    assign w_msr_read = w_blk_req && !regblk_req_is_wr && (w_reg_addr == ADDR_MSR);
    assign w_iir_read = w_blk_req && !regblk_req_is_wr && (w_reg_addr == ADDR_IIR);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_lsr_read_d <= 1'b0;
            r_msr_read_d <= 1'b0;
            r_iir_read_d <= 1'b0;
        end else begin
            r_lsr_read_d <= w_lsr_read;
            r_msr_read_d <= w_msr_read;
            r_iir_read_d <= w_iir_read;
        end
    )

    assign w_lsr_read_evt = w_lsr_read && !r_lsr_read_d;
    assign w_msr_read_evt = w_msr_read && !r_msr_read_d;
    assign w_iir_read_evt = w_iir_read && !r_iir_read_d;

    // ========================================================================
    // TX Write Edge Detection and RX Read Edge Detection
    // ========================================================================
    // Track if we're doing a UART_DATA register read or write
    logic w_uart_data_read;
    logic w_uart_data_write;
    assign w_uart_data_read  = w_blk_req && !regblk_req_is_wr &&
                               (w_reg_addr == ADDR_DATA);

    // THE BYTE ENABLE IS PART OF THE DECODE, NOT JUST OF THE DATA. A write
    // to UART_DATA with lane 0 disabled (PSTRB=4'b0010, say) is not a THR
    // write at all. Masking the captured byte but pushing anyway - which is
    // what this did - transmitted a NUL for every such access.
    assign w_uart_data_write = w_blk_req && regblk_req_is_wr &&
                               (w_reg_addr == ADDR_DATA) &&
                               regblk_wr_biten[0];

    // THR PUSH: ONE PULSE PER ACKED WRITE, taken from the write-data lane.
    //
    // THR has no register field (see the RDL): it is write-only, so there is
    // no storage to read back and nothing to wait for. The byte is whatever
    // this access is writing, captured on the acked cycle, and the push is a
    // rising-edge pulse on that cycle.
    //
    // THIS DEPENDS ON THE REQUEST DROPPING BETWEEN COMMANDS, and it is worth
    // being honest about that rather than claiming it is correct by
    // construction. peakrdl_to_cmdrsp holds regblk_req from the accept cycle
    // through CMD_WAIT_ACK, and this regblock's ack is combinational on the
    // held request, so one command is two cycles of req and ack together.
    // Back-to-back commands with no idle cycle between them would be four
    // such cycles with one rising edge, and the second byte would be lost.
    // That cannot happen behind an APB front end - APB is strictly
    // one-outstanding and needs a SETUP cycle per transfer, and the bridge
    // itself would drop the second response anyway (its rsp FSM only
    // captures in RSP_IDLE) - but nothing in THIS file enforces it.
    //
    // The fix does not belong here: no signal visible to this module marks a
    // command boundary. req and ack alone cannot distinguish "the extra held
    // cycle after an ack" from "the first cycle of the next command", and
    // the two cases need opposite decisions. A one-cycle accept qualifier
    // from peakrdl_to_cmdrsp would settle it; that file is shared and out of
    // scope here. The same dependency applies to the LSR/MSR/IIR read events
    // and to the RBR pop below.
    logic       r_thr_ack_d;
    logic       r_thr_push;
    logic [7:0] r_thr_data;
    logic       w_thr_ack_now;

    logic       r_rbr_ack_d;
    logic       r_rbr_pop;
    logic       w_rbr_ack_now;

    // The ack is COMBINATIONAL on the held request, so it is high for BOTH
    // cycles the bridge holds it - a pulse taken straight from it pushes the
    // same byte twice. Rising edge, then one cycle of delay so the captured
    // byte is stable when the push fires.
    assign w_thr_ack_now = w_uart_data_write && w_blk_wr_ack;
    assign w_rbr_ack_now = w_uart_data_read  && w_blk_rd_ack;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_thr_ack_d <= 1'b0;
            r_thr_push  <= 1'b0;
            r_thr_data  <= 8'h00;
            r_rbr_ack_d <= 1'b0;
            r_rbr_pop   <= 1'b0;
        end else begin
            r_thr_ack_d <= w_thr_ack_now;
            r_thr_push  <= w_thr_ack_now && !r_thr_ack_d;
            if (w_thr_ack_now && !r_thr_ack_d) begin
                r_thr_data <= regblk_wr_data[7:0] & regblk_wr_biten[7:0];
            end

            r_rbr_ack_d <= w_rbr_ack_now;
            r_rbr_pop   <= w_rbr_ack_now && !r_rbr_ack_d;
        end
    )

    assign w_tx_write = r_thr_push;
    assign w_rx_read  = r_rbr_pop;

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
        .cfg_afe            (hwif_out.UART_MCR.afe.value),

        // FIFO commands
        .cmd_rx_fifo_reset  (hwif_out.UART_FCR.rx_fifo_reset.value),
        .cmd_tx_fifo_reset  (hwif_out.UART_FCR.tx_fifo_reset.value),

        // TX data
        .tx_data            (r_thr_data),
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
        .clr_overrun_error  (w_lsr_read_evt),
        .clr_parity_error   (w_lsr_read_evt),
        .clr_framing_error  (w_lsr_read_evt),
        .clr_break_interrupt(w_lsr_read_evt),
        // 16550 interrupt enables, one per source
        .cfg_rx_data_ie     (hwif_out.UART_IER.rx_data_avail_ie.value),
        .cfg_tx_empty_ie    (hwif_out.UART_IER.tx_empty_ie.value),
        .cfg_line_status_ie (hwif_out.UART_IER.rx_line_status_ie.value),
        .cfg_modem_ie       (hwif_out.UART_IER.modem_status_ie.value),
        .iir_read           (w_iir_read_evt),

        .clr_delta_cts      (w_msr_read_evt),
        .clr_delta_dsr      (w_msr_read_evt),
        .clr_trailing_ri    (w_msr_read_evt),
        .clr_delta_dcd      (w_msr_read_evt),

        // Interrupt
        .int_not_pending    (w_int_not_pending),
        .int_id             (w_int_id),
        .int_timeout        (w_int_timeout),
        .irq                (irq),
        .cfg_dma_mode       (hwif_out.UART_FCR.dma_mode.value),
        .rxrdy_n            (rxrdy_n),
        .txrdy_n            (txrdy_n)
    );

    // ========================================================================
    // Connect Status to hwif_in
    // ========================================================================
    // RX data
    assign hwif_in.UART_DATA.rx_data.next       = w_rx_data;
    assign hwif_in.UART_DATA.rx_data_alias.next = w_rx_data;

    // IIR
    assign hwif_in.UART_IIR.int_not_pending.next = w_int_not_pending;
    assign hwif_in.UART_IIR.int_id.next = w_int_id;
    assign hwif_in.UART_IIR.timeout_pending.next = w_int_timeout;
    assign hwif_in.UART_IIR.fifo_status.next = w_sts_fifo_status;

    // LSR
    assign hwif_in.UART_LSR.data_ready.next = w_sts_data_ready;
    assign hwif_in.UART_LSR.overrun_error.hwset = w_sts_overrun_error;
    assign hwif_in.UART_LSR.parity_error.hwset = w_sts_parity_error;
    assign hwif_in.UART_LSR.framing_error.hwset = w_sts_framing_error;
    assign hwif_in.UART_LSR.break_interrupt.hwset = w_sts_break_interrupt;
    assign hwif_in.UART_LSR.tx_holding_empty.next = w_sts_tx_holding_empty;
    assign hwif_in.UART_LSR.tx_empty.next = w_sts_tx_empty;
    assign hwif_in.UART_LSR.rx_fifo_error.next = w_sts_rx_fifo_error;

    // MSR
    assign hwif_in.UART_MSR.delta_cts.hwset = w_sts_delta_cts;
    assign hwif_in.UART_MSR.delta_dsr.hwset = w_sts_delta_dsr;
    assign hwif_in.UART_MSR.trailing_ri.hwset = w_sts_trailing_ri;
    assign hwif_in.UART_MSR.delta_dcd.hwset = w_sts_delta_dcd;
    assign hwif_in.UART_MSR.cts.next = w_sts_cts;
    assign hwif_in.UART_MSR.dsr.next = w_sts_dsr;
    assign hwif_in.UART_MSR.ri.next = w_sts_ri;
    assign hwif_in.UART_MSR.dcd.next = w_sts_dcd;

endmodule : uart_16550_config_regs

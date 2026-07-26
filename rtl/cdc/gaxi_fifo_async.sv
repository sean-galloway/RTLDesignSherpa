// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gaxi_fifo_async
// Purpose: Gaxi Fifo Async module
//
// Documentation: docs/markdown/rtl-cdc/gaxi_fifo_async.md
// Subsystem: cdc
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "fifo_defs.svh"
`include "reset_defs.svh"


// Paramerized Asynchronous FIFO -- This works for any even depth
module gaxi_fifo_async #(
    parameter fifo_mem_t MEM_STYLE = FIFO_AUTO,
    parameter int        REGISTERED       = 0,   // 0 = mux mode, 1 = flop mode
    parameter int        DATA_WIDTH       = 8,
    // DEPTH default is a POWER OF 2 so the all-defaults configuration is legal
    // under the default Gray encoding (USE_JOHNSON=0). Was 10, which became an
    // illegal default when USE_JOHNSON was introduced.
    parameter int        DEPTH            = 16,
    // Pointer CDC encoding.
    //   0 (default) = GRAY code. Pointer is AW+1 bits, converted with gray2bin.
    //                 Cheap and the industry-standard scheme, but REQUIRES a
    //                 power-of-2 DEPTH (a Gray sequence only has the
    //                 single-bit-change property when it wraps at 2**N).
    //   1           = JOHNSON code. Pointer is DEPTH bits (JCW), converted with
    //                 johnson2bin. Costs DEPTH flops per pointer instead of
    //                 AW+1, but supports ARBITRARY (non-power-of-2) DEPTH.
    // Both encodings change only one bit per increment, so both are safe to
    // synchronize; this selects cost vs depth flexibility, not CDC safety.
    parameter int        USE_JOHNSON      = 0,
    parameter int        N_FLOP_CROSS     = 2,
    parameter int        ALMOST_WR_MARGIN = 1,
    parameter int        ALMOST_RD_MARGIN = 1,
    parameter int        DW = DATA_WIDTH,
    parameter int        D  = DEPTH,
    parameter int        AW = $clog2(DEPTH),
    parameter int        JCW = D,   // Johnson Counter Width
    parameter int        N  = N_FLOP_CROSS
) (
    // clocks and resets
    input  logic            axi_wr_aclk,
                            axi_wr_aresetn,
                            axi_rd_aclk,
                            axi_rd_aresetn,
    // write side
    input  logic            wr_valid,
    output logic            wr_ready,   // not full
    input  logic [DW-1:0]   wr_data,
    // read side
    input  logic            rd_ready,
    output logic            rd_valid,   // not empty
    output logic [DW-1:0]   rd_data
);

    /////////////////////////////////////////////////////////////////////////
    // locals
    /////////////////////////////////////////////////////////////////////////
    logic [AW-1:0] r_wr_addr, r_rd_addr;

    // Width of the CDC'd pointer: DEPTH bits for Johnson, AW+1 for Gray.
    localparam int PTRW = (USE_JOHNSON != 0) ? JCW : (AW + 1);

    // Gray mode needs a power-of-2 DEPTH; Johnson does not. This is an
    // ELABORATION-time check (generate-scope $error), so an illegal
    // configuration fails the build rather than silently producing a corrupt
    // pointer on silicon. Do NOT move this into an `initial` block -- that is a
    // runtime construct and would never fire during lint or elaboration.
    generate
    if ((USE_JOHNSON == 0) && ((DEPTH & (DEPTH - 1)) != 0)) begin : g_bad_depth
        $error("gaxi_fifo_async: USE_JOHNSON=0 (Gray) requires a power-of-2 DEPTH, got %0d. Set USE_JOHNSON=1 for arbitrary depths.", DEPTH);
    end
    endgenerate

    // Johnson/Gray domain pointers
    logic [PTRW-1:0] r_wr_ptr_gray, r_wdom_rd_ptr_gray, r_rd_ptr_gray, r_rdom_wr_ptr_gray;
    // Binary pointers (+wrap bit)
    logic [AW:0] r_wr_ptr_bin, w_wdom_rd_ptr_bin, r_rd_ptr_bin, w_rdom_wr_ptr_bin;
    logic [AW:0] w_wr_ptr_bin_next, w_rd_ptr_bin_next;
    logic        r_wr_full, r_wr_almost_full, r_rd_empty, r_rd_almost_empty;
    logic        w_write, w_read;
    logic [AW:0] w_count;

    // Common read data; driven inside the selected memory branch
    logic [DW-1:0] w_rd_data;

    /////////////////////////////////////////////////////////////////////////
    // write/read enables
    /////////////////////////////////////////////////////////////////////////
    assign w_write = wr_valid && wr_ready;
    assign w_read  = rd_valid && rd_ready;

    /////////////////////////////////////////////////////////////////////////
    // Binary pointer counters (wr/rd domains)
    /////////////////////////////////////////////////////////////////////////
    generate
    if (USE_JOHNSON != 0) begin : g_ptr_johnson
        // Binary pointer wraps at MAX=D with an inverted MSB, so arbitrary
        // (non-power-of-2) depths work. The Johnson pointer is DEPTH bits.
        counter_bin #(
            .MAX   (D),
            .WIDTH (AW + 1)
        ) wr_ptr_counter_bin(
            .clk              (axi_wr_aclk),
            .rst_n            (axi_wr_aresetn),
            .enable           (w_write && !r_wr_full),
            .counter_bin_next (w_wr_ptr_bin_next),
            .counter_bin_curr (r_wr_ptr_bin)
        );

        counter_bin #(
            .MAX   (D),
            .WIDTH (AW + 1)
        ) rd_ptr_counter_bin(
            .clk              (axi_rd_aclk),
            .rst_n            (axi_rd_aresetn),
            .enable           (w_read && !r_rd_empty),
            .counter_bin_next (w_rd_ptr_bin_next),
            .counter_bin_curr (r_rd_ptr_bin)
        );

        counter_johnson #(
            .WIDTH (JCW)
        ) wr_ptr_counter_gray(
            .clk          (axi_wr_aclk),
            .rst_n        (axi_wr_aresetn),
            .enable       (w_write && !r_wr_full),
            .counter_gray (r_wr_ptr_gray)
        );

        counter_johnson #(
            .WIDTH (JCW)
        ) rd_ptr_counter_gray(
            .clk          (axi_rd_aclk),
            .rst_n        (axi_rd_aresetn),
            .enable       (w_read && !r_rd_empty),
            .counter_gray (r_rd_ptr_gray)
        );
    end else begin : g_ptr_gray
        // counter_bingray emits the binary counter AND its registered Gray
        // encoding from one instance, so the separate counter_bin is not
        // needed. Free-running AW+1 bits == counter_bin(MAX=D) when D is a
        // power of 2 (enforced by the elaboration check above). Registering
        // the Gray value (rather than XOR-ing the binary combinationally)
        // keeps the crossing glitch-free.
        counter_bingray #(
            .WIDTH (AW + 1)
        ) wr_ptr_counter_bingray(
            .clk              (axi_wr_aclk),
            .rst_n            (axi_wr_aresetn),
            .enable           (w_write && !r_wr_full),
            .counter_bin      (r_wr_ptr_bin),
            .counter_bin_next (w_wr_ptr_bin_next),
            .counter_gray     (r_wr_ptr_gray)
        );

        counter_bingray #(
            .WIDTH (AW + 1)
        ) rd_ptr_counter_bingray(
            .clk              (axi_rd_aclk),
            .rst_n            (axi_rd_aresetn),
            .enable           (w_read && !r_rd_empty),
            .counter_bin      (r_rd_ptr_bin),
            .counter_bin_next (w_rd_ptr_bin_next),
            .counter_gray     (r_rd_ptr_gray)
        );
    end
    endgenerate

    /////////////////////////////////////////////////////////////////////////
    // CDC of Johnson/Gray pointers and conversion to binary
    /////////////////////////////////////////////////////////////////////////
    // NOTE (reset robustness): each domain synchronizes the REMOTE pointer using
    // its OWN clock and its OWN reset. A reset applied to one domain alone
    // therefore clears both that domain's pointer and its copy of the remote
    // pointer together, leaving that side self-consistent (both zero => empty)
    // rather than desynchronized. This holds for either encoding.
    glitch_free_n_dff_arn #(
        .FLOP_COUNT (N),
        .WIDTH      (PTRW)
    ) rd_ptr_gray_cross_inst(
        .q     (r_wdom_rd_ptr_gray),
        .d     (r_rd_ptr_gray),
        .clk   (axi_wr_aclk),
        .rst_n (axi_wr_aresetn)
    );

    glitch_free_n_dff_arn #(
        .FLOP_COUNT (N),
        .WIDTH      (PTRW)
    ) wr_ptr_gray_cross_inst(
        .q     (r_rdom_wr_ptr_gray),
        .d     (r_wr_ptr_gray),
        .clk   (axi_rd_aclk),
        .rst_n (axi_rd_aresetn)
    );

    generate
    if (USE_JOHNSON != 0) begin : g_cvt_johnson
        // johnson2bin is registered (takes clk/rst_n).
        johnson2bin #(
            .JCW           (JCW),
            .WIDTH         (AW + 1)
        ) rd_ptr_gray2bin_inst(
            .binary (w_wdom_rd_ptr_bin),
            .gray   (r_wdom_rd_ptr_gray),
            .clk    (axi_wr_aclk),
            .rst_n  (axi_wr_aresetn)
        );

        johnson2bin #(
            .JCW           (JCW),
            .WIDTH         (AW + 1)
        ) wr_ptr_gray2bin_inst(
            .binary (w_rdom_wr_ptr_bin),
            .gray   (r_rdom_wr_ptr_gray),
            .clk    (axi_rd_aclk),
            .rst_n  (axi_rd_aresetn)
        );
    end else begin : g_cvt_gray
        // gray2bin is purely combinational (no clk/rst), so the Gray path has
        // one less pipeline stage than the Johnson path on the pointer compare.
        gray2bin #(
            .WIDTH (AW + 1)
        ) rd_ptr_gray2bin_inst(
            .binary (w_wdom_rd_ptr_bin),
            .gray   (r_wdom_rd_ptr_gray)
        );

        gray2bin #(
            .WIDTH (AW + 1)
        ) wr_ptr_gray2bin_inst(
            .binary (w_rdom_wr_ptr_bin),
            .gray   (r_rdom_wr_ptr_gray)
        );
    end
    endgenerate

    /////////////////////////////////////////////////////////////////////////
    // address extraction
    /////////////////////////////////////////////////////////////////////////
    assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr = r_rd_ptr_bin[AW-1:0];

    /////////////////////////////////////////////////////////////////////////
    // Full/empty/almost & count
    /////////////////////////////////////////////////////////////////////////
    fifo_control #(
        .DEPTH             (D),
        .ADDR_WIDTH        (AW),
        .ALMOST_RD_MARGIN  (ALMOST_RD_MARGIN),
        .ALMOST_WR_MARGIN  (ALMOST_WR_MARGIN),
        .REGISTERED        (REGISTERED)
    ) fifo_control_inst(
        .wr_clk            (axi_wr_aclk),
        .wr_rst_n          (axi_wr_aresetn),
        .rd_clk            (axi_rd_aclk),
        .rd_rst_n          (axi_rd_aresetn),
        .wr_ptr_bin        (w_wr_ptr_bin_next),
        .wdom_rd_ptr_bin   (w_wdom_rd_ptr_bin),
        .rd_ptr_bin        (w_rd_ptr_bin_next),
        .rdom_wr_ptr_bin   (w_rdom_wr_ptr_bin),
        .wr_full           (r_wr_full),
        .wr_almost_full    (r_wr_almost_full),
        .rd_empty          (r_rd_empty),
        .rd_almost_empty   (r_rd_almost_empty),
        .count             (w_count)
    );

    assign wr_ready = !r_wr_full;
    assign rd_valid = !r_rd_empty;

    /////////////////////////////////////////////////////////////////////////
    // Memory implementation (scoped per MEM_STYLE)
    //  * SRL/AUTO: allow combinational read when REGISTERED==0
    //  * BRAM:     synchronous read on axi_rd_aclk (true dual-port BRAM)
    //              ⇒ effective +1 cycle read latency even if REGISTERED==0
    /////////////////////////////////////////////////////////////////////////
    generate
        if (MEM_STYLE == FIFO_SRL) begin : gen_srl
            `ifdef XILINX
                (* shreg_extract = "yes", ram_style = "distributed" *)
            `elsif INTEL
                /* synthesis ramstyle = "MLAB" */
            `endif
            logic [DATA_WIDTH-1:0] mem [DEPTH];

            // Write port (axi_wr_aclk)
            always_ff @(posedge axi_wr_aclk) begin
                if (w_write && !r_wr_full) begin
                    mem[r_wr_addr] <= wr_data;
                end
            end

            // Read port
            if (REGISTERED != 0) begin : g_flop
                `ALWAYS_FF_RST(axi_rd_aclk, axi_rd_aresetn,
                    if (!axi_rd_aresetn) w_rd_data <= '0;
                    else                 w_rd_data <= mem[r_rd_addr];
                )

            end else begin : g_mux
                always_comb w_rd_data = mem[r_rd_addr];
            end

        end
        else if (MEM_STYLE == FIFO_BRAM) begin : gen_bram
            `ifdef XILINX
                (* ram_style = "block" *)
            `elsif INTEL
                /* synthesis ramstyle = "M20K" */
            `endif
            logic [DATA_WIDTH-1:0] mem [DEPTH];

            // Write port (axi_wr_aclk)
            always_ff @(posedge axi_wr_aclk) begin
                if (w_write && !r_wr_full) begin
                    mem[r_wr_addr] <= wr_data;
                end
            end

            // Synchronous read port (axi_rd_aclk) → infer true dual-port BRAM
            `ALWAYS_FF_RST(axi_rd_aclk, axi_rd_aresetn,
                if (!axi_rd_aresetn) w_rd_data <= '0;
                else                 w_rd_data <= mem[r_rd_addr];
            )


        end
        else begin : gen_auto
            // Let the tool decide (LUTRAM vs BRAM). Allow comb read in sim when REGISTERED==0.
            logic [DATA_WIDTH-1:0] mem [DEPTH];

            // Write port (axi_wr_aclk)
            always_ff @(posedge axi_wr_aclk) begin
                if (w_write && !r_wr_full) begin
                    mem[r_wr_addr] <= wr_data;
                end
            end

            if (REGISTERED != 0) begin : g_flop
                `ALWAYS_FF_RST(axi_rd_aclk, axi_rd_aresetn,
                    if (!axi_rd_aresetn) w_rd_data <= '0;
                    else                 w_rd_data <= mem[r_rd_addr];
                )

            end else begin : g_mux
                always_comb w_rd_data = mem[r_rd_addr];
            end

        end
    endgenerate

    // Common output connect
    assign rd_data = w_rd_data;

    /////////////////////////////////////////////////////////////////////////
    // Overflow/underflow error checking
    /////////////////////////////////////////////////////////////////////////
    always_ff @(posedge axi_rd_aclk) begin
        if (w_read && r_rd_empty) begin
        end
    end

endmodule : gaxi_fifo_async

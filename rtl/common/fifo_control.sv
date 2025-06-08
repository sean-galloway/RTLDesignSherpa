`timescale 1ns / 1ps

// Paramerized Asynchronous FIFO -- This only works for power of two depths
module fifo_control #(
    parameter int ADDR_WIDTH = 3,
    parameter int DEPTH = 16,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter int REGISTERED = 0  // 0 = mux mode, 1 = flop mode
) (
    // clocks and resets
    input  logic                    i_wr_clk,
                                    i_wr_rst_n,
                                    i_rd_clk,
                                    i_rd_rst_n,
    // Pointers
    input  logic [ADDR_WIDTH:0]     iw_wr_ptr_bin,
    input  logic [ADDR_WIDTH:0]     iw_wdom_rd_ptr_bin,
    input  logic [ADDR_WIDTH:0]     iw_rd_ptr_bin,
    input  logic [ADDR_WIDTH:0]     iw_rdom_wr_ptr_bin,
    output logic [ADDR_WIDTH:0]     ow_count,
    output logic                    o_wr_full,
    output logic                    o_wr_almost_full,
    output logic                    o_rd_empty,
    output logic                    o_rd_almost_empty
);

    localparam int D = DEPTH;
    localparam int AW = ADDR_WIDTH;
    localparam int AFULL = ALMOST_WR_MARGIN;
    localparam int AEMPTY = ALMOST_RD_MARGIN;
    localparam int AFT = D - AFULL;
    localparam int AET = AEMPTY;

    logic w_wdom_ptr_xor;
    logic w_rdom_ptr_xor;
    logic w_wr_full_d, w_wr_almost_full_d;
    logic w_rd_empty_d, w_rd_almost_empty_d;
    logic [AW-1:0] w_almost_full_count, w_almost_empty_count;

    /////////////////////////////////////////////////////////////////////////
    // XOR the two upper bits of the pointers to for use in the full/empty equations
    assign w_wdom_ptr_xor = iw_wr_ptr_bin[AW] ^ iw_wdom_rd_ptr_bin[AW];
    assign w_rdom_ptr_xor = iw_rd_ptr_bin[AW] ^ iw_rdom_wr_ptr_bin[AW];

    /////////////////////////////////////////////////////////////////////////
    // Full signals
    assign w_wr_full_d = (w_wdom_ptr_xor && (iw_wr_ptr_bin[AW-1:0] == iw_wdom_rd_ptr_bin[AW-1:0]));

    // Fixed: Cast D to AW-bit width to match other operands
    assign w_almost_full_count = (w_wdom_ptr_xor) ?
                        (AW'(D) - iw_wdom_rd_ptr_bin[AW-1:0] + iw_wr_ptr_bin[AW-1:0]) :
                        (iw_wr_ptr_bin[AW-1:0] - iw_wdom_rd_ptr_bin[AW-1:0]);

    assign w_wr_almost_full_d = w_almost_full_count >= AW'(AFT);

    always_ff @(posedge i_wr_clk, negedge i_wr_rst_n) begin
        if (!i_wr_rst_n) begin
            o_wr_full <= 'b0;
            o_wr_almost_full <= 'b0;
        end else begin
            o_wr_full <= w_wr_full_d;
            o_wr_almost_full <= w_wr_almost_full_d;
        end
    end

    /////////////////////////////////////////////////////////////////////////
    // Empty Signals - Mode-aware write pointer selection
    logic [ADDR_WIDTH:0] w_wr_ptr_for_empty;
    logic w_rdom_ptr_xor_for_empty;

    generate
        if (REGISTERED == 1) begin : gen_flop_mode
            // FLOP mode: Use previous cycle's write pointer to match registered data timing
            logic [ADDR_WIDTH:0] r_rdom_wr_ptr_bin_delayed;

            always_ff @(posedge i_rd_clk or negedge i_rd_rst_n) begin
                if (!i_rd_rst_n) begin
                    r_rdom_wr_ptr_bin_delayed <= '0;
                end else begin
                    r_rdom_wr_ptr_bin_delayed <= iw_rdom_wr_ptr_bin;
                end
            end

            assign w_wr_ptr_for_empty = r_rdom_wr_ptr_bin_delayed;
        end else begin : gen_mux_mode
            // MUX mode: Use current write pointer for immediate data availability
            assign w_wr_ptr_for_empty = iw_rdom_wr_ptr_bin;
        end
    endgenerate

    // Calculate XOR using the mode-appropriate write pointer
    assign w_rdom_ptr_xor_for_empty = iw_rd_ptr_bin[AW] ^ w_wr_ptr_for_empty[AW];

    // Empty detection using mode-appropriate write pointer
    assign w_rd_empty_d = (!w_rdom_ptr_xor_for_empty &&
                            (iw_rd_ptr_bin[AW:0] == w_wr_ptr_for_empty[AW:0]));

    /////////////////////////////////////////////////////////////////////////
    // Almost Empty calculation (uses standard timing regardless of mode)
    // Fixed: Cast D to AW-bit width to match other operands
    assign w_almost_empty_count = (w_rdom_ptr_xor) ?
                        (AW'(D) - iw_rd_ptr_bin[AW-1:0] + iw_rdom_wr_ptr_bin[AW-1:0]) :
                        (iw_rdom_wr_ptr_bin[AW-1:0] - iw_rd_ptr_bin[AW-1:0]);

    /* verilator lint_off CMPCONST */
    assign w_rd_almost_empty_d = w_almost_empty_count <= AW'(AET);
    /* verilator lint_on CMPCONST */

    // Fixed: Cast D to AW-bit width to match other operands
    assign ow_count = (w_rdom_ptr_xor) ?
                (iw_rdom_wr_ptr_bin[AW-1:0] - iw_rd_ptr_bin[AW-1:0] + AW'(D)) :
                (iw_rdom_wr_ptr_bin[AW-1:0] - iw_rd_ptr_bin[AW-1:0]);

    always_ff @(posedge i_rd_clk, negedge i_rd_rst_n) begin
        if (!i_rd_rst_n) begin
            o_rd_empty <= 'b1;
            o_rd_almost_empty <= 'b0;
        end else begin
            o_rd_empty <= w_rd_empty_d;
            o_rd_almost_empty <= w_rd_almost_empty_d;
        end
    end

endmodule : fifo_control

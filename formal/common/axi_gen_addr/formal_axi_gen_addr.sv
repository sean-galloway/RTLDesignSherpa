// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for axi_gen_addr (yosys-compatible)
// Proves burst type behavior: FIXED, INCR, WRAP address generation.

module formal_axi_gen_addr #(
    parameter int AW  = 32,
    parameter int DW  = 32,
    parameter int ODW = 32,
    parameter int LEN = 8
) (
    input logic clk
);

    (* anyconst *) logic [AW-1:0]  curr_addr;
    (* anyconst *) logic [2:0]     size;
    (* anyconst *) logic [1:0]     burst;
    (* anyconst *) logic [LEN-1:0] len;

    logic [AW-1:0] next_addr;
    logic [AW-1:0] next_addr_align;

    // Instantiate DUT
    axi_gen_addr #(
        .AW  (AW),
        .DW  (DW),
        .ODW (ODW),
        .LEN (LEN)
    ) dut (
        .curr_addr       (curr_addr),
        .size            (size),
        .burst           (burst),
        .len             (len),
        .next_addr       (next_addr),
        .next_addr_align (next_addr_align)
    );

    // =========================================================================
    // Derived constants
    // =========================================================================
    localparam int ODWBYTES = ODW / 8;
    wire [AW-1:0] w_increment = (AW'(1) << size);
    wire [AW-1:0] w_alignment_mask = AW'(ODWBYTES) - 1;

    // =========================================================================
    // Assumptions
    // =========================================================================

    // Size must not exceed data bus width
    always @(posedge clk)
        assume ((1 << size) <= (DW / 8));

    // =========================================================================
    // Safety properties
    // =========================================================================

    // FIXED burst (2'b00): next_addr == curr_addr
    always @(posedge clk) begin
        if (burst == 2'b00)
            ap_fixed: assert (next_addr == curr_addr);
    end

    // INCR burst (2'b01): next_addr == curr_addr + increment
    // When DW == ODW, increment is simply (1 << size)
    always @(posedge clk) begin
        if (burst == 2'b01 && DW == ODW)
            ap_incr: assert (next_addr == curr_addr + w_increment);
    end

    // INCR burst with different data widths: increment capped at ODWBYTES
    always @(posedge clk) begin
        if (burst == 2'b01 && DW != ODW) begin
            if (w_increment > AW'(ODWBYTES))
                ap_incr_capped: assert (next_addr == curr_addr + AW'(ODWBYTES));
            else
                ap_incr_narrow: assert (next_addr == curr_addr + w_increment);
        end
    end

    // All bursts: next_addr_align is aligned to ODW/8 bytes
    always @(posedge clk)
        ap_align: assert ((next_addr_align & w_alignment_mask) == '0);

    // next_addr_align is derived from next_addr with lower bits cleared
    always @(posedge clk)
        ap_align_source: assert (next_addr_align == (next_addr & ~w_alignment_mask));

    // FIXED burst: aligned address also based on curr_addr
    always @(posedge clk) begin
        if (burst == 2'b00)
            ap_fixed_align: assert (next_addr_align == (curr_addr & ~w_alignment_mask));
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover FIXED burst
    always @(posedge clk)
        cp_fixed: cover (burst == 2'b00);

    // Cover INCR burst
    always @(posedge clk)
        cp_incr: cover (burst == 2'b01);

    // Cover WRAP burst
    always @(posedge clk)
        cp_wrap: cover (burst == 2'b10);

    // Cover non-zero address with INCR
    always @(posedge clk)
        cp_incr_nonzero: cover (burst == 2'b01 && curr_addr != '0 && next_addr != '0);

    // Cover WRAP with typical AXI len (len=3 means 4-beat wrap)
    always @(posedge clk)
        cp_wrap_4beat: cover (burst == 2'b10 && len == LEN'(3));

endmodule

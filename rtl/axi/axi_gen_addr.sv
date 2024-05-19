`timescale 1ns / 1ps

module axi_gen_addr
#(
    parameter int AW  = 32,
    parameter int DW  = 32,
    parameter int ODW = 32, // ouptput data width
    parameter int LEN = 8
)(
    input  logic [AW-1:0]  i_curr_addr,
    input  logic [2:0]     i_size,
    input  logic [1:0]     i_burst,
    input  logic [LEN-1:0] i_len,
    output logic [AW-1:0]  ow_next_addr
);

localparam int ODWBYTES = ODW / 8;

logic [AW-1:0] increment_pre;
logic [AW-1:0] increment;
logic [AW-1:0] wrap_mask;
logic [AW-1:0] aligned_addr;
logic [AW-1:0] wrap_addr;


always_comb begin
    // calculate the increment; scale the increment if there is a difference between the two data widths
    increment_pre = (1 << i_size);
    increment     = increment_pre;
    if (DW != ODW) begin
        if (increment_pre > ODWBYTES)
            increment = ODWBYTES;
    end

    // Calculate the wrap mask based on i_size and i_len
    wrap_mask = (1 << (i_size + $clog2(i_len + 1))) - 1;

    // Calculate the aligned address
    aligned_addr = (i_curr_addr + increment) & ~(increment - 1);

    // Calculate the wrap address
    wrap_addr = (i_curr_addr & ~wrap_mask) | (aligned_addr & wrap_mask);
end

always_comb begin
    case (i_burst)
        2'b00: ow_next_addr = i_curr_addr;               // FIXED burst
        2'b01: ow_next_addr = i_curr_addr + increment;   // INCR burst
        2'b10: ow_next_addr = wrap_addr;                 // WRAP burst
        default: ow_next_addr = i_curr_addr + increment; // Default to INCR burst
    endcase
end

endmodule : axi_gen_addr

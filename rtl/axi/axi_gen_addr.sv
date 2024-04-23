`timescale 1ns / 1ps

module axi_gen_addr
#(
    parameter int AW    = 32,
    parameter int DW    = 32,
    parameter int LEN   = 8
)(
    input  logic [AW-1:0]       i_curr_addr,
    input  logic [2:0]          i_size,
    input  logic [1:0]          i_burst,
    input  logic [LEN-1:0]      i_len,
    output logic [AW-1:0]       ow_next_addr
);

localparam int NumBytes = DW / 8;
logic [AW-1:0] increment;
logic [AW-1:0] wrap_boundary;

always_comb begin
    case (i_size)
        3'b000:  increment = NumBytes;       // 1 byte
        3'b001:  increment = NumBytes << 1;  // 2 bytes
        3'b010:  increment = NumBytes << 2;  // 4 bytes
        3'b011:  increment = NumBytes << 3;  // 8 bytes
        3'b100:  increment = NumBytes << 4;  // 16 bytes
        3'b101:  increment = NumBytes << 5;  // 32 bytes
        3'b110:  increment = NumBytes << 6;  // 64 bytes
        3'b111:  increment = NumBytes << 7;  // 128 bytes
        default: increment = NumBytes;       // Default to 1 byte
    endcase
end

always_comb begin
    case (i_burst)
        2'b00: ow_next_addr = i_curr_addr; // FIXED burst
        2'b01: ow_next_addr = i_curr_addr + increment; // INCR burst
        2'b10: begin  // WRAP burst
            wrap_boundary = (i_curr_addr & ~(increment - 1)) + (i_len << i_size);
            if ((i_curr_addr + increment) >= wrap_boundary) begin
                ow_next_addr = wrap_boundary - increment;
            end else begin
                ow_next_addr = i_curr_addr + increment;
            end
        end
        default: ow_next_addr = i_curr_addr + increment; // Default to INCR burst
    endcase
end

endmodule : axi_gen_addr

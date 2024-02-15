module bram #(
    parameter int RAM_WIDTH = 8,
    parameter int RAM_ADDR_BITS = 13,
    parameter reg [7:0] FILENAME [0:255] = "" // verilog_lint: waive unpacked-dimensions-range-ordering
) (
    input  logic                     clk,
    input  logic                     write_enable,
    input  logic [RAM_ADDR_BITS-1:0] address,
    input  logic [    RAM_WIDTH-1:0] write_data,
    input  logic                     read_enable,
    output logic [    RAM_WIDTH-1:0] read_data
);

    function automatic integer get_string_length;
        input reg [7:0] str[];
        integer i;
        integer length;
        begin
            length = 0;
            for (i = 0; i < $size(str); i = i + 1) begin
                if (str[i] == 8'h00) begin
                    break;
                end
                length = length + 1;
            end
            get_string_length = length;
        end
    endfunction

    (* RAM_STYLE="BLOCK" *)
    logic [RAM_WIDTH-1:0] bram [0:(2**RAM_ADDR_BITS)-1]; // verilog_lint: waive unpacked-dimensions-range-ordering

    int string_length;
    initial begin
        string_length = get_string_length(FILENAME);
        if (string_length > 0) $readmemh(FILENAME, bram, 0, (2 ** RAM_ADDR_BITS) - 1);
    end

    always @(posedge clk) begin
        if (write_enable) bram[address] <= write_data;
        if (read_enable) read_data <= bram[address];
    end

endmodule

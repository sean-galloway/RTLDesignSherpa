module iverilog_dump();
initial begin
    $dumpfile("math_adder_kogge_stone_nbit.fst");
    $dumpvars(0, math_adder_kogge_stone_nbit);
end
endmodule

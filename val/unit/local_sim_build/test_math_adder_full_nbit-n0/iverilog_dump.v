module iverilog_dump();
initial begin
    $dumpfile("math_adder_full_nbit.fst");
    $dumpvars(0, math_adder_full_nbit);
end
endmodule

module iverilog_dump();
initial begin
    $dumpfile("math_adder_half.fst");
    $dumpvars(0, math_adder_half);
end
endmodule

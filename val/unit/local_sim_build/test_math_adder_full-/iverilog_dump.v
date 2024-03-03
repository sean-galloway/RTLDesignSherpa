module iverilog_dump();
initial begin
    $dumpfile("math_adder_full.fst");
    $dumpvars(0, math_adder_full);
end
endmodule

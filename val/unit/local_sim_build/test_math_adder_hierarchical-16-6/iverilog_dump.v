module iverilog_dump();
initial begin
    $dumpfile("math_adder_hierarchical.fst");
    $dumpvars(0, math_adder_hierarchical);
end
endmodule

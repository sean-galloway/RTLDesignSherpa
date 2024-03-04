module iverilog_dump();
initial begin
    $dumpfile("math_multiplier_booths.fst");
    $dumpvars(0, math_multiplier_booths);
end
endmodule

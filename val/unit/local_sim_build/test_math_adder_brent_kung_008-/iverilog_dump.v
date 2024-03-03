module iverilog_dump();
initial begin
    $dumpfile("math_adder_brent_kung_008.fst");
    $dumpvars(0, math_adder_brent_kung_008);
end
endmodule

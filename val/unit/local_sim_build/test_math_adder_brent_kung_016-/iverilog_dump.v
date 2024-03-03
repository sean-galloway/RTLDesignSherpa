module iverilog_dump();
initial begin
    $dumpfile("math_adder_brent_kung_016.fst");
    $dumpvars(0, math_adder_brent_kung_016);
end
endmodule

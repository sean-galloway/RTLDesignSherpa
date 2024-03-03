module iverilog_dump();
initial begin
    $dumpfile("leading_one_trailing_one.fst");
    $dumpvars(0, leading_one_trailing_one);
end
endmodule

module iverilog_dump();
initial begin
    $dumpfile("bin_to_bcd.fst");
    $dumpvars(0, bin_to_bcd);
end
endmodule

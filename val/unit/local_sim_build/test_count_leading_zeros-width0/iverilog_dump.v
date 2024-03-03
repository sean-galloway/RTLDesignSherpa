module iverilog_dump();
initial begin
    $dumpfile("count_leading_zeros.fst");
    $dumpvars(0, count_leading_zeros);
end
endmodule

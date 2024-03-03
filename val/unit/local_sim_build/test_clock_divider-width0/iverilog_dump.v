module iverilog_dump();
initial begin
    $dumpfile("clock_divider.fst");
    $dumpvars(0, clock_divider);
end
endmodule

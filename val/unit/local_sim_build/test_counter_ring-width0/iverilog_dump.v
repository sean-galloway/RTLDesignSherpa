module iverilog_dump();
initial begin
    $dumpfile("counter_ring.fst");
    $dumpvars(0, counter_ring);
end
endmodule

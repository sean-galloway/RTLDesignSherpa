module iverilog_dump();
initial begin
    $dumpfile("fifo_sync.fst");
    $dumpvars(0, fifo_sync);
end
endmodule

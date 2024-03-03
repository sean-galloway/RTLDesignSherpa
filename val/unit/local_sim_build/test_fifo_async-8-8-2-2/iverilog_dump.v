module iverilog_dump();
initial begin
    $dumpfile("fifo_async.fst");
    $dumpvars(0, fifo_async);
end
endmodule

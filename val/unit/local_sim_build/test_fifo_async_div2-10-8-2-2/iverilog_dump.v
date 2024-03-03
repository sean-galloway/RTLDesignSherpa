module iverilog_dump();
initial begin
    $dumpfile("fifo_async_div2.fst");
    $dumpvars(0, fifo_async_div2);
end
endmodule

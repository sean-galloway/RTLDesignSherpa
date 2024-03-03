module iverilog_dump();
initial begin
    $dumpfile("arbiter_round_robin.fst");
    $dumpvars(0, arbiter_round_robin);
end
endmodule

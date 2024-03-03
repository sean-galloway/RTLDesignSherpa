module iverilog_dump();
initial begin
    $dumpfile("arbiter_weighted_round_robin.fst");
    $dumpvars(0, arbiter_weighted_round_robin);
end
endmodule

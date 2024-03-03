module iverilog_dump();
initial begin
    $dumpfile("clock_pulse.fst");
    $dumpvars(0, clock_pulse);
end
endmodule

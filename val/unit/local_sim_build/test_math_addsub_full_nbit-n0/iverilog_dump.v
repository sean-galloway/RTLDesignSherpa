module iverilog_dump();
initial begin
    $dumpfile("math_addsub_full_nbit.fst");
    $dumpvars(0, math_addsub_full_nbit);
end
endmodule

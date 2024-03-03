module iverilog_dump();
initial begin
    $dumpfile("math_divider_srt.fst");
    $dumpvars(0, math_divider_srt);
end
endmodule

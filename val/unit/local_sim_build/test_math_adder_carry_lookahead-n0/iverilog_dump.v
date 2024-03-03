module iverilog_dump();
initial begin
    $dumpfile("math_adder_carry_lookahead.fst");
    $dumpvars(0, math_adder_carry_lookahead);
end
endmodule

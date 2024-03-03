module iverilog_dump();
initial begin
    $dumpfile("math_adder_carry_save_nbit.fst");
    $dumpvars(0, math_adder_carry_save_nbit);
end
endmodule

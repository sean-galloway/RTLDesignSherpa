module iverilog_dump();
initial begin
    $dumpfile("math_adder_carry_save.fst");
    $dumpvars(0, math_adder_carry_save);
end
endmodule

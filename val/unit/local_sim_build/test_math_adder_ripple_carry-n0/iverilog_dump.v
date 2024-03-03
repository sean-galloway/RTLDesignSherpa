module iverilog_dump();
initial begin
    $dumpfile("math_adder_ripple_carry.fst");
    $dumpvars(0, math_adder_ripple_carry);
end
endmodule

module iverilog_dump();
initial begin
    $dumpfile("dataint_parity.fst");
    $dumpvars(0, dataint_parity);
end
endmodule

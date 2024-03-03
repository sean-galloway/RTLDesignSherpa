module iverilog_dump();
initial begin
    $dumpfile("dataint_checksum.fst");
    $dumpvars(0, dataint_checksum);
end
endmodule

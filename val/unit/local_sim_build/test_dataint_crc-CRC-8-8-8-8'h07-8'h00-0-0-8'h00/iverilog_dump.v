module iverilog_dump();
initial begin
    $dumpfile("dataint_crc.fst");
    $dumpvars(0, dataint_crc);
end
endmodule

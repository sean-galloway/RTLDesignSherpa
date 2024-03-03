module iverilog_dump();
initial begin
    $dumpfile("dataint_ecc_hamming_decode_secded.fst");
    $dumpvars(0, dataint_ecc_hamming_decode_secded);
end
endmodule

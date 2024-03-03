module iverilog_dump();
initial begin
    $dumpfile("dataint_ecc_hamming_encode_secded.fst");
    $dumpvars(0, dataint_ecc_hamming_encode_secded);
end
endmodule

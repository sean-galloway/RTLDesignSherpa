module iverilog_dump();
initial begin
    $dumpfile("bin2gray.fst");
    $dumpvars(0, bin2gray);
end
endmodule

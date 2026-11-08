// formal_bank_queue -- mc_bank_queue is a drop-in for gaxi_age_fifo_sync with
// the age column off (memory-controllers MC-010, ISSUE-001 row 2, 2026-11-08).
//
// Both queues get the SAME free stimulus (pushes, pops, payloads; the FIFO's
// age inputs tied off) and every output the store reads must agree, cycle for
// cycle: wr_ready, rd_valid, count, the head payload under rd_valid, and each
// peek's valid and payload under its valid. The environment honours both
// handshakes (a push only when both are ready, a pop only when both are
// valid) -- the two readies / valids are themselves asserted equal, so the
// gate is not weakening the check. Lockstep equivalence from reset is what
// "drop-in" means here; nothing about the FIFO's internals is assumed.
//
// YOSYS-COMPATIBLE FORM: both DUTs pre-flattened by sv2v; immediate assertions.
module formal_bank_queue #(
    parameter int DW    = 4,
    parameter int DEPTH = 8,
    parameter int PEEK  = 2
) (
    input logic aclk
);
    localparam int AW  = $clog2(DEPTH);
    localparam int PKN = (PEEK > 0) ? PEEK : 1;

    (* anyseq *) reg          wr_valid, rd_ready;
    (* anyseq *) reg [DW-1:0] wr_data;
    reg aresetn;

    wire          f_wr_ready, q_wr_ready, f_rd_valid, q_rd_valid;
    wire [AW:0]   f_count, q_count;
    wire [DW-1:0] f_rd_data, q_rd_data;
    // sv2v flattens the unpacked peek ports: valid k is bit k of a [0:PKN-1]
    // vector, payload k is the chunk ((PKN-1)-k)*DW +: DW (read off the flat)
    wire [0:PKN-1]     f_pk_valid, q_pk_valid, f_pk_thr;
    wire [PKN*DW-1:0]  f_pk_data,  q_pk_data;
    wire [7:0]    f_youngest, f_rd_age;   // unused age outputs of the reference
    wire          f_rd_thr;

    // the environment pushes only when BOTH can take it and pops only when
    // BOTH have a head; the asserts below say the two never disagree anyway
    wire w_push = wr_valid && f_wr_ready && q_wr_ready;
    wire w_pop  = rd_ready && f_rd_valid && q_rd_valid;

    gaxi_age_fifo_sync #(.DATA_WIDTH(DW), .AGE_WIDTH(8), .DEPTH(DEPTH), .PEEK(PEEK)) u_ref (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .age_dec(1'b0),
        .wr_valid(w_push), .wr_ready(f_wr_ready), .wr_data(wr_data), .wr_data_age(8'd0),
        .rd_ready(w_pop), .count(f_count), .youngest(f_youngest),
        .rd_valid(f_rd_valid), .rd_data(f_rd_data), .rd_data_age(f_rd_age), .rd_age_thresh(f_rd_thr),
        .pk_valid(f_pk_valid), .pk_data(f_pk_data), .pk_age_thresh(f_pk_thr)
    );
    mc_bank_queue #(.DATA_WIDTH(DW), .DEPTH(DEPTH), .PEEK(PEEK)) u_dut (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(w_push), .wr_ready(q_wr_ready), .wr_data(wr_data),
        .rd_ready(w_pop), .count(q_count),
        .rd_valid(q_rd_valid), .rd_data(q_rd_data),
        .pk_valid(q_pk_valid), .pk_data(q_pk_data)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge aclk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial aresetn = 1'b0;
    always @(posedge aclk) if (f_past_valid >= 2) aresetn <= 1'b1;

    always @(posedge aclk) if (aresetn && f_past_valid >= 3) begin
        a_wr_ready: assert (q_wr_ready == f_wr_ready);
        a_rd_valid: assert (q_rd_valid == f_rd_valid);
        // count is NOT compared: gaxi_age_fifo_sync (REGISTERED = 0) exports the
        // NEXT-pointer count, this module the registered one, and
        // mc_bank_fifo_store leaves the port unconnected on both.
        if (f_rd_valid) a_head: assert (q_rd_data == f_rd_data);
    end
    genvar k;
    generate for (k = 0; k < PKN; k = k + 1) begin : g_pk
        always @(posedge aclk) if (aresetn && f_past_valid >= 3) begin
            // unlabeled: yosys gives every iteration's labelled assert the same cell name
            assert (q_pk_valid[k] == f_pk_valid[k]);
            if (f_pk_valid[k]) assert (q_pk_data[((PKN-1)-k)*DW +: DW] == f_pk_data[((PKN-1)-k)*DW +: DW]);
        end
    end endgenerate

    // the interesting shapes are reachable: full, a pop that refills the
    // shift register from the memory, a push and pop in one cycle, and the
    // last peek valid
    always @(posedge aclk) if (aresetn) begin
        c_full:      cover (f_count == DEPTH[AW:0]);
        c_push_pop:  cover (w_push && w_pop);
        c_refill:    cover (w_pop && (f_count > (PKN + 1)));
        c_last_peek: cover (f_pk_valid[PKN-1] && w_pop);
        c_drained:   cover (f_past_valid > 10 && f_count == 0 && !w_push);
    end
endmodule

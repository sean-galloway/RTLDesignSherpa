// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for ioapic_msi_emit -- the MSI delivery companion (RLB-008).
//
// The whole contract is a FORMAT MAPPING and it is entirely port-visible: this
// module is combinational, has no submodules, and holds no state. That makes it
// close to an ideal formal target, and it is why DEPS is empty -- pulling in
// apb4_master_stub's closure would prove the MASTER, not the emitter.
//
// THE PACKING IS RESTATED INDEPENDENTLY, NOT COPIED. sv2v folds the DUT's
// separate last/first/pwrite bits into a literal 3'b111. If this harness
// restated the DUT's own expression it would agree with itself and prove
// nothing -- the tautology that let the old block_ready property ship a wedge.
// So f_cmd_expected below is built from the SPEC (last, first, pwrite, pprot,
// full strobe, addr, data), and a wrong field order fails.
//
//   P1  the destination lands at address[19:12]
//   P2  the vector lands at data[7:0]
//   P3  the delivery mode lands at data[10:8], forwarded unmodified
//   P4  the destination mode lands at data[11]
//   P5  cmd_data field order matches what apb4_master_stub unpacks
//   P6  the write is a write, one beat, full strobe
//   P7  cmd_valid tracks deliv_valid; deliv_ready tracks cmd_ready
//   P8  rsp_ready is never low -- a posted write's status must not back up
//   P9  deliv_retry iff the response says PSLVERR
//
// P9 rests on rsp_data[DATA_WIDTH] being the pslverr bit of
// {last, first, pslverr, prdata} (apb4_master_stub.sv:149). That single index
// is the most error-prone line in the module and M2 below breaks it.

module formal_ioapic_msi_emit (
    input logic clk,
    input logic rst_n
);

    localparam int AW  = 32;
    localparam int DW  = 32;
    localparam int SW  = DW / 8;
    localparam int CPW = AW + DW + SW + 6;
    localparam int RPW = DW + 3;

    (* anyseq *) reg          deliv_valid;
    (* anyseq *) reg [7:0]    deliv_vector;
    (* anyseq *) reg [7:0]    deliv_dest;
    (* anyseq *) reg          deliv_dest_mode;
    (* anyseq *) reg [2:0]    deliv_deliv_mode;
    (* anyseq *) reg [AW-1:0] msi_addr_base;
    (* anyseq *) reg [DW-1:0] msi_data_template;
    (* anyseq *) reg          cmd_ready;
    (* anyseq *) reg          rsp_valid;
    (* anyseq *) reg [RPW-1:0] rsp_data;

    wire           deliv_ready;
    wire           deliv_retry;
    wire           cmd_valid;
    wire [CPW-1:0] cmd_data;
    wire           rsp_ready;

    ioapic_msi_emit #(.ADDR_WIDTH(AW), .DATA_WIDTH(DW)) dut (
        .deliv_valid       (deliv_valid),
        .deliv_vector      (deliv_vector),
        .deliv_dest        (deliv_dest),
        .deliv_dest_mode   (deliv_dest_mode),
        .deliv_deliv_mode  (deliv_deliv_mode),
        .deliv_ready       (deliv_ready),
        .deliv_retry       (deliv_retry),
        .msi_addr_base     (msi_addr_base),
        .msi_data_template (msi_data_template),
        .cmd_valid         (cmd_valid),
        .cmd_ready         (cmd_ready),
        .cmd_data          (cmd_data),
        .rsp_valid         (rsp_valid),
        .rsp_ready         (rsp_ready),
        .rsp_data          (rsp_data)
    );

    // The expected message, built from the SPEC rather than from the DUT.
    wire [AW-1:0] f_addr = {msi_addr_base[AW-1:20], deliv_dest, msi_addr_base[11:0]};
    wire [DW-1:0] f_data = {msi_data_template[DW-1:12], deliv_dest_mode,
                            deliv_deliv_mode, deliv_vector};
    wire [CPW-1:0] f_cmd_expected = {1'b1,            // last
                                     1'b1,            // first
                                     1'b1,            // pwrite
                                     3'b010,          // pprot
                                     {SW{1'b1}},      // full strobe
                                     f_addr,
                                     f_data};

    // The field slices, named for legibility in a counterexample.
    wire [AW-1:0] f_cmd_addr = cmd_data[DW +: AW];
    wire [DW-1:0] f_cmd_data = cmd_data[0 +: DW];

    always @(posedge clk) begin
        if (rst_n) begin
            ap_addr_dest:   assert (f_cmd_addr[19:12] == deliv_dest);          // P1
            ap_data_vector: assert (f_cmd_data[7:0]   == deliv_vector);        // P2
            ap_data_mode:   assert (f_cmd_data[10:8]  == deliv_deliv_mode);    // P3
            ap_data_destmd: assert (f_cmd_data[11]    == deliv_dest_mode);     // P4
            ap_cmd_packing: assert (cmd_data == f_cmd_expected);               // P5, P6
            ap_valid_track: assert (cmd_valid  == deliv_valid);                // P7
            ap_ready_track: assert (deliv_ready == cmd_ready);                 // P7
            ap_rsp_ready:   assert (rsp_ready);                                // P8
            ap_retry_iff:   assert (deliv_retry == (rsp_valid && rsp_data[DW])); // P9
        end
    end

    // Reachability: without these the asserts can pass vacuously.
    always @(posedge clk) begin
        if (rst_n) begin
            cp_emit:        cover (deliv_valid && cmd_valid && cmd_ready);
            cp_retry:       cover (deliv_retry);
            cp_accept:      cover (rsp_valid && !rsp_data[DW] && !deliv_retry);
            cp_logical:     cover (deliv_valid && deliv_dest_mode && cmd_ready);
            cp_lowestpri:   cover (deliv_valid && deliv_deliv_mode == 3'b001);
        end
    end

endmodule

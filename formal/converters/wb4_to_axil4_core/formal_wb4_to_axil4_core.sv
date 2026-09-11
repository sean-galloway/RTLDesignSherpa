// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal harness for wb4_to_axil4_core: Wishbone command/response queues to
// the AXI4-Lite channels. The in-RTL `ifdef FORMAL` assertions ride along
// through sv2v --define=FORMAL; this file adds the port-level contract with
// a free FUB and a free AXI slave.
//
//   P1: a write takes AW and W in the SAME clock, never one alone
//   P2: a command becomes a write or a read, never both
//   P3: the response consumed is the HEAD's channel -- this is the ordering
//       guarantee, the reason the block exists: B4 terminates in issue order
//       while AXI4-Lite's B and R are independent
//   P4: open commands never exceed OUTSTANDING
//   P5: OKAY becomes ACK, any error response becomes ERR, and RTY is never
//       produced (an AXI slave cannot ask for a retry)
//
// Covers: a write issued, a read issued, a write retiring, a read retiring,
// an error termination, and the queue full.

module formal_wb4_to_axil4_core #(
    parameter int OUTSTANDING = 2
) (
    input logic clk,
    input logic rst_n
);
    localparam int AW = 8;
    localparam int DW = 16;
    localparam int SW = DW / 8;

    (* anyseq *) reg           cmd_valid, cmd_we, rsp_ready;
    (* anyseq *) reg [AW-1:0]  cmd_adr;
    (* anyseq *) reg [DW-1:0]  cmd_dat;
    (* anyseq *) reg [SW-1:0]  cmd_sel;
    (* anyseq *) reg           fub_awready, fub_wready, fub_bvalid, fub_arready, fub_rvalid;
    (* anyseq *) reg [1:0]     fub_bresp, fub_rresp;
    (* anyseq *) reg [DW-1:0]  fub_rdata;

    wire          cmd_ready, rsp_valid;
    wire [1:0]    rsp_status;
    wire [DW-1:0] rsp_dat;
    wire [AW-1:0] fub_awaddr, fub_araddr;
    wire [2:0]    fub_awprot, fub_arprot;
    wire          fub_awvalid, fub_wvalid, fub_bready, fub_arvalid, fub_rready;
    wire [DW-1:0] fub_wdata;
    wire [SW-1:0] fub_wstrb;

    wb4_to_axil4_core #(.ADDR_WIDTH (AW), .DATA_WIDTH (DW), .OUTSTANDING (OUTSTANDING)) dut (
        .aclk (clk), .aresetn (rst_n),
        .cmd_valid (cmd_valid), .cmd_ready (cmd_ready), .cmd_we (cmd_we),
        .cmd_adr (cmd_adr), .cmd_dat (cmd_dat), .cmd_sel (cmd_sel),
        .rsp_valid (rsp_valid), .rsp_ready (rsp_ready), .rsp_status (rsp_status), .rsp_dat (rsp_dat),
        .fub_awaddr (fub_awaddr), .fub_awprot (fub_awprot), .fub_awvalid (fub_awvalid), .fub_awready (fub_awready),
        .fub_wdata (fub_wdata), .fub_wstrb (fub_wstrb), .fub_wvalid (fub_wvalid), .fub_wready (fub_wready),
        .fub_bresp (fub_bresp), .fub_bvalid (fub_bvalid), .fub_bready (fub_bready),
        .fub_araddr (fub_araddr), .fub_arprot (fub_arprot), .fub_arvalid (fub_arvalid), .fub_arready (fub_arready),
        .fub_rdata (fub_rdata), .fub_rresp (fub_rresp), .fub_rvalid (fub_rvalid), .fub_rready (fub_rready)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // The FUB holds a command until taken.
    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n))
        if ($past(cmd_valid && !cmd_ready)) begin
            assume (cmd_valid);
            assume ($stable(cmd_we) && $stable(cmd_adr) && $stable(cmd_dat) && $stable(cmd_sel));
        end

    // A well-behaved AXI slave answers only what it was given, and holds a
    // response until taken.
    wire f_wr_go = fub_awvalid && fub_awready && fub_wvalid && fub_wready;
    wire f_rd_go = fub_arvalid && fub_arready;
    reg [7:0] f_wr_open, f_rd_open;
    always @(posedge clk) if (!rst_n) begin f_wr_open <= 0; f_rd_open <= 0; end
        else begin
            f_wr_open <= f_wr_open + f_wr_go - (fub_bvalid && fub_bready);
            f_rd_open <= f_rd_open + f_rd_go - (fub_rvalid && fub_rready);
        end
    always @(*) if (rst_n) begin
        if (f_wr_open == 0) assume (!fub_bvalid);
        if (f_rd_open == 0) assume (!fub_rvalid);
    end
    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
        if ($past(fub_bvalid && !fub_bready)) assume (fub_bvalid && $stable(fub_bresp));
        if ($past(fub_rvalid && !fub_rready)) assume (fub_rvalid && $stable(fub_rresp) && $stable(fub_rdata));
    end

    wire f_issue  = cmd_valid && cmd_ready;
    wire f_retire = rsp_valid && rsp_ready;
    reg [7:0] f_open;
    always @(posedge clk) if (!rst_n) f_open <= 0; else f_open <= f_open + f_issue - f_retire;

    // Direction of each open command, in issue order: the reference model the
    // ordering property is checked against.
    reg [OUTSTANDING-1:0] f_dir;
    reg [7:0] f_head, f_tail;
    always @(posedge clk)
        if (!rst_n) begin f_head <= 0; f_tail <= 0; end
        else begin
            if (f_issue) begin
                f_dir[f_tail[$clog2(OUTSTANDING)-1:0]] <= cmd_we;
                f_tail <= (f_tail == OUTSTANDING-1) ? 0 : f_tail + 1;
            end
            if (f_retire) f_head <= (f_head == OUTSTANDING-1) ? 0 : f_head + 1;
        end

    always @(posedge clk) if (rst_n) begin
        // P1 / P2
        ap_write_pairs:   assert (!(fub_awvalid && fub_awready) || (fub_wvalid && fub_wready));
        ap_write_pairs2:  assert (!(fub_wvalid && fub_wready) || (fub_awvalid && fub_awready));
        ap_one_direction: assert (!(f_wr_go && f_rd_go));
        // P3: only the head's channel is consumed, and it is the head's direction
        ap_one_channel:   assert (!(fub_bready && fub_rready));
        ap_in_order:      assert (!f_retire || (fub_bready == f_dir[f_head[$clog2(OUTSTANDING)-1:0]]));
        // P4
        ap_open_bound:    assert (f_open <= OUTSTANDING);
        ap_rsp_when_open: assert (!rsp_valid || f_open != 0);
        // A presented termination must be BACKED by a real response on the
        // head's own channel. Without this, a block that asserted rsp_valid
        // whenever EITHER channel had a response would still satisfy every
        // ordering property above while returning a status and data read off
        // a channel that has nothing -- caught by mutation, not by review.
        ap_rsp_backed:    assert (!rsp_valid || f_open == 0 ||
                                  (f_dir[f_head[$clog2(OUTSTANDING)-1:0]] ? fub_bvalid : fub_rvalid));
        // P5
        ap_no_rty:        assert (!rsp_valid || rsp_status != 2'd2);
        // Take the direction from the MODEL's head, not from fub_bready:
        // bready only asserts in the retire clock, while rsp_status is live
        // whenever rsp_valid is.
        ap_status_map:    assert (!rsp_valid || f_open == 0 ||
                                  (rsp_status == (((f_dir[f_head[$clog2(OUTSTANDING)-1:0]]
                                                    ? fub_bresp : fub_rresp) == 2'b00) ? 2'd0 : 2'd1)));
    end

    always @(posedge clk) if (rst_n) begin
        cp_write_issued: cover (f_wr_go);
        cp_read_issued:  cover (f_rd_go);
        cp_write_retire: cover (f_retire && fub_bready);
        cp_read_retire:  cover (f_retire && fub_rready);
        cp_err:          cover (f_retire && rsp_status == 2'd1);
        cp_full:         cover (f_open == OUTSTANDING);
    end
endmodule

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal harness for axil4_to_wb4_core: AXI4-Lite channel set -> Wishbone
// command/response queues. The in-RTL `ifdef FORMAL` assertions ride along
// through sv2v --define=FORMAL; this file adds the port-level contract:
//
//   P1: a command is issued only when a request is present (AW+W or AR)
//   P2: the command carries the right direction/address for the channel
//       it took (write: cmd_we, AW address, W strobes; read: !cmd_we, AR
//       address, all selects)
//   P3: B and R never fire together; a response is consumed only by the
//       channel it belongs to (rsp_ready follows bready/rready of that side)
//   P4: outstanding count (issued - responded) never exceeds SIDE_DEPTH,
//       and B/R count exactly the responses consumed with something open
//   P5: AXI-side response codes: OKAY only for ACK, SLVERR for ERR,
//       RTY_RESP for RTY
//
// Covers: write issued, read issued, alternation (write then read when
// both are pending), B with SLVERR, R with data, side queue full.

module formal_axil4_to_wb4_core (
    input logic clk,
    input logic rst_n
);
    localparam int AW = 8;
    localparam int DW = 32;
    localparam int SW = DW / 8;
    localparam int SIDE_DEPTH = 4;
    localparam logic [1:0] RTY_RESP = 2'b11;

    (* anyseq *) reg [AW-1:0]  fub_awaddr;
    (* anyseq *) reg [2:0]     fub_awprot;
    (* anyseq *) reg           fub_awvalid;
    (* anyseq *) reg [DW-1:0]  fub_wdata;
    (* anyseq *) reg [SW-1:0]  fub_wstrb;
    (* anyseq *) reg           fub_wvalid;
    (* anyseq *) reg           fub_bready;
    (* anyseq *) reg [AW-1:0]  fub_araddr;
    (* anyseq *) reg [2:0]     fub_arprot;
    (* anyseq *) reg           fub_arvalid;
    (* anyseq *) reg           fub_rready;
    (* anyseq *) reg           cmd_ready;
    (* anyseq *) reg           rsp_valid;
    (* anyseq *) reg [1:0]     rsp_status;
    (* anyseq *) reg [DW-1:0]  rsp_dat;

    wire           fub_awready, fub_wready, fub_bvalid, fub_arready, fub_rvalid;
    wire [1:0]     fub_bresp, fub_rresp;
    wire [DW-1:0]  fub_rdata;
    wire           cmd_valid, cmd_we, rsp_ready;
    wire [AW-1:0]  cmd_adr;
    wire [DW-1:0]  cmd_dat;
    wire [SW-1:0]  cmd_sel;

    axil4_to_wb4_core #(
        .ADDR_WIDTH (AW), .DATA_WIDTH (DW), .SIDE_DEPTH (SIDE_DEPTH), .RTY_RESP (RTY_RESP)
    ) dut (
        .aclk (clk), .aresetn (rst_n),
        .fub_awaddr (fub_awaddr), .fub_awprot (fub_awprot), .fub_awvalid (fub_awvalid), .fub_awready (fub_awready),
        .fub_wdata (fub_wdata), .fub_wstrb (fub_wstrb), .fub_wvalid (fub_wvalid), .fub_wready (fub_wready),
        .fub_bresp (fub_bresp), .fub_bvalid (fub_bvalid), .fub_bready (fub_bready),
        .fub_araddr (fub_araddr), .fub_arprot (fub_arprot), .fub_arvalid (fub_arvalid), .fub_arready (fub_arready),
        .fub_rdata (fub_rdata), .fub_rresp (fub_rresp), .fub_rvalid (fub_rvalid), .fub_rready (fub_rready),
        .cmd_valid (cmd_valid), .cmd_ready (cmd_ready), .cmd_we (cmd_we), .cmd_adr (cmd_adr),
        .cmd_dat (cmd_dat), .cmd_sel (cmd_sel),
        .rsp_valid (rsp_valid), .rsp_ready (rsp_ready), .rsp_status (rsp_status), .rsp_dat (rsp_dat)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // AXI-Lite: valid held with stable payload until ready (the skids in
    // front of the core guarantee this in the wrapper).
    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
        if ($past(fub_awvalid && !fub_awready)) assume (fub_awvalid && fub_awaddr == $past(fub_awaddr));
        if ($past(fub_wvalid  && !fub_wready))  assume (fub_wvalid && fub_wdata == $past(fub_wdata) && fub_wstrb == $past(fub_wstrb));
        if ($past(fub_arvalid && !fub_arready)) assume (fub_arvalid && fub_araddr == $past(fub_araddr));
        if ($past(rsp_valid   && !rsp_ready))   assume (rsp_valid && rsp_status == $past(rsp_status));
    end

    wire f_issue  = cmd_valid && cmd_ready;
    wire f_b_hs   = fub_bvalid && fub_bready;
    wire f_r_hs   = fub_rvalid && fub_rready;
    wire f_rsp_hs = rsp_valid && rsp_ready;

    // Outstanding = issued - answered through B/R (port-level model)
    reg [7:0] f_open;
    initial f_open = 0;
    always @(posedge clk)
        if (!rst_n) f_open <= 0;
        else        f_open <= f_open + f_issue - (f_b_hs || f_r_hs);

    always @(posedge clk) if (rst_n) begin
        // P1 / P2: issue only with a request; payload from the channel taken
        ap_issue_has_request: assert (!cmd_valid || (fub_awvalid && fub_wvalid) || fub_arvalid);
        ap_write_payload:     assert (!(f_issue && cmd_we) || (fub_awready && fub_wready && !fub_arready &&
                                      cmd_adr == fub_awaddr && cmd_dat == fub_wdata && cmd_sel == fub_wstrb));
        ap_read_payload:      assert (!(f_issue && !cmd_we) || (fub_arready && !fub_awready && !fub_wready &&
                                      cmd_adr == fub_araddr && cmd_sel == {SW{1'b1}}));
        ap_ready_only_on_issue: assert (!(fub_awready || fub_wready || fub_arready) || f_issue);
        // P3
        ap_b_r_exclusive:     assert (!(fub_bvalid && fub_rvalid));
        ap_b_consumes:        assert (!f_b_hs || f_rsp_hs);
        ap_r_consumes:        assert (!f_r_hs || f_rsp_hs);
        ap_rsp_needs_channel: assert (!(f_rsp_hs && f_open != 0) || f_b_hs || f_r_hs);
        // P4
        ap_open_bound:        assert (f_open <= SIDE_DEPTH);
        ap_no_response_when_none_open: assert (!(fub_bvalid || fub_rvalid) || f_open != 0);
        // P5
        ap_b_code: assert (!fub_bvalid || fub_bresp == (rsp_status == 2'd1 ? 2'b10 : rsp_status == 2'd2 ? RTY_RESP : 2'b00));
        ap_r_code: assert (!fub_rvalid || fub_rresp == (rsp_status == 2'd1 ? 2'b10 : rsp_status == 2'd2 ? RTY_RESP : 2'b00));
        ap_r_data: assert (!fub_rvalid || fub_rdata == rsp_dat);
    end

    // Direction of every open transfer, in issue order (mirror of the side queue)
    reg [SIDE_DEPTH-1:0] f_dir;
    reg [7:0] f_head, f_tail;
    initial begin f_dir = 0; f_head = 0; f_tail = 0; end
    always @(posedge clk)
        if (!rst_n) begin f_head <= 0; f_tail <= 0; end
        else begin
            if (f_issue) begin f_dir[f_tail[1:0]] <= cmd_we; f_tail <= (f_tail == SIDE_DEPTH-1) ? 0 : f_tail + 1; end
            if (f_b_hs || f_r_hs) f_head <= (f_head == SIDE_DEPTH-1) ? 0 : f_head + 1;
        end
    always @(posedge clk) if (rst_n && f_open != 0) begin
        ap_direction: assert (!(fub_bvalid || fub_rvalid) || (fub_bvalid == f_dir[f_head[1:0]]));
    end

    // Alternation: a write issued right after a read while both were pending
    reg f_last_wr;
    initial f_last_wr = 0;
    always @(posedge clk) if (rst_n && f_issue) f_last_wr <= cmd_we;
    always @(posedge clk) if (rst_n && f_past_valid > 1 && $past(rst_n)) begin
        ap_no_starve: assert (!(f_issue && fub_awvalid && fub_wvalid && fub_arvalid) || (cmd_we != f_last_wr));
    end

    always @(posedge clk) if (rst_n) begin
        cp_write_issued: cover (f_issue && cmd_we);
        cp_read_issued:  cover (f_issue && !cmd_we);
        cp_alternate:    cover (f_issue && fub_awvalid && fub_wvalid && fub_arvalid && f_last_wr && !cmd_we);
        cp_b_slverr:     cover (f_b_hs && fub_bresp == 2'b10);
        cp_r_rty:        cover (f_r_hs && fub_rresp == RTY_RESP);
        cp_r_ok:         cover (f_r_hs && fub_rresp == 2'b00);
        cp_side_full:    cover (f_open == SIDE_DEPTH);
        cp_drained:      cover (f_past_valid > 6 && f_open == 0 && f_last_wr);
    end
endmodule

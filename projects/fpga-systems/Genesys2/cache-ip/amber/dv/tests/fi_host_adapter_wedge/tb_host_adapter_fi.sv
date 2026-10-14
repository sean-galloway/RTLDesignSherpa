// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Fault-injection repro for the Genesys2 board-only read hang (amber G2
// bring-up, 2026-10). Standalone Icarus TB around the generated
// host_adapter (the uart-bridge -> xbar adapter in bridge_amber_axil).
//
// Question being answered: "if you know the scenario, why can't you
// recreate it in sim?"
//
//   Phase 1: with the AR tracker deposited into its FULL encoding (the
//            state the board is stuck in: ar_trk_full=1 with no reads in
//            flight), the FIRST read after reset wedges with exactly the
//            board's ILA signature. That state is NOT reachable by any
//            legal transition from reset -- the push/pop discipline keeps
//            wptr-rptr inside [0,DEPTH) -- so no 2-state sim (RTL or
//            gate-level, randomized reset or not) can ever enter it.
//            Silicon entered it via means RTL cannot model (single-event
//            flip / netlist transform); the deposit reproduces the
//            *signature* and proves the locus.
//
//   Phase 2: release the deposit, pulse reset, run legal reads -- the
//            RTL path is clean, matching every sim level (fub/unit/
//            harness) that reported no repro.
//
// Board signature reproduced (ILA round 4, ila_trace.csv):
//   host AR:  arvalid=1 held / arready=0 forever
//   fabric:   host_32b_arvalid=0 (request never forwarded), no R ever
//   static:   all of the above unchanged across the capture window
//   self-sustaining: tracker pop needs an R; R needs a forwarded AR;
//            forwarding needs !full -- deadlock by construction.

`timescale 1ns/1ps

module tb_host_adapter_fi;
    import bridge_amber_axil_pkg::*;

    logic aclk = 1'b0;
    always #5 aclk = ~aclk;
    logic aresetn;

    // --------------------------------------------------------------
    // host-side AXI (external): AR driven by TB, everything else idle
    // --------------------------------------------------------------
    logic [31:0] host_axi_awaddr  = 32'd0;
    logic [2:0]  host_axi_awprot  = 3'd0;
    logic [31:0] host_axi_wdata   = 32'd0;
    logic [3:0]  host_axi_wstrb   = 4'd0;
    logic [31:0] host_axi_araddr  = 32'd0;
    logic [7:0]  host_axi_arlen   = 8'd0;
    logic [2:0]  host_axi_arsize  = 3'd2;
    logic [1:0]  host_axi_arburst = 2'b01;
    logic [3:0]  host_axi_arcache = 4'd0;
    logic [2:0]  host_axi_arprot  = 3'd0;
    logic [3:0]  host_axi_arqos   = 4'd0;
    logic [3:0]  host_axi_arregion= 4'd0;
    logic        host_axi_arvalid = 1'b0;
    logic        host_axi_arready;
    logic        host_axi_rid;
    logic [31:0] host_axi_rdata;
    logic [1:0]  host_axi_rresp;
    logic        host_axi_rlast;
    logic        host_axi_ruser;
    logic        host_axi_rvalid;
    logic        host_axi_rready  = 1'b1;

    logic [6:0]  slave_select_aw, slave_select_ar;
    logic        bridge_id_aw, bridge_id_ar;

    // --------------------------------------------------------------
    // 32b fabric side: minimal AXI slave model (AR accept + 1-beat R)
    // --------------------------------------------------------------
    axi4_aw_t    host_32b_aw;
    logic        host_32b_awvalid, host_32b_awready;
    axi4_w_32b_t host_32b_w;
    logic        host_32b_wvalid,  host_32b_wready;
    axi4_b_t     host_32b_b;
    logic        host_32b_bvalid,  host_32b_bready;
    axi4_ar_t    host_32b_ar;
    logic        host_32b_arvalid, host_32b_arready;
    axi4_r_32b_t host_32b_r;
    logic        host_32b_rvalid,  host_32b_rready;

    // 64b side tied idle
    axi4_aw_t    host_64b_aw;
    logic        host_64b_awvalid, host_64b_awready = 1'b0;
    axi4_w_64b_t host_64b_w;
    logic        host_64b_wvalid,  host_64b_wready  = 1'b0;
    axi4_b_t     host_64b_b;
    logic        host_64b_bvalid  = 1'b0, host_64b_bready;
    axi4_ar_t    host_64b_ar;
    logic        host_64b_arvalid, host_64b_arready = 1'b0;
    axi4_r_64b_t host_64b_r;
    logic        host_64b_rvalid  = 1'b0, host_64b_rready;

    assign host_32b_awready = 1'b0;
    assign host_32b_wready  = 1'b0;
    assign host_32b_bvalid  = 1'b0;
    assign host_32b_b       = '0;
    assign host_32b_arready = 1'b1;   // xbar-side slave always ready
    assign host_64b_r       = '0;

    always @(posedge aclk) begin
        if (!aresetn) begin
            host_32b_rvalid <= 1'b0;
            host_32b_r      <= '0;
        end else begin
            if (host_32b_rvalid && host_32b_rready)
                host_32b_rvalid <= 1'b0;
            if (host_32b_arvalid && host_32b_arready) begin
                host_32b_rvalid   <= 1'b1;
                host_32b_r.id     <= 1'b0;
                host_32b_r.data   <= 32'hA5A5_0000 | host_32b_ar.addr[11:0];
                host_32b_r.resp   <= 2'b00;
                host_32b_r.last   <= 1'b1;
                host_32b_r.user   <= 1'b0;
            end
        end
    end

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------
    host_adapter #(
        .NUM_SLAVES(7),
        .BRIDGE_ID(0),
        .BRIDGE_ID_WIDTH(1)
    ) dut (
        .aclk(aclk),
        .aresetn(aresetn),
        .host_axi_awid(1'b0), .host_axi_awaddr(host_axi_awaddr),
        .host_axi_awlen(8'h0), .host_axi_awsize(3'd2),
        .host_axi_awburst(2'b01), .host_axi_awlock(1'b0),
        .host_axi_awcache(4'h0), .host_axi_awprot(host_axi_awprot),
        .host_axi_awqos(4'h0), .host_axi_awregion(4'h0),
        .host_axi_awuser(1'b0), .host_axi_awvalid(1'b0),
        .host_axi_awready(), .host_axi_wdata(host_axi_wdata),
        .host_axi_wstrb(host_axi_wstrb), .host_axi_wlast(1'b1),
        .host_axi_wuser(1'b0), .host_axi_wvalid(1'b0),
        .host_axi_wready(), .host_axi_bid(), .host_axi_bresp(),
        .host_axi_buser(), .host_axi_bvalid(), .host_axi_bready(1'b0),
        .host_axi_arid(1'b0), .host_axi_araddr(host_axi_araddr),
        .host_axi_arlen(8'h0), .host_axi_arsize(3'd2),
        .host_axi_arburst(2'b01), .host_axi_arlock(1'b0),
        .host_axi_arcache(4'h0), .host_axi_arprot(host_axi_arprot),
        .host_axi_arqos(4'h0), .host_axi_arregion(4'h0),
        .host_axi_aruser(1'b0), .host_axi_arvalid(host_axi_arvalid),
        .host_axi_arready(host_axi_arready), .host_axi_rid(host_axi_rid),
        .host_axi_rdata(host_axi_rdata), .host_axi_rresp(host_axi_rresp),
        .host_axi_rlast(host_axi_rlast), .host_axi_ruser(host_axi_ruser),
        .host_axi_rvalid(host_axi_rvalid),
        .host_axi_rready(host_axi_rready),
        .slave_select_aw(slave_select_aw), .bridge_id_aw(bridge_id_aw),
        .slave_select_ar(slave_select_ar), .bridge_id_ar(bridge_id_ar),
        .host_32b_aw(host_32b_aw), .host_32b_awvalid(), .host_32b_awready(host_32b_awready),
        .host_32b_w(host_32b_w), .host_32b_wvalid(), .host_32b_wready(host_32b_wready),
        .host_32b_b(host_32b_b), .host_32b_bvalid(host_32b_bvalid), .host_32b_bready(),
        .host_32b_ar(host_32b_ar), .host_32b_arvalid(host_32b_arvalid),
        .host_32b_arready(host_32b_arready),
        .host_32b_r(host_32b_r), .host_32b_rvalid(host_32b_rvalid),
        .host_32b_rready(host_32b_rready),
        .host_64b_aw(host_64b_aw), .host_64b_awvalid(), .host_64b_awready(host_64b_awready),
        .host_64b_w(host_64b_w), .host_64b_wvalid(), .host_64b_wready(host_64b_wready),
        .host_64b_b(host_64b_b), .host_64b_bvalid(host_64b_bvalid), .host_64b_bready(),
        .host_64b_ar(host_64b_ar), .host_64b_arvalid(), .host_64b_arready(host_64b_arready),
        .host_64b_r(host_64b_r), .host_64b_rvalid(host_64b_rvalid), .host_64b_rready()
    );

    // --------------------------------------------------------------
    // Stimulus
    // --------------------------------------------------------------
    integer errors = 0;
    integer i, cyc;
    reg [31:0] rdata;
    reg        rok;
    reg [4:0]  wptr_fi;

    task do_read(input [31:0] addr, output [31:0] data, output bit ok);
        integer to;
        begin
            @(negedge aclk);
            host_axi_araddr  = addr;
            host_axi_arvalid = 1'b1;
            ok  = 1'b0;
            to  = 0;
            while (!host_axi_arready && to < 50) begin
                @(posedge aclk); #1; to = to + 1;
            end
            if (host_axi_arready)
                $display("     AR accepted (host side); fub-side push below");
            if (!host_axi_arready) begin
                @(negedge aclk); host_axi_arvalid = 1'b0;
                ok = 1'b0;
                disable do_read;
            end
            @(negedge aclk); host_axi_arvalid = 1'b0;
            to = 0;
            while (!host_axi_rvalid && to < 50) begin
                @(posedge aclk); #1; to = to + 1;
            end
            if (host_axi_rvalid) begin
                data = host_axi_rdata;
                ok   = host_axi_rlast;
            end
            @(negedge aclk);
        end
    endtask

    // True push select: the skid registers AR before the fub-side
    // handshake, so sampling comb_slave_select_ar at the s-side
    // handshake shows stale decode. Monitor the push instead.
    always @(posedge aclk)
        if (aresetn && dut.ar_trk_push)
            $display("     ar_trk_push: select=%b fub_araddr=0x%08x",
                     dut.comb_slave_select_ar, dut.fub_axi_araddr);

    initial begin
        $dumpfile("fi_host_adapter.vcd");
        $dumpvars(0, tb_host_adapter_fi);
        aresetn = 1'b0;
        repeat (6) @(posedge aclk);
        aresetn = 1'b1;
        repeat (4) @(posedge aclk);

        // ---------------- Phase 1: tracker deposited full, first read ----------------
        // rptr is 0 right after reset; full pattern = wptr 16 (MSB set,
        // low bits equal). This is the state the board was captured in.
        wptr_fi = dut.ar_trk_rptr + 5'd16;
        $display("[P1] FI: force dut.ar_trk_wptr = %b (rptr=%b -> ar_trk_full=1)",
                 wptr_fi, dut.ar_trk_rptr);
        force dut.ar_trk_wptr = wptr_fi;
        #1;
        $display("     ar_trk_full=%b ar_gate_ok=%b fub_axi_arready=%b",
                 dut.ar_trk_full, dut.ar_gate_ok, dut.fub_axi_arready);

        do_read(32'h0001_0000, rdata, rok);
        $display("     first read after reset: ok=%0d (0 = never completed)", rok);
        if (rok) begin
            errors = errors + 1;
            $display("     ^^ P1 UNEXPECTED: read completed despite full tracker");
        end

        // Board-signature comparison: re-drive AR and hold it; every
        // cycle must match {arready=0, 32b_arvalid=0, no R, full=1}.
        @(negedge aclk);
        host_axi_araddr  = 32'h0001_0000;
        host_axi_arvalid = 1'b1;
        begin : sig_check
            integer bad;
            bad = 0;
            for (cyc = 0; cyc < 64; cyc = cyc + 1) begin
                @(posedge aclk); #1;
                if (host_axi_arready !== 1'b0)  bad = bad + 1;
                if (host_32b_arvalid !== 1'b0)  bad = bad + 1;
                if (host_axi_rvalid !== 1'b0)   bad = bad + 1;
                if (dut.ar_trk_full !== 1'b1)   bad = bad + 1;
            end
            if (bad == 0) begin
                $display("     64-cycle hold: host_arvalid=1/arready=0, host_32b_arvalid=0,");
                $display("                    rvalid=0, ar_trk_full=1, fub_axi_arready=0");
                $display("     -> IDENTICAL to board ILA signature (static window, no forward, no response)");
            end else begin
                errors = errors + 1;
                $display("     ^^ signature mismatch, %0d violations", bad);
            end
        end

        // Self-sustaining: release the deposit; no legal transition can
        // exit (pop needs fub_axi_rvalid; forward needs !full).
        release dut.ar_trk_wptr;
        for (cyc = 0; cyc < 32; cyc = cyc + 1) begin
            @(posedge aclk); #1;
            if (host_axi_arready !== 1'b0) begin
                errors = errors + 1;
                $display("     ^^ recovered at cyc %0d -- unexpected", cyc);
            end
        end
        $display("     post-release 32-cycle hold: still wedged (deadlock by construction)");
        @(negedge aclk); host_axi_arvalid = 1'b0;

        // ---------------- Phase 2: clean reset, legal reads ----------------
        aresetn = 1'b0;
        repeat (6) @(posedge aclk);
        aresetn = 1'b1;
        repeat (4) @(posedge aclk);
        $display("[P2] clean reset, legal single-beat reads (addr=0x0001_0000, slave 0)");
        for (i = 0; i < 3; i = i + 1) begin
            do_read(32'h0001_0000, rdata, rok);
            $display("     read %0d: ok=%0d data=0x%08x", i, rok, rdata);
            if (!rok || rdata !== 32'hA5A5_0000) begin
                errors = errors + 1;
                $display("     ^^ P2 FAILURE");
            end
        end

        if (errors == 0)
            $display("RESULT: PASS -- board signature reproduced from the unreachable state;");
        else
            $display("RESULT: FAIL -- %0d error(s)", errors);
        $finish;
    end

    // Global watchdog
    initial begin
        #100000;
        $display("RESULT: FAIL -- global timeout");
        $finish;
    end
endmodule

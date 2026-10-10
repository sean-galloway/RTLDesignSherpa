// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal wrapper for amber_control (yosys-compatible)
// Run with: sby amber_control.sby
//
// Task 13 proofs (MAS ch06) at the tiny geometry SETS=16 / WAYS=2 /
// LINE_BYTES=64 / BUS_WIDTH=64:
//   (1) no stale data after an external write -- snoop invalidation lands in
//       the tag store and a CPU lookup can never hit a poisoned line
//       (pending-fill state accuracy included: the grant-cycle CRRESP is
//       checked against the resolved reference state, pf/stale/victim/
//       installed priority, against an independent copy of the HAS Table 3.0
//       decode);
//   (2) no deadlock/livelock under fair arbitration -- every transient state
//       residence and the whole request-to-response path are bounded given
//       the fair constraints (fill/drain done, cdready, snoop spacing +
//       per-transaction snoop cap, CPU request only at IDLE).
//
// Structure: the wrapper top holds the abstract tag-array model (a 16x2
// store, reset to Invalid, applying every port-A write -- an exact model of
// amber_tag_array at this geometry) and the no-stale-data poison check on
// that model. The remaining properties and all environment assumptions live
// in amber_control_props, instantiated at the top and fed by the DUT's
// ports plus 52 internal signals that amber_control.sby exposes as DUT
// output ports (yosys has no hierarchical references and no working bind in
// this build; expose over a parameter-specialized flat is the mechanism --
// see the Task 13 report, Toolchain findings). req_wdata and the port-B
// data-array read are tied off: no property claims data VALUES (the
// victim-CD check keeps port-A read data free because it compares against
// the gathered line).

module formal_amber_control (
    input  logic        clk,
    input  logic        rst_n,

    // CPU frontend (free environment)
    input  logic        req_valid,
    input  logic [31:0] req_addr,
    input  logic        req_we,
    input  logic [7:0]  req_be,
    input  logic [63:0] req_wdata,

    // snoop responder (free environment; amber_snoop_resp contract)
    input  logic        snoop_req,
    input  logic [2:0]  snoop_type,
    input  logic [31:0] snoop_addr,
    input  logic        cdready,

    // replacement engine (free: any victim way is legal)
    input  logic        repl_way,

    // fill / drain partners (free with fair constraints, see props)
    input  logic        fill_done,
    input  logic        fill_beat_valid,
    input  logic [2:0]  fill_beat_idx,
    input  logic        drain_done,

    // data-array read data (free; state proofs never depend on data values)
    input  logic [63:0] data_a_rdata,
    input  logic [63:0] data_b_rdata
);

    localparam ADDR_WIDTH = 32;
    localparam SETS       = 16;
    localparam WAYS       = 2;
    localparam LINE_BYTES = 64;
    localparam BUS_WIDTH  = 64;
    localparam SET_INDEX_WIDTH   = 4;
    localparam TAG_WIDTH         = 22;
    localparam TAG_STATE_WIDTH   = 25;
    localparam BEAT_INDEX_WIDTH  = 3;
    localparam WAY_INDEX_WIDTH   = 1;
    localparam MEM_ADDR_WIDTH    = 7;

    // ------------------------------------------------------------------
    // DUT outputs (observed by the wrapper where needed)
    // ------------------------------------------------------------------
    logic        ctrl_req_ready;
    logic        ctrl_rsp_valid;
    logic [63:0] ctrl_rsp_data;
    logic [SET_INDEX_WIDTH-1:0]            ctrl_tag_a_set;
    logic                                  ctrl_tag_a_wr_en;
    logic [WAYS-1:0]                       ctrl_tag_a_wr_way_onehot;
    logic [SET_INDEX_WIDTH-1:0]            ctrl_tag_a_wr_set;
    logic [TAG_STATE_WIDTH-1:0]            ctrl_tag_a_wr_tag_state;
    logic                                  ctrl_tag_b_req;
    logic [SET_INDEX_WIDTH-1:0]            ctrl_tag_b_set;
    logic [MEM_ADDR_WIDTH-1:0]             ctrl_data_a_addr;
    logic [WAY_INDEX_WIDTH-1:0]            ctrl_data_a_way;
    logic                                  ctrl_data_a_wr_en;
    logic [WAYS-1:0]                       ctrl_data_a_wr_way_onehot;
    logic [MEM_ADDR_WIDTH-1:0]             ctrl_data_a_wr_addr;
    logic [BUS_WIDTH-1:0]                  ctrl_data_a_wr_wdata;
    logic [BUS_WIDTH/8-1:0]                ctrl_data_a_wr_be;
    logic [MEM_ADDR_WIDTH-1:0]             ctrl_data_b_addr;
    logic [WAY_INDEX_WIDTH-1:0]            ctrl_data_b_way;
    logic                                  ctrl_repl_req;
    logic                                  ctrl_repl_hit;
    logic                                  ctrl_repl_update;
    logic [WAY_INDEX_WIDTH-1:0]            ctrl_repl_hit_way;
    logic                                  ctrl_victim_load;
    logic [ADDR_WIDTH-1:0]                 ctrl_victim_addr_in;
    logic [LINE_BYTES*8-1:0]               ctrl_victim_data_in;
    logic                                  ctrl_fill_start;
    logic [ADDR_WIDTH-1:0]                 ctrl_fill_addr;
    logic [2:0]                            ctrl_req_class;
    logic                                  ctrl_drain_start;
    logic                                  ctrl_snoop_ready;
    logic [4:0]                            ctrl_crresp;
    logic [BUS_WIDTH-1:0]                  ctrl_cddata;
    logic                                  ctrl_cdlast;
    logic                                  ctrl_cdvalid;
    logic                                  ctrl_init_busy;
    logic [SET_INDEX_WIDTH-1:0]            ctrl_init_set;
    logic [3:0]                            ctrl_state;

    // house reset protocol for the wrapper-side properties
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    // ------------------------------------------------------------------
    // Abstract tag-array model (exact model of amber_tag_array at 16x2):
    // reset to Invalid (matches the DUT init walk's net effect; the walk
    // writes {0, I} everywhere, so applying it is a no-op on the model),
    // every port-A write applied. Read combinationally on both ports.
    // ------------------------------------------------------------------
    logic [WAYS-1:0][TAG_STATE_WIDTH-1:0]  tag_a_tag_state;
    logic [WAYS-1:0][TAG_STATE_WIDTH-1:0]  tag_b_tag_state;

    reg [TAG_STATE_WIDTH-1:0] tag_model [0:SETS*WAYS-1];
    integer mi;
    always @(posedge clk) begin
        if (!rst_n) begin
            for (mi = 0; mi < SETS*WAYS; mi = mi+1)
                tag_model[mi] <= {{TAG_STATE_WIDTH-3{1'b0}}, 3'b000};
        end else if (ctrl_tag_a_wr_en) begin
            for (mi = 0; mi < WAYS; mi = mi+1)
                if (ctrl_tag_a_wr_way_onehot[mi])
                    tag_model[mi*SETS + ctrl_tag_a_wr_set]
                        <= ctrl_tag_a_wr_tag_state;
        end
    end

    genvar gw;
    generate
        for (gw = 0; gw < WAYS; gw = gw+1) begin : g_tag_rd
            assign tag_a_tag_state[gw] = tag_model[gw*SETS + ctrl_tag_a_set];
            assign tag_b_tag_state[gw] = tag_model[gw*SETS + ctrl_tag_b_set];
        end
    endgenerate

    logic [11:0]       obs_state_q;
    logic [4-1:0]      obs_req_set;
    logic [22-1:0]     obs_req_tag;
    logic obs_req_we_q;
    logic [8-1:0]      obs_req_be_q;
    logic [64-1:0]     obs_req_wdata_q;
    logic obs_upgr_q;
    logic [2:0]        obs_hit_state_q;
    logic [1-1:0]      obs_hit_way_q;
    logic [2-1:0]      obs_hit_way_onehot;
    logic [1-1:0]      obs_victim_way_q;
    logic [22-1:0]     obs_victim_tag_q;
    logic [2-1:0]      obs_victim_way_onehot;
    logic obs_victim_valid;
    logic [32-1:0]     obs_victim_buf_addr;
    logic [(64*8)-1:0] obs_victim_buf_data;
    logic [4-1:0]      obs_sn_set_q;
    logic [22-1:0]     obs_sn_hit_tag_q;
    logic [1-1:0]      obs_sn_hit_way_q;
    logic [2-1:0]      obs_sn_hit_way_onehot;
    logic obs_sn_hit_any_q;
    logic obs_sn_pf_q;
    logic obs_sn_stale_q;
    logic obs_sn_victim_q;
    logic obs_sn_upgr_line_q;
    logic [3-1:0]      obs_sn_beat_q;
    logic obs_sn_beat_gated;
    logic obs_sn_complete;
    logic obs_sn_wr_tag;
    logic [2:0]        obs_sn_ref_q;
    logic [2:0]        obs_sn_ref_grant;
    logic [2:0]        obs_sn_type_q;
    logic [2:0]        obs_w_sn_nxt;
    logic obs_sn_pf_gnt_match;
    logic obs_sn_stale_gnt;
    logic obs_sn_upgr_line_gnt;
    logic obs_victim_match;
    logic obs_sn_hit_any;
    logic [2:0]        obs_sn_hit_state;
    logic obs_pf_active;
    logic [26-1:0]     obs_pf_addr;
    logic [2:0]        obs_pf_state;
    logic obs_pf_match;
    logic [8-1:0]      obs_pf_data_valid;
    logic obs_pend_vld_q;
    logic [2:0]        obs_pend_state_q;
    logic [2:0]        obs_install_state_eff;
    logic [11:0]       obs_sn_return_q;
    logic obs_fill_seen_q;
    logic obs_fill_done_q;
    logic obs_drain_seen_q;
    logic obs_drain_done_q;

    // ------------------------------------------------------------------
    // DUT -- instantiated without parameter overrides: the committed flat
    // is pre-specialized to the tiny formal geometry by specialize_params
    // (which also strips the parameter declarations so yosys bind fires).
    // ------------------------------------------------------------------
    amber_control dut (
        .clk                     (clk),
        .rst_n                   (rst_n),
        .req_valid               (req_valid),
        .req_addr                (req_addr),
        .req_we                  (req_we),
        .req_be                  (req_be),
        .req_wdata               (64'd0), // tied: ap_hit_wr checks the merge payload against the latched request, which is tied the same way; no property claims data values
        .ctrl_req_ready          (ctrl_req_ready),
        .ctrl_rsp_valid          (ctrl_rsp_valid),
        .ctrl_rsp_data           (ctrl_rsp_data),
        .ctrl_tag_a_set          (ctrl_tag_a_set),
        .ctrl_tag_a_tag_state    (tag_a_tag_state),
        .ctrl_tag_a_wr_en        (ctrl_tag_a_wr_en),
        .ctrl_tag_a_wr_way_onehot(ctrl_tag_a_wr_way_onehot),
        .ctrl_tag_a_wr_set       (ctrl_tag_a_wr_set),
        .ctrl_tag_a_wr_tag_state (ctrl_tag_a_wr_tag_state),
        .ctrl_data_a_addr        (ctrl_data_a_addr),
        .ctrl_data_a_way         (ctrl_data_a_way),
        .ctrl_data_a_rdata       (data_a_rdata), // free: the victim-CD source assertion compares against this gather data
        .ctrl_data_a_wr_en       (ctrl_data_a_wr_en),
        .ctrl_data_a_wr_way_onehot(ctrl_data_a_wr_way_onehot),
        .ctrl_data_a_wr_addr     (ctrl_data_a_wr_addr),
        .ctrl_data_a_wr_wdata    (ctrl_data_a_wr_wdata),
        .ctrl_data_a_wr_be       (ctrl_data_a_wr_be),
        .ctrl_tag_b_req          (ctrl_tag_b_req),
        .ctrl_tag_b_set          (ctrl_tag_b_set),
        .ctrl_tag_b_tag_state    (tag_b_tag_state),
        .ctrl_data_b_addr        (ctrl_data_b_addr),
        .ctrl_data_b_way         (ctrl_data_b_way),
        .ctrl_data_b_rdata       (64'd0), // tied: CD data values are never claimed
        .ctrl_repl_req           (ctrl_repl_req),
        .ctrl_repl_set           (),
        .ctrl_repl_way           (repl_way),
        .ctrl_repl_hit           (ctrl_repl_hit),
        .ctrl_repl_update        (ctrl_repl_update),
        .ctrl_repl_hit_way       (ctrl_repl_hit_way),
        .ctrl_victim_load        (ctrl_victim_load),
        .ctrl_victim_addr_in     (ctrl_victim_addr_in),
        .ctrl_victim_data_in     (ctrl_victim_data_in),
        .ctrl_fill_start         (ctrl_fill_start),
        .ctrl_fill_addr          (ctrl_fill_addr),
        .ctrl_req_class          (ctrl_req_class),
        .ctrl_fill_done          (fill_done),
        .ctrl_fill_beat_valid    (fill_beat_valid),
        .ctrl_fill_beat_idx      (fill_beat_idx),
        .ctrl_drain_start        (ctrl_drain_start),
        .ctrl_drain_done         (drain_done),
        .ctrl_snoop_req          (snoop_req),
        .ctrl_snoop_ready        (ctrl_snoop_ready),
        .ctrl_snoop_type         (snoop_type),
        .ctrl_snoop_addr         (snoop_addr),
        .ctrl_crresp             (ctrl_crresp),
        .ctrl_cddata             (ctrl_cddata),
        .ctrl_cdlast             (ctrl_cdlast),
        .ctrl_cdvalid            (ctrl_cdvalid),
        .ctrl_cdready            (cdready),
        .ctrl_init_busy          (ctrl_init_busy),
        .ctrl_init_set           (ctrl_init_set),
        .ctrl_state              (ctrl_state),
        .state_q                  (obs_state_q),
        .req_set                  (obs_req_set),
        .req_tag                  (obs_req_tag),
        .req_we_q                 (obs_req_we_q),
        .req_be_q                 (obs_req_be_q),
        .req_wdata_q              (obs_req_wdata_q),
        .upgr_q                   (obs_upgr_q),
        .hit_state_q              (obs_hit_state_q),
        .hit_way_q                (obs_hit_way_q),
        .hit_way_onehot           (obs_hit_way_onehot),
        .victim_way_q             (obs_victim_way_q),
        .victim_tag_q             (obs_victim_tag_q),
        .victim_way_onehot        (obs_victim_way_onehot),
        .victim_valid             (obs_victim_valid),
        .victim_buf_addr          (obs_victim_buf_addr),
        .victim_buf_data          (obs_victim_buf_data),
        .sn_set_q                 (obs_sn_set_q),
        .sn_hit_tag_q             (obs_sn_hit_tag_q),
        .sn_hit_way_q             (obs_sn_hit_way_q),
        .sn_hit_way_onehot        (obs_sn_hit_way_onehot),
        .sn_hit_any_q             (obs_sn_hit_any_q),
        .sn_pf_q                  (obs_sn_pf_q),
        .sn_stale_q               (obs_sn_stale_q),
        .sn_victim_q              (obs_sn_victim_q),
        .sn_upgr_line_q           (obs_sn_upgr_line_q),
        .sn_beat_q                (obs_sn_beat_q),
        .sn_beat_gated            (obs_sn_beat_gated),
        .sn_complete              (obs_sn_complete),
        .sn_wr_tag                (obs_sn_wr_tag),
        .sn_ref_q                 (obs_sn_ref_q),
        .sn_ref_grant             (obs_sn_ref_grant),
        .sn_type_q                (obs_sn_type_q),
        .w_sn_nxt                 (obs_w_sn_nxt),
        .sn_pf_gnt_match          (obs_sn_pf_gnt_match),
        .sn_stale_gnt             (obs_sn_stale_gnt),
        .sn_upgr_line_gnt         (obs_sn_upgr_line_gnt),
        .victim_match             (obs_victim_match),
        .sn_hit_any               (obs_sn_hit_any),
        .sn_hit_state             (obs_sn_hit_state),
        .pf_active                (obs_pf_active),
        .pf_addr                  (obs_pf_addr),
        .pf_state                 (obs_pf_state),
        .pf_match                 (obs_pf_match),
        .pf_data_valid            (obs_pf_data_valid),
        .pend_vld_q               (obs_pend_vld_q),
        .pend_state_q             (obs_pend_state_q),
        .install_state_eff        (obs_install_state_eff),
        .sn_return_q              (obs_sn_return_q),
        .fill_seen_q              (obs_fill_seen_q),
        .fill_done_q              (obs_fill_done_q),
        .drain_seen_q             (obs_drain_seen_q),
        .drain_done_q             (obs_drain_done_q)
    );

    // ------------------------------------------------------------------
    // Internal observability. The DUT flat is parameter-specialized (see
    // the Makefile) and amber_control.sby exposes the internal signals
    // below as DUT output ports; yosys has no hierarchical references and
    // its bind statement never fires on any target (verified in Task 13),
    // so expose + a plain property-module instantiation is the mechanism.
    // ------------------------------------------------------------------

    // ------------------------------------------------------------------
    // Proof (1): no stale data after an external write. When an
    // invalidating snoop completes on an installed line, that (set, tag)
    // is poisoned; until any (re)install writes the set, no way of the set
    // may present the poisoned tag in a valid MESI state. The check runs on
    // the exact tag-array model above, so a dropped or misdirected
    // invalidation write fails here. The completion condition uses the
    // exposed DUT internals.
    // ------------------------------------------------------------------
    localparam [3:0] W_CS_LOOKUP = 4'd2;
    localparam [3:0] W_CS_SNOOP  = 4'd10;
    localparam [2:0] W_ST_I      = 3'b000;

    reg             poison_vld;
    reg [SET_INDEX_WIDTH-1:0] poison_set;
    reg [TAG_WIDTH-1:0]       poison_tag;

    wire f_inv_complete = (ctrl_state == W_CS_SNOOP) && obs_sn_complete
                          && obs_sn_hit_any_q && !obs_sn_pf_q && !obs_sn_stale_q
                          && !obs_sn_victim_q && !obs_sn_upgr_line_q
                          && (obs_w_sn_nxt == W_ST_I);

    always @(posedge clk) begin
        if (!rst_n) begin
            poison_vld <= 1'b0;
        end else begin
            if (poison_vld && ctrl_tag_a_wr_en
                && (ctrl_tag_a_wr_set == poison_set))
                poison_vld <= 1'b0;   // a (re)install to the set ends the watch
            if (f_inv_complete) begin
                poison_vld <= 1'b1;   // new watch outranks the clear above
                poison_set <= obs_sn_set_q;
                poison_tag <= obs_sn_hit_tag_q;
            end
        end
    end

    wire [TAG_STATE_WIDTH-1:0] w_pway0 = tag_model[poison_set];
    wire [TAG_STATE_WIDTH-1:0] w_pway1 = tag_model[SETS + poison_set];
    wire w_poisoned = poison_vld
        && (((w_pway0[TAG_STATE_WIDTH-1 -: TAG_WIDTH] == poison_tag)
             && (w_pway0[2:0] != W_ST_I))
            || ((w_pway1[TAG_STATE_WIDTH-1 -: TAG_WIDTH] == poison_tag)
                && (w_pway1[2:0] != W_ST_I)));

    always @(posedge clk) begin
        if (rst_n)
            ap_no_stale_after_ext_write: assert (!w_poisoned);
    end

    // the poisoned line is looked up (and, per the assertion, misses)
    always @(posedge clk) begin
        if (rst_n)
            cp_poisoned_lookup: cover (poison_vld && (ctrl_state == W_CS_LOOKUP)
                                       && (obs_req_set == poison_set));
    end

    amber_control_props props (
        .clk                      (clk),
        .rst_n                    (rst_n),
        .ctrl_state               (ctrl_state),
        .state_q                  (obs_state_q),
        .req_valid                (req_valid),
        .ctrl_req_ready           (ctrl_req_ready),
        .ctrl_rsp_valid           (ctrl_rsp_valid),
        .ctrl_tag_a_wr_en         (ctrl_tag_a_wr_en),
        .ctrl_tag_a_wr_set        (ctrl_tag_a_wr_set),
        .ctrl_tag_a_wr_way_onehot (ctrl_tag_a_wr_way_onehot),
        .ctrl_tag_a_wr_tag_state  (ctrl_tag_a_wr_tag_state),
        .ctrl_data_a_wr_en        (ctrl_data_a_wr_en),
        .ctrl_data_a_wr_be        (ctrl_data_a_wr_be),
        .ctrl_data_a_wr_wdata     (ctrl_data_a_wr_wdata),
        .ctrl_fill_start          (ctrl_fill_start),
        .ctrl_fill_done           (fill_done),
        .ctrl_fill_beat_valid     (fill_beat_valid),
        .ctrl_fill_beat_idx       (fill_beat_idx),
        .ctrl_drain_start         (ctrl_drain_start),
        .ctrl_drain_done          (drain_done),
        .snoop_req                (snoop_req),
        .snoop_type               (snoop_type),
        .ctrl_snoop_ready         (ctrl_snoop_ready),
        .ctrl_crresp              (ctrl_crresp),
        .ctrl_cdvalid             (ctrl_cdvalid),
        .ctrl_cdlast              (ctrl_cdlast),
        .ctrl_cddata              (ctrl_cddata),
        .cdready                  (cdready),
        .req_set                  (obs_req_set),
        .req_tag                  (obs_req_tag),
        .req_we_q                 (obs_req_we_q),
        .req_be_q                 (obs_req_be_q),
        .req_wdata_q              (obs_req_wdata_q),
        .upgr_q                   (obs_upgr_q),
        .hit_state_q              (obs_hit_state_q),
        .hit_way_q                (obs_hit_way_q),
        .hit_way_onehot           (obs_hit_way_onehot),
        .victim_way_q             (obs_victim_way_q),
        .victim_tag_q             (obs_victim_tag_q),
        .victim_way_onehot        (obs_victim_way_onehot),
        .victim_valid             (obs_victim_valid),
        .victim_buf_addr          (obs_victim_buf_addr),
        .victim_buf_data          (obs_victim_buf_data),
        .sn_set_q                 (obs_sn_set_q),
        .sn_hit_tag_q             (obs_sn_hit_tag_q),
        .sn_hit_way_q             (obs_sn_hit_way_q),
        .sn_hit_way_onehot        (obs_sn_hit_way_onehot),
        .sn_hit_any_q             (obs_sn_hit_any_q),
        .sn_pf_q                  (obs_sn_pf_q),
        .sn_stale_q               (obs_sn_stale_q),
        .sn_victim_q              (obs_sn_victim_q),
        .sn_upgr_line_q           (obs_sn_upgr_line_q),
        .sn_beat_q                (obs_sn_beat_q),
        .sn_beat_gated            (obs_sn_beat_gated),
        .sn_complete              (obs_sn_complete),
        .sn_wr_tag                (obs_sn_wr_tag),
        .sn_ref_q                 (obs_sn_ref_q),
        .sn_ref_grant             (obs_sn_ref_grant),
        .sn_type_q                (obs_sn_type_q),
        .w_sn_nxt                 (obs_w_sn_nxt),
        .sn_pf_gnt_match          (obs_sn_pf_gnt_match),
        .sn_stale_gnt             (obs_sn_stale_gnt),
        .sn_upgr_line_gnt         (obs_sn_upgr_line_gnt),
        .victim_match             (obs_victim_match),
        .sn_hit_any               (obs_sn_hit_any),
        .sn_hit_state             (obs_sn_hit_state),
        .pf_active                (obs_pf_active),
        .pf_addr                  (obs_pf_addr),
        .pf_state                 (obs_pf_state),
        .pf_match                 (obs_pf_match),
        .pf_data_valid            (obs_pf_data_valid),
        .pend_vld_q               (obs_pend_vld_q),
        .pend_state_q             (obs_pend_state_q),
        .install_state_eff        (obs_install_state_eff),
        .sn_return_q              (obs_sn_return_q),
        .fill_seen_q              (obs_fill_seen_q),
        .fill_done_q              (obs_fill_done_q),
        .drain_seen_q             (obs_drain_seen_q),
        .drain_done_q             (obs_drain_done_q)
    );

endmodule

// ===========================================================================
// Property module: bound into amber_control (ports resolve in DUT scope)
// ===========================================================================
//
// Assumption inventory (environment obligations; each recorded):
//   - house reset protocol;
//   - A-fill: done only after start, one pulse per launch, forced within 12
//     cycles of the start (fair partner), and only as RLAST (all 8 beats
//     delivered first); beats arrive in order 0..7, one strobe per beat,
//     only between start and done (AXI R-channel contract);
//   - A-drain: done only after start, forced within 6 cycles;
//   - A-cdready: stalled at most 1 cycle (fair manager);
//   - A-snoop (fair arbitration): a grant may follow a previous grant only
//     after >= 6 cycles, and at most 2 grants per accepted CPU request;
//   - A-cpu (fair arbitration): req_valid only raises at IDLE (the blocking
//     frontend's contract) and only one request is outstanding.
//
// The bounded-liveness assertions are the contrapositive of deadlock/
// livelock: under these fair constraints no state residence and no whole
// request can exceed its bound. Bounds are generous on purpose (the honest
// path uses ~half); a FAIL means the RTL can actually be starved/stuck.
//
module amber_control_props (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [3:0]  ctrl_state,
    input  logic [11:0] state_q,
    input  logic        req_valid,
    input  logic        ctrl_req_ready,
    input  logic        ctrl_rsp_valid,
    input  logic        ctrl_tag_a_wr_en,
    input  logic [3:0]  ctrl_tag_a_wr_set,
    input  logic [1:0]  ctrl_tag_a_wr_way_onehot,
    input  logic [24:0] ctrl_tag_a_wr_tag_state,
    input  logic        ctrl_data_a_wr_en,
    input  logic [7:0]  ctrl_data_a_wr_be,
    input  logic [63:0] ctrl_data_a_wr_wdata,
    input  logic        ctrl_fill_start,
    input  logic        ctrl_fill_done,
    input  logic        ctrl_fill_beat_valid,
    input  logic [2:0]  ctrl_fill_beat_idx,
    input  logic        ctrl_drain_start,
    input  logic        ctrl_drain_done,
    input  logic        snoop_req,
    input  logic [2:0]  snoop_type,
    input  logic        ctrl_snoop_ready,
    input  logic [4:0]  ctrl_crresp,
    input  logic        ctrl_cdvalid,
    input  logic        ctrl_cdlast,
    input  logic [63:0] ctrl_cddata,
    input  logic        cdready,
    input  logic [3:0]  req_set,
    input  logic [21:0] req_tag,
    input  logic        req_we_q,
    input  logic [7:0]  req_be_q,
    input  logic [63:0] req_wdata_q,
    input  logic        upgr_q,
    input  logic [2:0]  hit_state_q,
    input  logic        hit_way_q,
    input  logic [1:0]  hit_way_onehot,
    input  logic        victim_way_q,
    input  logic [21:0] victim_tag_q,
    input  logic [1:0]  victim_way_onehot,
    input  logic        victim_valid,
    input  logic [31:0] victim_buf_addr,
    input  logic [511:0] victim_buf_data,
    input  logic [3:0]  sn_set_q,
    input  logic [21:0] sn_hit_tag_q,
    input  logic        sn_hit_way_q,
    input  logic [1:0]  sn_hit_way_onehot,
    input  logic        sn_hit_any_q,
    input  logic        sn_pf_q,
    input  logic        sn_stale_q,
    input  logic        sn_victim_q,
    input  logic        sn_upgr_line_q,
    input  logic [2:0]  sn_beat_q,
    input  logic        sn_beat_gated,
    input  logic        sn_complete,
    input  logic        sn_wr_tag,
    input  logic [2:0]  sn_ref_q,
    input  logic [2:0]  sn_ref_grant,
    input  logic [2:0]  sn_type_q,
    input  logic [2:0]  w_sn_nxt,
    input  logic        sn_pf_gnt_match,
    input  logic        sn_stale_gnt,
    input  logic        sn_upgr_line_gnt,
    input  logic        victim_match,
    input  logic        sn_hit_any,
    input  logic [2:0]  sn_hit_state,
    input  logic        pf_active,
    input  logic [25:0] pf_addr,
    input  logic [2:0]  pf_state,
    input  logic        pf_match,
    input  logic [7:0]  pf_data_valid,
    input  logic        pend_vld_q,
    input  logic [2:0]  pend_state_q,
    input  logic [2:0]  install_state_eff,
    input  logic [11:0] sn_return_q,
    input  logic        fill_seen_q,
    input  logic        fill_done_q,
    input  logic        drain_seen_q,
    input  logic        drain_done_q
);

    localparam SETS       = 16;
    localparam WAYS       = 2;
    localparam TAGW       = 22;
    localparam TAGSW      = 25;
    localparam FILL_BEATS = 8;

    // ctrl_state_t encodings (amber_pkg)
    localparam [3:0] CS_IDLE        = 4'd0;
    localparam [3:0] CS_LOOKUP      = 4'd2;
    localparam [3:0] CS_HIT_RD      = 4'd3;
    localparam [3:0] CS_HIT_WR      = 4'd4;
    localparam [3:0] CS_MISS_VICTIM = 4'd5;
    localparam [3:0] CS_MISS_DRAIN  = 4'd6;
    localparam [3:0] CS_MISS_FILL   = 4'd7;
    localparam [3:0] CS_FILL_WRITE  = 4'd8;
    localparam [3:0] CS_REPLAY      = 4'd9;
    localparam [3:0] CS_SNOOP       = 4'd10;
    localparam [3:0] CS_ERROR       = 4'd11;

    // cache_state_t encodings (amber_pkg)
    localparam [2:0] ST_I = 3'b000;
    localparam [2:0] ST_S = 3'b001;
    localparam [2:0] ST_E = 3'b010;
    localparam [2:0] ST_M = 3'b011;

    localparam [11:0] OH_MISS_DRAIN = 12'b0000_0100_0000;

    // ------------------------------------------------------------------
    // Independent spec copy of the HAS Table 3.0 CRRESP decode. amber_pkg
    // is the RTL authority; this copy is the formal cross-check: a wiring
    // change to the pkg function fails ap_grant_crresp. Verified cell for
    // cell against amber_pkg.amber_snoop_crresp (IHI0022 bit order
    // {WU[4], IS[3], PD[2], Err[1], DT[0]}).
    // ------------------------------------------------------------------
    function [4:0] exp_crresp;
        input [2:0] state;
        input [2:0] snoop;
        reg dt, pd, is, wu;
        begin
            dt = 1'b0; pd = 1'b0; is = 1'b0; wu = 1'b0;
            case (state)
                ST_M: begin
                    case (snoop)
                        3'b000, 3'b011, 3'b100: begin dt = 1'b1; pd = 1'b1; is = 1'b1; end
                        3'b001, 3'b010:         begin dt = 1'b1; pd = 1'b1; end
                        default: ;
                    endcase
                end
                ST_E: begin
                    case (snoop)
                        3'b000, 3'b001: begin dt = 1'b1; is = 1'b1; wu = 1'b1; end
                        3'b010:         begin dt = 1'b1; wu = 1'b1; end
                        3'b011:         begin is = 1'b1; wu = 1'b1; end
                        default: ;
                    endcase
                end
                ST_S: begin
                    case (snoop)
                        3'b000, 3'b001: is = 1'b1;
                        default: ;
                    endcase
                end
                default: ;
            endcase
            exp_crresp = {wu, is, pd, 1'b0, dt};
        end
    endfunction

    // ------------------------------------------------------------------
    // Formal infrastructure (house pattern)
    // ------------------------------------------------------------------
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    // =========================================================================
    // Environment assumptions (fair arbitration + well-behaved partners)
    // =========================================================================

    // ---- fill partner ----
    reg f_fill_start_seen, f_fill_done_seen;
    reg [3:0] f_fill_wait;
    reg [3:0] f_beat_count;
    always @(posedge clk) begin
        if (!rst_n) begin
            f_fill_start_seen <= 1'b0; f_fill_done_seen <= 1'b0;
            f_fill_wait <= 4'd0; f_beat_count <= 4'd0;
        end else begin
            if (ctrl_fill_start) begin
                f_fill_start_seen <= 1'b1;
                f_fill_wait <= 4'd0;
                f_beat_count <= 4'd0;
            end else if (!f_fill_done_seen && (f_fill_wait != 4'hF)) begin
                f_fill_wait <= f_fill_wait + 4'd1;
            end
            if (ctrl_fill_done) f_fill_done_seen <= 1'b1;
            if (ctrl_fill_beat_valid && (f_beat_count != 4'hF))
                f_beat_count <= f_beat_count + 4'd1;
            if (ctrl_state == CS_FILL_WRITE) begin
                f_fill_start_seen <= 1'b0; f_fill_done_seen <= 1'b0;
                f_fill_wait <= 4'd0; f_beat_count <= 4'd0;
            end
        end
    end

    always @(posedge clk) begin
        if (rst_n) begin
            as_fill_done_after_start: assume (!ctrl_fill_done || f_fill_start_seen);
            as_fill_done_once: assume (!ctrl_fill_done || !f_fill_done_seen);
            // Structural minimum: 8 in-order beat strobes, one per cycle,
            // all BEFORE done (as_fill_done_is_rlast + as_beat_order), so
            // the earliest legal done is start+9. The fair window must
            // exceed that or the assumption set is UNSATISFIABLE and the
            // whole proof vacates past the fill (caught by the cover task:
            // no completing trace existed). 12 = smallest value with
            // margin; DV full soaks complete fills in ~12-20 cycles.
            as_fill_done_fair: assume (!(f_fill_start_seen && !f_fill_done_seen)
                                       || (f_fill_wait < 12) || ctrl_fill_done);
            as_fill_done_is_rlast: assume (!ctrl_fill_done
                                           || (f_beat_count == FILL_BEATS));
            as_beat_order: assume (!ctrl_fill_beat_valid
                || (f_fill_start_seen && !f_fill_done_seen
                    && (ctrl_fill_beat_idx == f_beat_count[2:0])));
        end
    end

    // ---- drain partner ----
    reg f_drain_start_seen, f_drain_done_seen;
    reg [3:0] f_drain_wait;
    always @(posedge clk) begin
        if (!rst_n) begin
            f_drain_start_seen <= 1'b0; f_drain_done_seen <= 1'b0;
            f_drain_wait <= 4'd0;
        end else begin
            if (ctrl_drain_start) begin
                f_drain_start_seen <= 1'b1;
                f_drain_wait <= 4'd0;
            end else if (!f_drain_done_seen && (f_drain_wait != 4'hF)) begin
                f_drain_wait <= f_drain_wait + 4'd1;
            end
            if (ctrl_drain_done) f_drain_done_seen <= 1'b1;
            if (ctrl_state == CS_FILL_WRITE) begin
                f_drain_start_seen <= 1'b0; f_drain_done_seen <= 1'b0;
                f_drain_wait <= 4'd0;
            end
        end
    end

    always @(posedge clk) begin
        if (rst_n) begin
            as_drain_done_after_start: assume (!ctrl_drain_done || f_drain_start_seen);
            as_drain_done_once: assume (!ctrl_drain_done || !f_drain_done_seen);
            as_drain_done_fair: assume (!(f_drain_start_seen && !f_drain_done_seen)
                                        || (f_drain_wait < 6) || ctrl_drain_done);
        end
    end

    // ---- CD channel (fair manager) ----
    reg [1:0] f_cd_wait;
    always @(posedge clk) begin
        if (!rst_n) f_cd_wait <= 0;
        else if (ctrl_cdvalid && !cdready) begin
            if (f_cd_wait != 2'h3) f_cd_wait <= f_cd_wait + 1;
        end else f_cd_wait <= 0;
    end

    always @(posedge clk) begin
        if (rst_n)
            as_cdready_fair: assume (!(ctrl_cdvalid && !cdready)
                                     || (f_cd_wait < 1) || cdready);
    end

    // ---- CPU / snoop fair arbitration ----
    reg        f_req_pending;
    wire       f_req_accept = req_valid && ctrl_req_ready;
    always @(posedge clk) begin
        if (!rst_n) f_req_pending <= 1'b0;
        else if (f_req_accept) f_req_pending <= 1'b1;
        else if (ctrl_rsp_valid) f_req_pending <= 1'b0;
    end

    reg [3:0] f_sn_gap;
    reg [1:0] f_sn_per_txn;
    always @(posedge clk) begin
        if (!rst_n) begin
            f_sn_gap <= 4'hF;
            f_sn_per_txn <= 2'd0;
        end else begin
            if (ctrl_snoop_ready) begin
                f_sn_gap <= 4'd0;
                if (f_req_pending && (f_sn_per_txn != 2'h3))
                    f_sn_per_txn <= f_sn_per_txn + 1;
            end else if (f_sn_gap != 4'hF) begin
                f_sn_gap <= f_sn_gap + 4'd1;
            end
            if (f_req_accept) f_sn_per_txn <= 2'd0;
        end
    end

    always @(posedge clk) begin
        if (rst_n) begin
            as_sn_spacing: assume (!snoop_req || (f_sn_gap >= 6));
            as_sn_per_txn: assume (!ctrl_snoop_ready || (f_sn_per_txn < 2));
            as_req_at_idle: assume (!req_valid || (ctrl_state == CS_IDLE));
            as_single_outstanding: assume (!req_valid || !f_req_pending);
        end
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // S0 the one-hot FSM is never corrupted and never enters sticky ERROR.
    // sn_return_q carries the same one-hot discipline: it is reset to
    // OH_IDLE and latched only from a one-hot state_q at the snoop grant.
    // That second clause is not redundant: without it k-induction's
    // arbitrary step state can inject a multi-hot sn_return_q, which
    // state_d then inherits out of CTRL_SNOOP (found by the induction
    // step failing on ap_fsm_onehot -- it is the closing lemma).
    always @(posedge clk) begin
        if (rst_n) begin
            ap_fsm_onehot: assert ((state_q != 12'd0)
                                   && ((state_q & (state_q - 12'd1)) == 12'd0));
            ap_sn_return_onehot: assert ((sn_return_q != 12'd0)
                                         && ((sn_return_q & (sn_return_q - 12'd1)) == 12'd0));
            ap_never_error: assert (ctrl_state != CS_ERROR);
        end
    end

    // S1 the invalidation actually lands: the snoop's final-cycle tag write
    // carries the resolved next state to the probed way.
    always @(posedge clk) begin
        if (rst_n)
            ap_inv_write_lands: assert (!(ctrl_state == CS_SNOOP && sn_complete && sn_wr_tag)
                || (ctrl_tag_a_wr_en
                    && (ctrl_tag_a_wr_set == sn_set_q)
                    && (ctrl_tag_a_wr_way_onehot == sn_hit_way_onehot)
                    && (ctrl_tag_a_wr_tag_state == {sn_hit_tag_q, w_sn_nxt})));
    end

    // S3 fill commit installs exactly the resolved line: the request tag at
    // the (upgrade hit | victim) way, in the effective install state.
    always @(posedge clk) begin
        if (rst_n)
            ap_fill_install: assert (!(ctrl_state == CS_FILL_WRITE)
                || (ctrl_tag_a_wr_en
                    && (ctrl_tag_a_wr_set == req_set)
                    && (ctrl_tag_a_wr_way_onehot == (upgr_q ? hit_way_onehot : victim_way_onehot))
                    && (ctrl_tag_a_wr_tag_state == {req_tag, install_state_eff})));
    end

    // S4 an armed post-commit snoop effect (invalidation-sticks) is what the
    // fill installs.
    always @(posedge clk) begin
        if (rst_n)
            ap_pend_install: assert (!(ctrl_state == CS_FILL_WRITE && pend_vld_q)
                || (ctrl_tag_a_wr_tag_state[2:0] == pend_state_q));
    end

    // S5 pending-fill state accuracy (MAS ch02/02): at the grant the CRRESP
    // reflects the resolved reference state -- pf > stale > victim-buffer >
    // installed hit > Invalid -- checked against the independent spec copy.
    wire [2:0] f_exp_ref = sn_pf_gnt_match ? pf_state  :
                           sn_stale_gnt    ? ST_I      :
                           victim_match    ? ST_M      :
                           sn_hit_any      ? sn_hit_state : ST_I;
    always @(posedge clk) begin
        if (rst_n)
            ap_grant_crresp: assert (!ctrl_snoop_ready
                || ((ctrl_crresp == exp_crresp(f_exp_ref, snoop_type))
                    && (f_exp_ref == sn_ref_grant)));
    end

    // S6 CD beat gating: beats present exactly when servable, cdlast on the
    // final beat index (the pf per-beat pf_data_valid gate included).
    always @(posedge clk) begin
        if (rst_n)
            ap_cd_gating: assert (!(ctrl_state == CS_SNOOP)
                || ((ctrl_cdvalid == sn_beat_gated)
                    && (ctrl_cdlast == (sn_beat_q == 3'd7))));
    end

    // S7 the stale-victim entry is answered Invalid, no data transfer.
    // The coupling lemma (sn_stale_q -> sn_ref_q == I) is a grant-cycle
    // latch invariant: k-induction's arbitrary step state otherwise pairs
    // sn_stale_q with an unrelated sn_ref_q. Reachable: both are latched
    // from the same grant where sn_stale_gnt forces sn_ref_grant = I.
    always @(posedge clk) begin
        if (rst_n)
            ap_stale_ref_i: assert (!sn_stale_q || (sn_ref_q == ST_I));
    end

    always @(posedge clk) begin
        if (rst_n)
            ap_stale_nodt: assert (!(ctrl_state == CS_SNOOP && sn_stale_q)
                || !ctrl_crresp[0]);
    end

    // S8 victim-buffer handoff: while the drain is outstanding the snoop's CD
    // beats are sourced from the staged victim line.
    always @(posedge clk) begin
        if (rst_n)
            ap_victim_cd_data: assert (!(ctrl_state == CS_SNOOP && sn_victim_q)
                || (ctrl_cddata == victim_buf_data[sn_beat_q*64 +: 64]));
    end

    // S9 write hit: byte merge into the request beat, promote E->M (M keeps
    // its tag entry) at exactly the hit way (the Task-7 one-hot pin).
    always @(posedge clk) begin
        if (rst_n)
            ap_hit_wr: assert (!(ctrl_state == CS_HIT_WR)
                || (ctrl_data_a_wr_en
                    && (ctrl_data_a_wr_be == req_be_q)
                    && (ctrl_data_a_wr_wdata == req_wdata_q)
                    && (ctrl_tag_a_wr_en == (hit_state_q != ST_M))
                    && (ctrl_tag_a_wr_way_onehot == hit_way_onehot)
                    && (ctrl_tag_a_wr_tag_state == {req_tag, ST_M})));
    end

    // =========================================================================
    // Liveness lives in formal_amber_control_live.sv / amber_control_live.sby
    // (a model-free wrapper: the bounded-residence and whole-request bounds
    // quantify over all tag behaviors, so they need no tag store -- and BMC
    // at depth 126 pays for the tag memory's store chains unnecessarily).
    // This file proves the SAFETY properties (incl. the poison invariant,
    // k-induction in amber_control.sby) and the cover statements.
    // =========================================================================

    // =========================================================================
    // Cover properties
    // =========================================================================

    // a CD beat served from the pending fill
    always @(posedge clk) begin
        if (rst_n)
            cp_pf_cd_beat: cover (ctrl_state == CS_SNOOP && sn_pf_q && ctrl_cdvalid);
    end

    // fill commit honoring an armed post-commit snoop effect
    always @(posedge clk) begin
        if (rst_n)
            cp_pend_commit: cover (ctrl_state == CS_FILL_WRITE && pend_vld_q);
    end

    // a snoop detour taken out of the drain wait, returning to it
    always @(posedge clk) begin
        if (rst_n)
            cp_detour_drain: cover (ctrl_state == CS_SNOOP
                                    && (sn_return_q == OH_MISS_DRAIN));
    end

    // a response to a request that went through the miss path
    reg f_saw_miss;
    always @(posedge clk) begin
        if (!rst_n) f_saw_miss <= 1'b0;
        else if (ctrl_rsp_valid) f_saw_miss <= 1'b0;
        else if (ctrl_state == 4'd5) f_saw_miss <= 1'b1;   // MISS_VICTIM
    end
    always @(posedge clk) begin
        if (rst_n)
            cp_miss_rsp: cover (ctrl_rsp_valid && f_saw_miss);
    end

    // a grant answered from the pending fill (the bypass path)
    always @(posedge clk) begin
        if (rst_n)
            cp_pf_grant: cover (ctrl_snoop_ready && (ctrl_state == CS_MISS_FILL)
                                && pf_match);
    end

    // hit service both ways
    always @(posedge clk) begin
        if (rst_n)
            cp_hits: cover ((ctrl_state == CS_HIT_RD) || (ctrl_state == CS_HIT_WR));
    end

endmodule

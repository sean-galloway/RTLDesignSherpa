`timescale 1ns / 1ps

`include "reset_defs.svh"
//
// axi5_atomic_filter: read-return atomic termination (bridge TASK-002 (was BRIDGE-002) A5-3a)
//
// Sits on the AW/W/B CONTROL path at an atomic-enabled boundary whose
// fabric can transport store-class atomics but cannot route the R-channel
// data that load-class atomics return (AtomicLoad 6'b10xxxx and
// AtomicSwap/Compare 6'b11000x respond on R with the AW ID — a write-path
// fabric never sees it, so an unfiltered load-class atomic would hang).
//
//   - AWATOP[5] == 0 (non-atomic and AtomicStore): AW/W/B pass through.
//   - AWATOP[5] == 1 (read-return classes): the AW is accepted upstream
//     but NOT forwarded, its W burst is consumed and discarded, a local
//     DECERR B response is returned with the AW's ID, AND the read data
//     transfers the atomic owes are returned on R: each DECERR, RID = AWID,
//     RLAST on the final one. IHI 0022L A6.4.8: "A Subordinate must send the
//     correct number of read data transfers, even if the write response is
//     DECERR or SLVERR" -- a compliant manager waits for them, so a B-only
//     answer hangs it (GitHub #102 item 2). A6.4.7 sets the count:
//     AWLEN+1 for AtomicLoad/AtomicSwap; for AtomicCompare half of that when
//     AWLEN+1 > 1, else 1 -- which is AWLEN>>1 beats-minus-one in both cases.
//
// The filter handles handshakes, ATOP, ID, AWLEN, WLAST and RLAST only;
// address/data payload buses route around it (connect them straight through
// -- the downstream side must qualify payload with m_awvalid/m_wvalid as
// usual). RDATA, RUSER and the AXI5 R sidebands also route around: on a
// local error beat they carry whatever the downstream R bus holds, which a
// DECERR makes don't-care.
// The B and R payloads are output MUXes: downstream responses take priority,
// local DECERRs drain when the downstream channel is idle. R never
// interleaves the two sources inside a burst: once a burst's first beat is
// accepted, its source is held until RLAST.
//
// Constraints (documented, asserted where cheap):
//   - W beats are stalled until their AW has been accepted (s_wready is
//     held low while the route queue is empty). AW never depends on W,
//     so this cannot deadlock.
//   - A local DECERR can pass a same-ID in-flight write's B response.
//     The AXI atomic rules already require atomics not to share an ID
//     with outstanding transactions, so a compliant master never sees
//     the reorder.

module axi5_atomic_filter #(
    parameter int AXI_ID_WIDTH   = 4,
    parameter int AXI_ATOP_WIDTH = 6,
    parameter int DEPTH_LG2      = 3,   // route/response queues: 2**DEPTH_LG2
    parameter int IW             = AXI_ID_WIDTH,
    parameter int DEPTH          = 1 << DEPTH_LG2
) (
    input  logic          aclk,
    input  logic          aresetn,

    // Upstream (from the boundary wrapper's fub side)
    input  logic          s_awvalid,
    output logic          s_awready,
    input  logic [IW-1:0] s_awid,
    input  logic [AXI_ATOP_WIDTH-1:0] s_awatop,
    input  logic [7:0]    s_awlen,     // R beat count of a swallowed atomic (A6.4.7)
    input  logic          s_wvalid,
    output logic          s_wready,
    input  logic          s_wlast,
    output logic          s_bvalid,
    input  logic          s_bready,
    output logic [IW-1:0] s_bid,
    output logic [1:0]    s_bresp,
    // Read data channel: downstream R merged with the local read-return
    // beats of swallowed atomics (RDATA/RUSER route around the filter).
    output logic          s_rvalid,
    input  logic          s_rready,
    output logic [IW-1:0] s_rid,
    output logic [1:0]    s_rresp,
    output logic          s_rlast,

    // Downstream (toward the fabric)
    output logic          m_awvalid,
    input  logic          m_awready,
    output logic          m_wvalid,
    input  logic          m_wready,
    input  logic          m_bvalid,
    output logic          m_bready,
    input  logic [IW-1:0] m_bid,
    input  logic [1:0]    m_bresp,
    input  logic          m_rvalid,
    output logic          m_rready,
    input  logic [IW-1:0] m_rid,
    input  logic [1:0]    m_rresp,
    input  logic          m_rlast
);

    // AWATOP[5] set => the atomic returns data on R: swallow it here.
    wire w_swallow = s_awatop[AXI_ATOP_WIDTH-1];

    // Read data transfers owed, minus one (A6.4.7). AtomicCompare (110001)
    // returns half the write length when that is more than one transfer:
    // (AWLEN+1)/2 - 1 == AWLEN>>1 for odd AWLEN, and AWLEN>>1 == 0 for the
    // single-transfer case, so one shift covers both. Load/Swap return AWLEN+1.
    localparam logic [AXI_ATOP_WIDTH-1:0] ATOP_COMPARE = AXI_ATOP_WIDTH'(6'b110001);
    wire [7:0] w_r_beats_m1 = (s_awatop == ATOP_COMPARE) ? (s_awlen >> 1) : s_awlen;

    // -----------------------------------------------------------------
    // Route queue: one entry per accepted AW, popped at its WLAST beat.
    // Entry = swallow flag for that transaction's W burst.
    // -----------------------------------------------------------------
    logic [DEPTH-1:0]     r_route_mem;
    logic [DEPTH_LG2:0]   r_route_wptr, r_route_rptr;
    wire                  w_route_empty = (r_route_wptr == r_route_rptr);
    wire                  w_route_full  =
        (r_route_wptr[DEPTH_LG2-1:0] == r_route_rptr[DEPTH_LG2-1:0]) &&
        (r_route_wptr[DEPTH_LG2]     != r_route_rptr[DEPTH_LG2]);
    wire                  w_route_head  = r_route_mem[r_route_rptr[DEPTH_LG2-1:0]];

    // -----------------------------------------------------------------
    // Response queue: one entry per swallowed AW; drains as local DECERR
    // B responses whenever the downstream B channel is idle.
    // -----------------------------------------------------------------
    logic [IW-1:0]        r_resp_mem [DEPTH];
    // r_resp_wptr reserves the slot at AW; r_resp_cptr COMMITS it once the
    // swallowed burst's WLAST has been consumed. AXI forbids returning B
    // before the write data has been received, and the response was
    // previously visible the moment the AW was accepted -- so a master still
    // mid-W-burst could see BVALID for that burst. Emptiness is judged on the
    // COMMIT pointer, so nothing is presented early; fullness still uses the
    // write pointer, so the slot is reserved as soon as it is claimed.
    logic [DEPTH_LG2:0]   r_resp_wptr, r_resp_cptr, r_resp_rptr;
    wire                  w_resp_empty = (r_resp_cptr == r_resp_rptr);
    wire                  w_resp_full  =
        (r_resp_wptr[DEPTH_LG2-1:0] == r_resp_rptr[DEPTH_LG2-1:0]) &&
        (r_resp_wptr[DEPTH_LG2]     != r_resp_rptr[DEPTH_LG2]);
    wire [IW-1:0]         w_resp_head  = r_resp_mem[r_resp_rptr[DEPTH_LG2-1:0]];

    // -----------------------------------------------------------------
    // Read-return queue: one entry per swallowed AW (ID + beats-minus-one);
    // drains as local DECERR R beats. Pushed at AW accept and visible at
    // once: A6.4.7 lets a Subordinate send all read data before accepting
    // any write data, and the Manager must be able to take it.
    // -----------------------------------------------------------------
    logic [IW-1:0]        r_rq_id_mem  [DEPTH];
    logic [7:0]           r_rq_len_mem [DEPTH];
    logic [DEPTH_LG2:0]   r_rq_wptr, r_rq_rptr;
    logic [7:0]           r_rq_beat;          // beats of the head entry sent
    wire                  w_rq_empty = (r_rq_wptr == r_rq_rptr);
    wire                  w_rq_full  =
        (r_rq_wptr[DEPTH_LG2-1:0] == r_rq_rptr[DEPTH_LG2-1:0]) &&
        (r_rq_wptr[DEPTH_LG2]     != r_rq_rptr[DEPTH_LG2]);
    wire [IW-1:0]         w_rq_head_id  = r_rq_id_mem[r_rq_rptr[DEPTH_LG2-1:0]];
    wire [7:0]            w_rq_head_len = r_rq_len_mem[r_rq_rptr[DEPTH_LG2-1:0]];
    wire                  w_local_rvalid = !w_rq_empty;
    wire                  w_local_rlast  = (r_rq_beat == w_rq_head_len);

    // -----------------------------------------------------------------
    // AW path. Forwarded AWs need m_awready; swallowed AWs need space in
    // both local response queues. Both need route-queue space.
    // -----------------------------------------------------------------
    assign m_awvalid = s_awvalid && !w_swallow && !w_route_full;
    assign s_awready = !w_route_full &&
                       (w_swallow ? (!w_resp_full && !w_rq_full) : m_awready);

    wire w_aw_hs = s_awvalid && s_awready;

    // -----------------------------------------------------------------
    // W path. Beats stall until their AW is queued; swallowed bursts
    // are sunk here, forwarded bursts hand through.
    // -----------------------------------------------------------------
    assign m_wvalid = s_wvalid && !w_route_empty && !w_route_head;
    assign s_wready = !w_route_empty &&
                      (w_route_head ? 1'b1 : m_wready);

    wire w_w_hs_last = s_wvalid && s_wready && s_wlast;

    // -----------------------------------------------------------------
    // B path. Downstream first; local DECERR when downstream is idle.
    // -----------------------------------------------------------------
    // The SOURCE is latched once a beat is presented. Without that, a local
    // DECERR held under s_bready=0 gets its payload replaced the moment a
    // downstream B arrives: s_bvalid stays high while s_bid/s_bresp change,
    // which is the AXI stability rule (payload constant from VALID to the
    // handshake) broken on the response channel. No beat is lost either way --
    // the resp queue pops only on w_local_b_hs -- but a strict VIP or a
    // formal stable(BID/BRESP) check fires, and the master is entitled to
    // sample BRESP on any cycle it likes for logging.
    //
    // Same selection-hold this repo already uses in apb_monitor_addr_check
    // and axi_monitor_addr_check for the identical hazard. Nothing is delayed
    // indefinitely: the hold clears on accept, and the displaced source is
    // presented on the next free cycle.
    logic r_sel_ds;      // the presented beat came from downstream
    logic r_sel_held;

    wire w_sel_ds = r_sel_held ? r_sel_ds : m_bvalid;

    assign s_bvalid = m_bvalid || !w_resp_empty;
    assign s_bid    = w_sel_ds ? m_bid   : w_resp_head;
    assign s_bresp  = w_sel_ds ? m_bresp : 2'b11;  // DECERR
    // Only accept downstream when downstream is the source being presented,
    // or its B would be consumed while the master is looking at a DECERR.
    assign m_bready = s_bready && w_sel_ds;

    // Matches this module's existing reset style rather than the reset-macro
    // header, which it does not include.
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_sel_held <= 1'b0;
            r_sel_ds   <= 1'b0;
        end else begin
            if (s_bvalid && s_bready)
                r_sel_held <= 1'b0;
            else if (s_bvalid && !s_bready) begin
                r_sel_held <= 1'b1;
                r_sel_ds   <= w_sel_ds;
            end
        end
    )

    // Pop when the beat the master ACCEPTED came from the local queue --
    // which is exactly !w_sel_ds, the same select that drove s_bid/s_bresp.
    //
    // This read `!m_bvalid && !w_resp_empty && s_bready`, keying the pop on
    // downstream being IDLE rather than on which source was presented. Under
    // the selection hold those differ: a local DECERR held through
    // backpressure stays presented when a downstream B arrives (w_sel_ds=0,
    // correctly), and when the master finally accepts it, m_bvalid is 1 -- so
    // the queue was not popped for a beat the master had taken. The same
    // DECERR was then presented again: a duplicate B with no matching AW, and
    // every later swallowed atomic shifted behind a stale head.
    wire w_local_b_hs = s_bvalid && s_bready && !w_sel_ds;

    // -----------------------------------------------------------------
    // R path. Same shape as B -- downstream first, local beats when the
    // downstream R channel is idle, source latched while a beat is held --
    // plus a BURST hold: once a burst's first beat is accepted the source
    // stays put until RLAST, so local and downstream bursts never interleave
    // on s_r* (a consumer that does not expect cross-ID interleaving sees
    // none). A held downstream burst whose next beat is late simply leaves
    // s_rvalid low; it cannot strand anything, because the downstream must
    // finish the burst it started.
    // -----------------------------------------------------------------
    logic r_r_sel_ds;    // the presented / in-progress burst is downstream's
    logic r_r_held;      // beat held under backpressure, or burst open

    wire w_r_sel_ds = r_r_held ? r_r_sel_ds : m_rvalid;

    assign s_rvalid = w_r_sel_ds ? m_rvalid : w_local_rvalid;
    assign s_rid    = w_r_sel_ds ? m_rid    : w_rq_head_id;
    assign s_rresp  = w_r_sel_ds ? m_rresp  : 2'b11;  // DECERR
    assign s_rlast  = w_r_sel_ds ? m_rlast  : w_local_rlast;
    assign m_rready = s_rready && w_r_sel_ds;

    wire w_r_hs       = s_rvalid && s_rready;
    wire w_local_r_hs = w_r_hs && !w_r_sel_ds;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_r_held   <= 1'b0;
            r_r_sel_ds <= 1'b0;
        end else begin
            if (w_r_hs) begin
                r_r_held   <= !s_rlast;      // open burst keeps its source
                r_r_sel_ds <= w_r_sel_ds;
            end else if (s_rvalid) begin
                r_r_held   <= 1'b1;          // beat presented, not accepted
                r_r_sel_ds <= w_r_sel_ds;
            end
        end
    )

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_route_wptr <= '0;
            r_route_rptr <= '0;
            r_resp_wptr  <= '0;
            r_resp_cptr  <= '0;
            r_resp_rptr  <= '0;
            r_rq_wptr    <= '0;
            r_rq_rptr    <= '0;
            r_rq_beat    <= '0;
        end else begin
            if (w_aw_hs) begin
                r_route_mem[r_route_wptr[DEPTH_LG2-1:0]] <= w_swallow;
                r_route_wptr <= r_route_wptr + 1'b1;
                if (w_swallow) begin
                    r_resp_mem[r_resp_wptr[DEPTH_LG2-1:0]] <= s_awid;
                    r_resp_wptr <= r_resp_wptr + 1'b1;
                    r_rq_id_mem[r_rq_wptr[DEPTH_LG2-1:0]]  <= s_awid;
                    r_rq_len_mem[r_rq_wptr[DEPTH_LG2-1:0]] <= w_r_beats_m1;
                    r_rq_wptr <= r_rq_wptr + 1'b1;
                end
            end
            if (w_w_hs_last) begin
                r_route_rptr <= r_route_rptr + 1'b1;
                // w_route_head is 1 for a swallowed burst: its DECERR becomes
                // visible only now, once its write data has been consumed.
                if (w_route_head)
                    r_resp_cptr <= r_resp_cptr + 1'b1;
            end
            if (w_local_b_hs)
                r_resp_rptr <= r_resp_rptr + 1'b1;
            if (w_local_r_hs) begin
                if (w_local_rlast) begin
                    r_rq_rptr <= r_rq_rptr + 1'b1;
                    r_rq_beat <= '0;
                end else begin
                    r_rq_beat <= r_rq_beat + 8'd1;
                end
            end
        end
    )

endmodule : axi5_atomic_filter

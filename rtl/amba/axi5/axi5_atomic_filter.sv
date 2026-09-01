`timescale 1ns / 1ps
//
// axi5_atomic_filter: read-return atomic termination (BRIDGE-002 A5-3a)
//
// Sits on the AW/W/B CONTROL path at an atomic-enabled boundary whose
// fabric can transport store-class atomics but cannot route the R-channel
// data that load-class atomics return (AtomicLoad 6'b10xxxx and
// AtomicSwap/Compare 6'b11000x respond on R with the AW ID — a write-path
// fabric never sees it, so an unfiltered load-class atomic would hang).
//
//   - AWATOP[5] == 0 (non-atomic and AtomicStore): AW/W/B pass through.
//   - AWATOP[5] == 1 (read-return classes): the AW is accepted upstream
//     but NOT forwarded, its W burst is consumed and discarded, and a
//     local DECERR B response is returned with the AW's ID.
//
// The filter handles handshakes, ATOP, ID, and WLAST only; address/data
// payload buses route around it (connect them straight through — the
// downstream side must qualify payload with m_awvalid/m_wvalid as usual).
// The B payload is an output MUX: downstream responses take priority,
// local DECERRs drain when the downstream B channel is idle.
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
    input  logic          s_wvalid,
    output logic          s_wready,
    input  logic          s_wlast,
    output logic          s_bvalid,
    input  logic          s_bready,
    output logic [IW-1:0] s_bid,
    output logic [1:0]    s_bresp,

    // Downstream (toward the fabric)
    output logic          m_awvalid,
    input  logic          m_awready,
    output logic          m_wvalid,
    input  logic          m_wready,
    input  logic          m_bvalid,
    output logic          m_bready,
    input  logic [IW-1:0] m_bid,
    input  logic [1:0]    m_bresp
);

    // AWATOP[5] set => the atomic returns data on R: swallow it here.
    wire w_swallow = s_awatop[AXI_ATOP_WIDTH-1];

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
    logic [DEPTH_LG2:0]   r_resp_wptr, r_resp_rptr;
    wire                  w_resp_empty = (r_resp_wptr == r_resp_rptr);
    wire                  w_resp_full  =
        (r_resp_wptr[DEPTH_LG2-1:0] == r_resp_rptr[DEPTH_LG2-1:0]) &&
        (r_resp_wptr[DEPTH_LG2]     != r_resp_rptr[DEPTH_LG2]);
    wire [IW-1:0]         w_resp_head  = r_resp_mem[r_resp_rptr[DEPTH_LG2-1:0]];

    // -----------------------------------------------------------------
    // AW path. Forwarded AWs need m_awready; swallowed AWs need queue
    // space only. Both need route-queue space.
    // -----------------------------------------------------------------
    assign m_awvalid = s_awvalid && !w_swallow && !w_route_full;
    assign s_awready = !w_route_full &&
                       (w_swallow ? !w_resp_full : m_awready);

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
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
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
    end

    wire w_local_b_hs = !m_bvalid && !w_resp_empty && s_bready;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_route_wptr <= '0;
            r_route_rptr <= '0;
            r_resp_wptr  <= '0;
            r_resp_rptr  <= '0;
        end else begin
            if (w_aw_hs) begin
                r_route_mem[r_route_wptr[DEPTH_LG2-1:0]] <= w_swallow;
                r_route_wptr <= r_route_wptr + 1'b1;
                if (w_swallow) begin
                    r_resp_mem[r_resp_wptr[DEPTH_LG2-1:0]] <= s_awid;
                    r_resp_wptr <= r_resp_wptr + 1'b1;
                end
            end
            if (w_w_hs_last)
                r_route_rptr <= r_route_rptr + 1'b1;
            if (w_local_b_hs)
                r_resp_rptr <= r_resp_rptr + 1'b1;
        end
    end

endmodule : axi5_atomic_filter

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: descriptor_engine_shared
// Purpose: One descriptor fetch engine serving every channel of a RAPIDS half
//
// Description:
//   Replaces NUM_CHANNELS descriptor_engine instances with one fetch path. The
//   behaviour each scheduler sees is descriptor_engine's, channel for channel:
//   the same kick policy, range refusal of the kicked address, EXT second-chunk
//   fetch, prefetch throttle, autonomous chaining, error pulse, channel reset
//   and completion / error MonBus packets.
//
//   What is shared:
//     - one AR issuer, picked round-robin among the channels that have an
//       address to fetch (the arbitration sits on the scheduler side; the AXI
//       master is owned outright, with no arbiter behind it)
//     - the address-range comparators (kick address at issue, next pointer at
//       chaining time)
//     - the R path: each beat is routed by RID to its channel and written
//       straight into that channel's descriptor FIFO, so there is no 256-bit
//       holding register per channel (except for EXT chunk 0, which must wait
//       for chunk 1)
//     - the MonBus reporter
//
//   What stays per channel: a state code, one pending fetch address, the
//   kick-in-progress flag, the descriptor FIFO (and the EXT chunk-1 FIFO).
//
//   Fetches use ARID = channel, so different channels' fetches overlap on the
//   bus while each channel keeps one fetch in flight and stays in order.
//
//   Difference from descriptor_engine: an R beat for a channel that is not
//   waiting (one that was reset mid-fetch) is accepted and dropped rather than
//   left on the shared R channel, where it would stall every other channel.
//
//   Injection (INJ_EN = 1, the tile's cell-issued descriptors, TILE_SPEC
//   11.11): inj_* hands in a complete descriptor for one channel, a pulse with
//   no backpressure. It waits in that channel's one-entry slot and is written
//   into the channel's FIFO, with no fetch, once the channel's fetch side is
//   idle and the FIFO has room. Idle means no fetch in flight, so an
//   injection never takes the entry an R beat needs. An idle channel starts
//   on it as if kicked; behind a running chain it goes after what that chain
//   queued. Its next pointer chains on into memory as a fetched descriptor's
//   does (the decision is taken at capture). Kicks wait while the slot is
//   full, and the slot waits while a beat is owed (r_owe), so a stale R beat
//   can never answer the chain fetch it starts. A descriptor arriving while
//   the slot is full, while the channel is held in reset, or an EXT one (its
//   second chunk cannot arrive this way) is dropped and sets the channel's
//   sticky inj_dropped bit (cleared by channel reset). A drop is not a
//   descriptor_error: the channel and the work it already holds carry on.
//
// Documentation: projects/components/dma-ip/rapids/docs/rapids_mas/
// Subsystem: rapids_fub
//
// Author: sean galloway
// Created: 2026-10-16

`timescale 1ns / 1ps

`include "reset_defs.svh"
`include "rapids_imports.svh"

module descriptor_engine_shared #(
    parameter int NUM_CHANNELS = 8,
    parameter int CHAN_WIDTH   = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1,
    parameter int ADDR_WIDTH   = 64,
    parameter int AXI_ID_WIDTH = 8,
    parameter int FIFO_DEPTH   = 8,
    parameter int USE_ROW_COL_MAJOR_ADDRESSING = 1,
    // MonBus: agent = MON_AGENT_BASE + channel, channel_id = channel
    parameter logic [15:0] MON_AGENT_BASE = 16'h0010,
    parameter logic [7:0]  MON_UNIT_ID    = 8'h01,
    parameter int MON_FIFO_DEPTH = 4,
    // Second writer into the descriptor FIFOs (cell-issued descriptors)
    parameter bit INJ_EN = 1'b0,
    // INJ_HOLD = 1 (tile straps, rapids TASK-027): inj_* is a valid/ready
    // handshake from the intake queue. A descriptor for a channel whose slot
    // is full waits (inj_ready low) instead of being dropped; one for a
    // channel in reset, or an EXT one, is still taken and dropped.
    parameter bit INJ_HOLD = 1'b0,
    parameter int NC = NUM_CHANNELS,
    parameter int CW = CHAN_WIDTH
) (
    input  logic                              clk,
    input  logic                              rst_n,

    // Per-channel kick (staged descriptor address)
    input  logic [NC-1:0]                     apb_valid,
    output logic [NC-1:0]                     apb_ready,
    input  logic [NC-1:0][ADDR_WIDTH-1:0]     apb_addr,

    // Per-channel scheduler interface
    input  logic [NC-1:0]                     channel_idle,
    output logic [NC-1:0]                     descriptor_valid,
    input  logic [NC-1:0]                     descriptor_ready,
    output logic [NC-1:0][255:0]              descriptor_packet,
    output logic [NC-1:0][255:0]              descriptor_ext_packet,
    output logic [NC-1:0]                     descriptor_error,
    output logic [NC-1:0]                     descriptor_eos,
    output logic [NC-1:0]                     descriptor_eol,
    output logic [NC-1:0]                     descriptor_eod,
    output logic [NC-1:0][1:0]                descriptor_type,

    // AXI4 read master (owned; ARID = channel)
    output logic                              ar_valid,
    input  logic                              ar_ready,
    output logic [ADDR_WIDTH-1:0]             ar_addr,
    output logic [7:0]                        ar_len,
    output logic [2:0]                        ar_size,
    output logic [1:0]                        ar_burst,
    output logic [AXI_ID_WIDTH-1:0]           ar_id,
    output logic                              ar_lock,
    output logic [3:0]                        ar_cache,
    output logic [2:0]                        ar_prot,
    output logic [3:0]                        ar_qos,
    output logic [3:0]                        ar_region,
    input  logic                              r_valid,
    output logic                              r_ready,
    input  logic [255:0]                      r_data,
    input  logic [1:0]                        r_resp,
    input  logic                              r_last,
    input  logic [AXI_ID_WIDTH-1:0]           r_id,

    // Configuration (shared by every channel, as before)
    input  logic                              cfg_prefetch_enable,
    input  logic [3:0]                        cfg_fifo_threshold,
    input  logic [ADDR_WIDTH-1:0]             cfg_addr0_base,
    input  logic [ADDR_WIDTH-1:0]             cfg_addr0_limit,
    input  logic [ADDR_WIDTH-1:0]             cfg_addr1_base,
    input  logic [ADDR_WIDTH-1:0]             cfg_addr1_limit,
    input  logic [NC-1:0]                     cfg_channel_reset,

    // Injected descriptor (INJ_EN): a pulse, never backpressured
    input  logic                              inj_valid,
    input  logic [CW-1:0]                     inj_ch,
    input  logic [255:0]                      inj_data,
    output logic                              inj_ready,     // INJ_HOLD: 0 = the slot is full, hold
    output logic [NC-1:0]                     inj_dropped,   // sticky per channel
    input  logic [NC-1:0]                     inj_dropped_clr, // one-cycle W1C clear (a drop wins)

    output logic [NC-1:0]                     descriptor_engine_idle,

    // MonBus (one stream for every channel)
    input  monitor_common_pkg::monbus_timestamp_t  i_mon_time,
    output logic                                   mon_valid,
    input  logic                                   mon_ready,
    output monitor_common_pkg::monitor_packet_t    mon_packet,
    output monitor_common_pkg::monbus_timestamp_t  mon_timestamp
);

    localparam bit EXT_EN = (USE_ROW_COL_MAJOR_ADDRESSING != 0);
    localparam int DFC_W  = $clog2(FIFO_DEPTH) + 1;
    localparam int FW     = 256 + 5;   // {data, eos, eol, eod, type}

    initial begin
        if (AXI_ID_WIDTH < CW)
            $fatal(1, "AXI_ID_WIDTH (%0d) must be >= CHAN_WIDTH (%0d)", AXI_ID_WIDTH, CW);
    end

    // Per-channel state
    typedef enum logic [2:0] {
        S_IDLE  = 3'd0,   // nothing to fetch
        S_PEND  = 3'd1,   // chunk-0 address pending (kick or chain)
        S_WAIT  = 3'd2,   // chunk-0 AR accepted, waiting for R
        S_PEND2 = 3'd3,   // EXT: chunk-1 AR pending
        S_WAIT2 = 3'd4,   // EXT: chunk-1 AR accepted, waiting for R
        S_ISSUE = 3'd5,   // chunk-0 request in the issue slot
        S_ISSUE2= 3'd6    // EXT: chunk-1 request in the issue slot
    } ch_state_t;

    ch_state_t                    r_st        [NC];
    logic [ADDR_WIDTH-1:0]        r_pend_addr [NC];
    logic [NC-1:0]                r_apb_ip;
    logic [NC-1:0]                r_idle_prev;
    logic [NC-1:0]                r_reset;
    logic [NC-1:0]                r_err;
    logic [NC-1:0]                r_owe;   // reset mid-fetch: one R beat still owed
    // Injection slot, one descriptor per channel (constant 0 unless INJ_EN)
    logic [NC-1:0]                r_inj_v;
    logic [NC-1:0]                r_inj_chain;   // its next pointer chains (decided at capture)
    logic [255:0]                 r_inj_d     [NC];

    // Per-channel FIFO taps
    logic [NC-1:0]                w_fifo_wr_valid;
    logic [NC-1:0]                w_fifo_wr_ready;
    logic [NC-1:0]                w_fifo_rd_valid;
    logic [NC-1:0]                w_fifo_rd_ready;
    logic [DFC_W-1:0]             w_fifo_count [NC];
    logic [FW-1:0]                w_fifo_rd_data [NC];
    logic [FW-1:0]                w_fifo_wr_data;      // one writer per cycle (the R path)
    logic [255:0]                 w_ext_wr_data;

    //=========================================================================
    // Range check helper
    //=========================================================================
    function automatic logic in_range(input logic [ADDR_WIDTH-1:0] a,
                                      input logic [ADDR_WIDTH-1:0] b0, input logic [ADDR_WIDTH-1:0] l0,
                                      input logic [ADDR_WIDTH-1:0] b1, input logic [ADDR_WIDTH-1:0] l1);
        return ((a >= b0) && (a <= l0)) || ((a >= b1) && (a <= l1));
    endfunction

    //=========================================================================
    // Prefetch throttle (descriptor_engine semantics)
    //=========================================================================
    logic [DFC_W-1:0] w_prefetch_limit;
    always_comb begin
        if (!cfg_prefetch_enable || cfg_fifo_threshold == 4'h0)
            w_prefetch_limit = DFC_W'(1);
        else
            w_prefetch_limit = DFC_W'(cfg_fifo_threshold);
    end

    //=========================================================================
    // Issue side: round-robin over channels with an address to fetch
    //=========================================================================
    logic [NC-1:0]  w_req;
    logic           w_pick_valid;
    logic [CW-1:0]  w_pick;
    logic [CW-1:0]  r_rr_ptr;

    // Throttle: descriptor_engine checked its count BEFORE the committing
    // write, so it held up to limit+1 descriptors; "count <= limit" here
    // reproduces that. The CSR threshold can exceed FIFO_DEPTH, so a fetch
    // also needs a free entry: the R beat can then always be written, and
    // one channel's full FIFO never holds the shared R channel.
    logic [NC-1:0] w_allows;
    always_comb begin
        for (int c = 0; c < NC; c++) begin
            w_allows[c] = (w_fifo_count[c] <= w_prefetch_limit) &&
                          (w_fifo_count[c] < DFC_W'(FIFO_DEPTH));
            w_req[c] = !r_reset[c] &&
                       (((r_st[c] == S_PEND) && w_allows[c]) ||
                        (r_st[c] == S_PEND2));
        end
    end

    // Rotate-priority pick starting after the last served channel. No held
    // grant, so a request withdrawn by channel reset can never wedge it.
    always_comb begin
        w_pick_valid = 1'b0;
        w_pick       = r_rr_ptr;
        for (int k = 1; k <= NC; k++) begin
            int idx;
            idx = (int'(r_rr_ptr) + k) % NC;
            if (!w_pick_valid && w_req[idx]) begin
                w_pick_valid = 1'b1;
                w_pick       = CW'(idx);
            end
        end
    end

    // Issue slot. The pick and the 16:1 address mux end at this register;
    // the range check runs on the registered address in the next cycle and
    // drives ARVALID. The chunk-1 +32 is not on this path: it is applied on
    // the R side when chunk 0 arrives (one beat per cycle, one shared adder),
    // so a channel in S_PEND2 already holds its chunk-1 address. Splitting the path there keeps the pick
    // and the four 64-bit compares out of one cycle, and the AR outputs come
    // straight from registers, so ARADDR/ARID are stable while waiting.
    logic                  r_slot_v;
    logic [CW-1:0]         r_slot_ch;
    logic [ADDR_WIDTH-1:0] r_slot_addr;
    logic                  r_slot_c1;
    logic                  w_slot_range_ok;
    logic                  w_range_refuse;  // slot holds a chunk-0 address outside both ranges
    logic                  w_ar_fire;
    logic                  w_slot_free;
    logic                  w_load;

    assign w_slot_range_ok = in_range(r_slot_addr, cfg_addr0_base, cfg_addr0_limit,
                                      cfg_addr1_base, cfg_addr1_limit);
    assign w_range_refuse  = r_slot_v && !r_slot_c1 && !w_slot_range_ok;
    assign ar_valid        = r_slot_v && !w_range_refuse;
    assign w_ar_fire       = ar_valid && ar_ready;
    assign w_slot_free     = !r_slot_v || w_ar_fire || w_range_refuse;
    assign w_load          = w_pick_valid && w_slot_free;

    assign ar_addr   = r_slot_addr;
    assign ar_len    = 8'h00;
    assign ar_size   = 3'b101;        // 32 bytes: one 256-bit descriptor chunk
    assign ar_burst  = 2'b01;
    assign ar_id     = AXI_ID_WIDTH'(r_slot_ch);
    assign ar_lock   = 1'b0;
    assign ar_cache  = 4'b0010;
    assign ar_prot   = 3'b000;
    assign ar_qos    = 4'h0;
    assign ar_region = 4'h0;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_rr_ptr    <= '0;
            r_slot_v    <= 1'b0;
            r_slot_ch   <= '0;
            r_slot_addr <= '0;
            r_slot_c1   <= 1'b0;
        end else begin
            if (w_load) begin
                r_slot_v    <= 1'b1;
                r_slot_ch   <= w_pick;
                r_slot_c1   <= (r_st[w_pick] == S_PEND2);
                r_slot_addr <= r_pend_addr[w_pick];
                r_rr_ptr    <= w_pick;
            end else if (w_ar_fire || w_range_refuse) begin
                r_slot_v    <= 1'b0;
            end
        end
    )

    //=========================================================================
    // R side: route by RID into the channel's FIFO
    //=========================================================================
    logic [CW-1:0]  w_rc;
    logic           w_rc_ok;        // RID names a real channel
    logic           w_rc_waiting;   // that channel is waiting for this beat
    logic           w_rc_chunk1;
    logic           w_r_fire;
    logic           w_resp_ok;
    logic           w_want_ext;
    logic [255:0]   w_chunk0;       // chunk 0 of the completing descriptor
    logic           w_push;         // descriptor completes and is pushed
    logic           w_r_error;      // AXI error response for a waiting channel

    assign w_rc         = r_id[CW-1:0];
    assign w_rc_ok      = (int'(w_rc) < NC);
    assign w_rc_waiting = w_rc_ok && ((r_st[w_rc] == S_WAIT) || (r_st[w_rc] == S_WAIT2));
    assign w_rc_chunk1  = w_rc_ok && (r_st[w_rc] == S_WAIT2);
    // A waiting channel takes the beat when its FIFO has room; any other beat
    // (no such channel, or a channel reset mid-fetch) is drained.
    assign r_ready      = w_rc_waiting ? w_fifo_wr_ready[w_rc] : 1'b1;
    assign w_r_fire     = r_valid && r_ready && w_rc_waiting && !r_reset[w_rc];
    assign w_resp_ok    = (r_resp == 2'b00);
    assign w_want_ext   = EXT_EN && !w_rc_chunk1 &&
                          (r_data[rapids_pkg::DESC_TYPE_HI:rapids_pkg::DESC_TYPE_LO] ==
                           rapids_pkg::RAPIDS_DESC_TYPE_EXT);
    assign w_r_error    = w_r_fire && !w_resp_ok;
    assign w_push       = w_r_fire && w_resp_ok && !w_want_ext;

    // EXT chunk-0 holding registers (only when the feature is compiled in)
    logic [255:0] w_hold_rc;
    generate
    if (EXT_EN) begin : g_hold
        logic [255:0] r_hold [NC];
        `ALWAYS_FF_RST(clk, rst_n,
            if (`RST_ASSERTED(rst_n)) begin
                for (int c = 0; c < NC; c++) r_hold[c] <= '0;
            end else if (w_r_fire && w_resp_ok && w_want_ext) begin
                r_hold[w_rc] <= r_data;
            end
        )
        assign w_hold_rc = r_hold[w_rc];
    end else begin : g_no_hold
        assign w_hold_rc = '0;
    end
    endgenerate

    assign w_chunk0      = w_rc_chunk1 ? w_hold_rc : r_data;

    // The waiting channel's fetch address: +32 is its chunk-1 address (stored
    // when chunk 0 arrives); a chunk-1 completion reports the descriptor's own
    // address, 32 below what is stored.
    logic [ADDR_WIDTH-1:0] w_rc_pend;
    logic [ADDR_WIDTH-1:0] w_rc_pend_p32;
    logic [ADDR_WIDTH-1:0] w_rc_desc_addr;
    assign w_rc_pend      = r_pend_addr[w_rc];
    assign w_rc_pend_p32  = w_rc_pend + ADDR_WIDTH'(32);
    assign w_rc_desc_addr = w_rc_chunk1 ? (w_rc_pend - ADDR_WIDTH'(32)) : w_rc_pend;
    assign w_ext_wr_data = r_data;   // chunk 1 when completing an EXT; don't-care otherwise
    assign w_fifo_wr_data = {w_chunk0,
                             1'b0, 1'b0, 1'b0,   // eos / eol / eod (reserved)
                             w_chunk0[DESC_OPCODE_HI:DESC_OPCODE_LO]};

    // Chaining decision, from chunk 0 of the completing descriptor
    logic [31:0]           w_next_ptr;
    logic [ADDR_WIDTH-1:0] w_next_addr;
    logic                  w_chunk0_valid;
    logic                  w_chain;

    assign w_next_ptr     = w_chunk0[191:160];
    assign w_next_addr    = {{(ADDR_WIDTH-32){1'b0}}, w_next_ptr};
    assign w_chunk0_valid = w_chunk0[192];
    assign w_chain        = (w_next_ptr != '0) && !w_chunk0[194] && w_chunk0_valid &&
                            in_range(w_next_addr, cfg_addr0_base, cfg_addr0_limit,
                                     cfg_addr1_base, cfg_addr1_limit);

    //=========================================================================
    // Injection capture decode. At most one injection arrives per cycle, so
    // one set of comparators serves every channel: EXT refusal and the
    // chaining decision are taken here and stored with the slot.
    //=========================================================================
    logic                  w_inj_ext;
    logic [ADDR_WIDTH-1:0] w_inj_next_addr;
    logic                  w_inj_chain;

    assign w_inj_ext       = EXT_EN &&
                             (inj_data[rapids_pkg::DESC_TYPE_HI:rapids_pkg::DESC_TYPE_LO] ==
                              rapids_pkg::RAPIDS_DESC_TYPE_EXT);
    assign w_inj_next_addr = {{(ADDR_WIDTH-32){1'b0}}, inj_data[191:160]};
    assign w_inj_chain     = (inj_data[191:160] != '0) && !inj_data[194] && inj_data[192] &&
                             in_range(w_inj_next_addr, cfg_addr0_base, cfg_addr0_limit,
                                      cfg_addr1_base, cfg_addr1_limit);

    // INJ_HOLD: the named channel's slot cannot take it this cycle
    logic w_inj_ch_ok;
    assign w_inj_ch_ok = (int'(inj_ch) < NC);
    assign inj_ready   = !INJ_HOLD || !w_inj_ch_ok || r_reset[inj_ch] || w_inj_ext || !r_inj_v[inj_ch];

    //=========================================================================
    // Per-channel state, kick policy, FIFOs
    //=========================================================================
    generate
    for (genvar c = 0; c < NC; c++) begin : g_ch
        logic w_kick;
        logic w_load_here;
        logic w_issue_here;
        logic w_refuse_here;
        logic w_slot_refuses;
        logic w_r_here;
        logic w_err_event;
        logic w_inj_here;     // an injected descriptor for this channel arrives
        logic w_inj_take;     // ...and is captured into the slot
        logic w_inj_drop;     // ...and is refused (slot full, or EXT)
        logic w_inj_wr;       // the slot is written into the FIFO this cycle
        logic [FW-1:0] w_wr_data_c;

        logic w_inj_arrive;
        assign w_inj_arrive = INJ_EN && inj_valid && (inj_ch == CW'(c));
        assign w_inj_here = w_inj_arrive && !r_reset[c];
        assign w_inj_take = w_inj_here && !r_inj_v[c] && !w_inj_ext;
        assign w_inj_drop = w_inj_arrive && (r_reset[c] || (r_inj_v[c] && !INJ_HOLD) || w_inj_ext);
        // S_IDLE: no fetch of this channel is in flight, so the R path cannot
        // be writing this FIFO and needs none of its entries.
        assign w_inj_wr   = INJ_EN && r_inj_v[c] && (r_st[c] == S_IDLE) && !r_reset[c] &&
                            !r_owe[c] && w_fifo_wr_ready[c];

        assign apb_ready[c] = (r_st[c] == S_IDLE) && !r_reset[c] && channel_idle[c] && !r_apb_ip[c] &&
                              !r_owe[c] && !r_inj_v[c];
        assign w_kick        = apb_valid[c] && apb_ready[c];
        assign w_load_here    = w_load && (w_pick == CW'(c));
        assign w_issue_here   = w_ar_fire && (r_slot_ch == CW'(c));
        assign w_refuse_here  = w_range_refuse && (r_slot_ch == CW'(c));
        // this channel's request is in the slot and will be refused (no AR)
        assign w_slot_refuses = r_slot_v && (r_slot_ch == CW'(c)) && !r_slot_c1 && !w_slot_range_ok;
        assign w_r_here      = w_r_fire && (w_rc == CW'(c));
        assign w_err_event   = w_refuse_here || (w_r_here && !w_resp_ok) ||
                               (w_r_here && w_push && !w_chunk0_valid);

        `ALWAYS_FF_RST(clk, rst_n,
            if (`RST_ASSERTED(rst_n)) begin
                r_st[c]        <= S_IDLE;
                r_pend_addr[c] <= '0;
                r_apb_ip[c]    <= 1'b0;
                r_idle_prev[c] <= 1'b1;
                r_reset[c]     <= 1'b0;
                r_err[c]       <= 1'b0;
                r_owe[c]       <= 1'b0;
                r_inj_v[c]     <= 1'b0;
                r_inj_chain[c] <= 1'b0;
                r_inj_d[c]     <= '0;
                inj_dropped[c] <= 1'b0;
            end else begin
                r_reset[c]     <= cfg_channel_reset[c];

                // Sticky drop flag: a channel reset clears it, a drop (even
                // one during that reset) sets it
                if (w_inj_drop)                              inj_dropped[c] <= 1'b1;
                else if (r_reset[c] || inj_dropped_clr[c])   inj_dropped[c] <= 1'b0;

                if (w_inj_take) begin
                    r_inj_v[c]     <= 1'b1;
                    r_inj_d[c]     <= inj_data;
                    r_inj_chain[c] <= w_inj_chain;
                end else if (w_inj_wr) begin
                    r_inj_v[c]     <= 1'b0;
                end

                // Owed beat: a reset mid-fetch leaves the beat in flight. It
                // is drained when it arrives (the channel is no longer
                // waiting), and no new kick is taken until then, so it can
                // never be mistaken for the answer to a new fetch on the same
                // ARID.
                if (r_owe[c] && r_valid && r_ready && w_rc_ok && (w_rc == CW'(c)))
                    r_owe[c] <= 1'b0;
                // A request already in the slot still issues (ARVALID may be
                // up), so a reset there owes the beat too, unless the slot
                // is about to refuse it.
                if (r_reset[c] && ((r_st[c] == S_WAIT) || (r_st[c] == S_WAIT2) ||
                                   (r_st[c] == S_ISSUE2) ||
                                   ((r_st[c] == S_ISSUE) && !w_slot_refuses)))
                    r_owe[c] <= 1'b1;
                r_idle_prev[c] <= channel_idle[c];

                // Error pulse: one cycle per event; held while a zero kick
                // address is presented (descriptor_engine's addr-0 rule).
                r_err[c] <= w_err_event || (apb_valid[c] && (apb_addr[c] == '0));

                if (r_reset[c]) begin
                    r_st[c]     <= S_IDLE;
                    r_apb_ip[c] <= 1'b0;
                    r_err[c]    <= 1'b0;
                    r_inj_v[c]  <= 1'b0;
                end else begin
                    // Kick-in-progress: set on accept, cleared when the
                    // scheduler returns to idle (rising edge).
                    if (w_kick)
                        r_apb_ip[c] <= 1'b1;
                    else if (!r_idle_prev[c] && channel_idle[c] && r_apb_ip[c])
                        r_apb_ip[c] <= 1'b0;

                    case (r_st[c])
                        S_IDLE: if (w_kick) begin
                            r_st[c]        <= S_PEND;
                            r_pend_addr[c] <= apb_addr[c];
                        end else if (w_inj_wr && r_inj_chain[c]) begin
                            // the injected descriptor chains on into memory
                            r_st[c]        <= S_PEND;
                            r_pend_addr[c] <= {{(ADDR_WIDTH-32){1'b0}}, r_inj_d[c][191:160]};
                        end
                        S_PEND:  if (w_load_here) r_st[c] <= S_ISSUE;
                        S_ISSUE: begin
                            if (w_refuse_here)     r_st[c] <= S_IDLE;
                            else if (w_issue_here) r_st[c] <= S_WAIT;
                        end
                        S_WAIT: if (w_r_here) begin
                            if (!w_resp_ok)      r_st[c] <= S_IDLE;
                            else if (w_want_ext) begin
                                r_st[c]        <= S_PEND2;
                                r_pend_addr[c] <= w_rc_pend_p32;   // chunk-1 address
                            end
                            else if (w_chain) begin
                                r_st[c]        <= S_PEND;
                                r_pend_addr[c] <= w_next_addr;
                            end else             r_st[c] <= S_IDLE;
                        end
                        S_PEND2:  if (w_load_here)  r_st[c] <= S_ISSUE2;
                        S_ISSUE2: if (w_issue_here) r_st[c] <= S_WAIT2;
                        S_WAIT2: if (w_r_here) begin
                            if (!w_resp_ok) r_st[c] <= S_IDLE;
                            else if (w_chain) begin
                                r_st[c]        <= S_PEND;
                                r_pend_addr[c] <= w_next_addr;
                            end else        r_st[c] <= S_IDLE;
                        end
                        default: r_st[c] <= S_IDLE;
                    endcase
                end
            end
        )

        // Two writers, never at once: the R path writes only a waiting
        // channel, the injection slot only an idle one.
        assign w_fifo_wr_valid[c] = (w_push && (w_rc == CW'(c))) || w_inj_wr;
        assign w_wr_data_c        = w_inj_wr ? {r_inj_d[c], 3'b000,
                                                r_inj_d[c][DESC_OPCODE_HI:DESC_OPCODE_LO]}
                                             : w_fifo_wr_data;
        // While the channel is reset its FIFO drains, so descriptors
        // prefetched for the aborted chain are not delivered afterwards.
        assign w_fifo_rd_ready[c] = r_reset[c] ? 1'b1 : descriptor_ready[c];

        gaxi_fifo_sync #(
            .DATA_WIDTH (FW),
            .DEPTH      (FIFO_DEPTH)
        ) u_desc_fifo (
            .axi_aclk    (clk),
            .axi_aresetn (rst_n),
            .wr_valid    (w_fifo_wr_valid[c]),
            .wr_ready    (w_fifo_wr_ready[c]),
            .wr_data     (w_wr_data_c),
            .rd_valid    (w_fifo_rd_valid[c]),
            .rd_ready    (w_fifo_rd_ready[c]),
            .rd_data     (w_fifo_rd_data[c]),
            .count       (w_fifo_count[c])
        );

        if (EXT_EN) begin : g_ext
            gaxi_fifo_sync #(
                .DATA_WIDTH (256),
                .DEPTH      (FIFO_DEPTH)
            ) u_ext_fifo (                    // lockstep with u_desc_fifo
                .axi_aclk    (clk),
                .axi_aresetn (rst_n),
                .wr_valid    (w_fifo_wr_valid[c]),
                .wr_ready    (),
                .wr_data     (w_ext_wr_data),
                .rd_valid    (),
                .rd_ready    (w_fifo_rd_ready[c]),
                .rd_data     (descriptor_ext_packet[c]),
                .count       ()
            );
        end else begin : g_no_ext
            assign descriptor_ext_packet[c] = '0;
        end

        assign descriptor_valid[c]       = w_fifo_rd_valid[c] && !r_err[c] && !r_reset[c];
        assign descriptor_packet[c]      = w_fifo_rd_data[c][FW-1:5];
        assign descriptor_eos[c]         = w_fifo_rd_data[c][4];
        assign descriptor_eol[c]         = w_fifo_rd_data[c][3];
        assign descriptor_eod[c]         = w_fifo_rd_data[c][2];
        assign descriptor_type[c]        = w_fifo_rd_data[c][1:0];
        assign descriptor_error[c]       = r_err[c];
        assign descriptor_engine_idle[c] = (r_st[c] == S_IDLE) && !r_reset[c] && !w_fifo_rd_valid[c] &&
                                           !r_inj_v[c];
    end
    endgenerate

    //=========================================================================
    // MonBus: completion on push, error on refusal / AXI error
    //=========================================================================
    // Up to two events per cycle (a refusal on the issue side, a completion or
    // error on the R side). Both enter a small FIFO; descriptor_engine drops a
    // packet that meets backpressure, and so does this one when the FIFO is
    // full.
    localparam int MPW = $bits(monitor_common_pkg::monitor_packet_t) +
                         $bits(monitor_common_pkg::monbus_timestamp_t);

    logic                                  w_ev_r;
    monitor_common_pkg::monitor_packet_t   w_pkt_r;
    monitor_common_pkg::monitor_packet_t   w_pkt_i;
    logic                                  r_mv_i, r_mv_r;
    logic [MPW-1:0]                        r_md_i, r_md_r;

    assign w_ev_r  = w_r_fire && (!w_resp_ok || w_push);
    assign w_pkt_r = w_resp_ok ?
        create_monitor_packet(PktTypeCompletion, PROTOCOL_CORE, CORE_COMPL_DESCRIPTOR_LOADED,
                              9'(w_rc), MON_UNIT_ID, MON_AGENT_BASE + 16'(w_rc),
                              64'(w_rc_desc_addr)) :
        create_monitor_packet(PktTypeError, PROTOCOL_CORE, CORE_ERR_DESCRIPTOR_ENGINE,
                              9'(w_rc), MON_UNIT_ID, MON_AGENT_BASE + 16'(w_rc),
                              {46'h0, r_resp, 16'h0});
    assign w_pkt_i = create_monitor_packet(PktTypeError, PROTOCOL_CORE, CORE_ERR_DESCRIPTOR_ENGINE,
                                           9'(r_slot_ch), MON_UNIT_ID, MON_AGENT_BASE + 16'(r_slot_ch),
                                           64'h0);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_mv_i <= 1'b0; r_md_i <= '0;
            r_mv_r <= 1'b0; r_md_r <= '0;
        end else begin
            r_mv_i <= w_range_refuse;
            r_md_i <= {w_pkt_i, i_mon_time};
            r_mv_r <= w_ev_r;
            r_md_r <= {w_pkt_r, i_mon_time};
        end
    )

    // Two registered event slots drain into the FIFO, R side first.
    logic           r_hold_i_valid;
    logic [MPW-1:0] r_hold_i_data;
    logic           w_mf_wr_valid, w_mf_wr_ready;
    logic [MPW-1:0] w_mf_wr_data, w_mf_rd_data;

    always_comb begin
        if (r_mv_r) begin
            w_mf_wr_valid = 1'b1;
            w_mf_wr_data  = r_md_r;
        end else if (r_hold_i_valid) begin
            w_mf_wr_valid = 1'b1;
            w_mf_wr_data  = r_hold_i_data;
        end else begin
            w_mf_wr_valid = r_mv_i;
            w_mf_wr_data  = r_md_i;
        end
    end

    // An issue-side event that loses to an R-side event the same cycle waits
    // one cycle in r_hold_i; a second collision while it waits drops it.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_hold_i_valid <= 1'b0;
            r_hold_i_data  <= '0;
        end else begin
            if (r_mv_r && r_mv_i) begin
                r_hold_i_valid <= 1'b1;
                r_hold_i_data  <= r_md_i;
            end else if (!r_mv_r && r_hold_i_valid) begin
                r_hold_i_valid <= r_mv_i;     // the waiting one went; a new one waits
                r_hold_i_data  <= r_md_i;
            end
        end
    )

    gaxi_fifo_sync #(
        .DATA_WIDTH (MPW),
        .DEPTH      (MON_FIFO_DEPTH)
    ) u_mon_fifo (
        .axi_aclk    (clk),
        .axi_aresetn (rst_n),
        .wr_valid    (w_mf_wr_valid),
        .wr_ready    (w_mf_wr_ready),
        .wr_data     (w_mf_wr_data),
        .rd_valid    (mon_valid),
        .rd_ready    (mon_ready),
        .rd_data     (w_mf_rd_data),
        .count       ()
    );

    assign mon_packet    = w_mf_rd_data[MPW-1 -: $bits(monitor_common_pkg::monitor_packet_t)];
    assign mon_timestamp = w_mf_rd_data[$bits(monitor_common_pkg::monbus_timestamp_t)-1:0];

    // r_last is single-beat by construction (ARLEN = 0)
    logic unused_ok;
    assign unused_ok = &{1'b0, r_last};

endmodule : descriptor_engine_shared

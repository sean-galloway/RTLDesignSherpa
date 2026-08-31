// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_addr_check
// Purpose: Configurable N-range address ALLOWLIST checker for AXI monitors
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba

`timescale 1ns / 1ps

`include "reset_defs.svh"

/**
 * AXI Monitor — Address-Range Allowlist Checker
 *
 * Watches the cmd_addr / cmd_valid / cmd_ready handshake already snooped by
 * axi_monitor_base. The N user-configured [low, high] inclusive ranges are
 * treated as an ALLOWLIST of expected addresses, and each accepted command
 * produces up to TWO packets on the shared addr_pkt_* stream (see the
 * DEBUG/ERROR split note below -- this banner used to say "at most one",
 * which predated per-range flavors and was the source the docs copied):
 *
 *   - MATCH  (address lands in >=1 enabled range), gated by cfg_debug_enable:
 *         packet_type = PktTypeAddrMatch   (4'h8)
 *         event_code  = AXI_ADDR_RANGE_MATCH (8'h01)
 *         event_data[63:60] = range_index (lowest matching range)
 *
 *   - MISS   (address in NO enabled range), gated by cfg_error_enable:
 *         packet_type = PktTypeError       (4'h0)
 *         event_code  = AXI_ERR_ADDR_RANGE (8'h0D)
 *         event_data[63:60] = 4'hF (no-range sentinel)
 *
 * In both cases:
 *         protocol          = PROTOCOL_AXI (4'h0)
 *         event_data[59: 0] = full cmd_addr (zero-padded if narrower)
 *
 * MATCH and MISS are NOT mutually exclusive. Per-range flavors
 * (ADDR_RANGE_IS_ERROR) evaluate the DEBUG watch-list and the ERROR allowlist
 * independently, so one command can hit a debug range (MATCH) while falling
 * outside every error range (MISS). Two pending slots hold both and the
 * output stream serializes them -- see the detailed comment at the flavor
 * split below, which is the authority.
 * The is_read flag is dropped from the encoding — read vs. write is recovered
 * from the IS_READ build parameter and the (unit_id, agent_id) of the
 * emitting monitor. Range index occupies 4 bits (up to 16 ranges); if
 * N_ADDR_RANGES grows beyond 16, widen the index field by chopping address
 * bits.
 *
 * Coalescing (lossy-but-honest, matching the monitor's trans_mgr philosophy):
 *   MATCH events coalesce per range (one pending slot + latched address each,
 *   latest hit per range wins). MISS events coalesce into a single pending
 *   slot (latest miss wins). One packet drains per cycle; MISS (error) has
 *   priority over MATCH, then lowest-index range. Events produced while a slot
 *   is already pending and the bus is stalled overwrite the latched address.
 *
 * Side-band timestamp:
 *   The free-running `i_mon_time` is sampled combinationally and driven out on
 *   `addr_pkt_timestamp` alongside the packet.
 *
 * When cfg_addr_check_enable is 0 the module is fully quiescent
 * (addr_pkt_valid stays low, no flops update). cfg_debug_enable /
 * cfg_error_enable independently gate the MATCH / MISS report paths.
 */
module axi_monitor_addr_check
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    parameter int N_ADDR_RANGES = 4,             // number of independent ranges (>=1)
    parameter int ADDR_WIDTH    = 32,            // address width
    parameter int ID_WIDTH      = 6,             // cmd_id width (clipped to 9 bits for channel_id)
    parameter logic [7:0]  UNIT_ID  = 8'h00,     // 8-bit Unit ID in monitor packets
    parameter logic [15:0] AGENT_ID = 16'h0000,  // 16-bit Agent ID in monitor packets
    parameter bit IS_READ       = 1'b1,          // 1 if this monitor watches reads (AR), 0 if writes (AW)

    // Per-range flavor selector: bit i picks how range i behaves.
    //   0 = DEBUG range  -> a hit emits an AddrMatch packet (cfg_debug_enable)
    //   1 = ERROR range  -> the enabled ERROR ranges form an allowlist; a
    //                       command whose address is in NONE of them emits an
    //                       Error/ADDR_RANGE packet (cfg_error_enable)
    // Default all-0: every range is a debug/match range, so the ERROR/miss
    // path is inert until a consumer marks ranges as error -> "unused by
    // default".
    parameter logic [N_ADDR_RANGES-1:0] ADDR_RANGE_IS_ERROR = '0,

    // Local widths
    parameter int M  = ADDR_WIDTH,
    parameter int IW = ID_WIDTH
)
(
    input  logic                                       clk,
    input  logic                                       aresetn,

    // Free-running counter from the monbus_group family, broadcast to every wrapper
    input  monbus_timestamp_t                          i_mon_time,

    // Snooped command stream (tap point: same wires as axi_monitor_base sees)
    input  logic [M-1:0]                               cmd_addr,
    input  logic [IW-1:0]                              cmd_id,
    input  logic                                       cmd_valid,
    input  logic                                       cmd_ready,

    // Range configuration
    input  logic                                       cfg_addr_check_enable,           // master on/off
    input  logic                                       cfg_debug_enable,                // enable MATCH (AddrMatch) path
    input  logic                                       cfg_error_enable,                // enable MISS  (Error) path
    input  logic [N_ADDR_RANGES-1:0]                   cfg_addr_range_enable,           // per-range enable
    input  logic [N_ADDR_RANGES-1:0][M-1:0]            cfg_addr_range_low,              // inclusive low
    input  logic [N_ADDR_RANGES-1:0][M-1:0]            cfg_addr_range_high,             // inclusive high

    // Outgoing monbus packet (consumer typically merges with reporter stream)
    output logic                                       addr_pkt_valid,
    input  logic                                       addr_pkt_ready,
    output monitor_packet_t                            addr_pkt_data,
    output monbus_timestamp_t                          addr_pkt_timestamp
);

    // -------------------------------------------------------------------------
    // Combinational range hits + two-flavor allowlist decision
    // -------------------------------------------------------------------------
    // DEBUG ranges (ADDR_RANGE_IS_ERROR[i]=0) and ERROR ranges (=1) are
    // evaluated independently, so a single command can legitimately produce
    // both a MATCH (it hit a debug watch) and a MISS (it was outside the error
    // allowlist); the two pending slots below hold each and the output stream
    // serialises them.
    logic                       cmd_fire;
    logic [N_ADDR_RANGES-1:0]   raw_hit;      // address in enabled range i
    assign cmd_fire = cmd_valid && cmd_ready && cfg_addr_check_enable;

    always_comb begin
        for (int i = 0; i < N_ADDR_RANGES; i++) begin
            raw_hit[i] = cfg_addr_range_enable[i] &&
                         (cmd_addr >= cfg_addr_range_low[i]) &&
                         (cmd_addr <= cfg_addr_range_high[i]);
        end
    end

    // Split by flavor.
    logic [N_ADDR_RANGES-1:0]   debug_hit;       // hit in a DEBUG-flavored range
    logic [N_ADDR_RANGES-1:0]   err_range_en;    // enabled ERROR-flavored ranges
    logic                       err_hit;         // address in some enabled ERROR range
    logic                       err_ranges_exist;
    always_comb begin
        for (int i = 0; i < N_ADDR_RANGES; i++) begin
            debug_hit[i]    = raw_hit[i] && !ADDR_RANGE_IS_ERROR[i];
            err_range_en[i] = cfg_addr_range_enable[i] && ADDR_RANGE_IS_ERROR[i];
        end
    end
    assign err_hit          = |(raw_hit & ADDR_RANGE_IS_ERROR);
    assign err_ranges_exist = |err_range_en;

    // Per-command events:
    //   match_set[i] : DEBUG range i hit and the MATCH path is enabled
    //   miss_set     : the ERROR allowlist is active but the address matched
    //                  none of it
    logic [N_ADDR_RANGES-1:0]   match_set;
    logic                       miss_set;
    always_comb begin
        for (int i = 0; i < N_ADDR_RANGES; i++)
            match_set[i] = cmd_fire && cfg_debug_enable && debug_hit[i];
    end
    assign miss_set = cmd_fire && cfg_error_enable && err_ranges_exist && !err_hit;

    // -------------------------------------------------------------------------
    // Pending state: per-range MATCH slots + a single MISS slot
    // -------------------------------------------------------------------------
    logic [N_ADDR_RANGES-1:0]               r_match_pending;
    logic [N_ADDR_RANGES-1:0][M-1:0]        r_match_addr;
    logic [N_ADDR_RANGES-1:0][IW-1:0]       r_match_id;

    logic                                   r_miss_pending;
    logic [M-1:0]                           r_miss_addr;
    logic [IW-1:0]                          r_miss_id;

    // Emission arbitration: MISS (error) first, then lowest-index MATCH range.
    logic [N_ADDR_RANGES-1:0] match_emit_oh;
    logic                     match_emit_any;
    logic [3:0]               match_emit_idx;
    assign match_emit_any = |r_match_pending;
    always_comb begin
        match_emit_oh  = '0;
        match_emit_idx = 4'h0;
        for (int i = 0; i < N_ADDR_RANGES; i++) begin
            if (r_match_pending[i] && match_emit_oh == '0) begin
                match_emit_oh[i] = 1'b1;
                match_emit_idx   = 4'(i);
            end
        end
    end

    // Per-range shadow slot. A MATCH hit arriving while THAT range's packet is
    // already on the bus must not rewrite the beat being presented: the monbus
    // is valid/ready, so the payload has to hold until the beat is accepted.
    // The newer hit is buffered here and installed on accept, which keeps
    // "newest wins" for every beat except the one already on the wire.
    logic [N_ADDR_RANGES-1:0]         r_shadow_valid;
    logic [N_ADDR_RANGES-1:0][M-1:0]  r_shadow_addr;
    logic [N_ADDR_RANGES-1:0][IW-1:0] r_shadow_id;

    logic emit_is_miss;                       // 1 = emit the MISS/error slot this cycle
    assign emit_is_miss = r_miss_pending;

    assign addr_pkt_valid = (r_miss_pending || match_emit_any) && cfg_addr_check_enable;
    logic accept;
    assign accept = addr_pkt_valid && addr_pkt_ready;

    // This range's packet is on the bus right now / is accepted this cycle.
    logic [N_ADDR_RANGES-1:0] w_presented, w_range_accept;
    always_comb begin
        for (int i = 0; i < N_ADDR_RANGES; i++) begin
            w_presented[i]    = addr_pkt_valid && !emit_is_miss && match_emit_oh[i];
            w_range_accept[i] = accept        && !emit_is_miss && match_emit_oh[i];
        end
    end

    `ALWAYS_FF_RST(clk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_match_pending <= '0;
            r_shadow_valid  <= '0;
            r_shadow_addr   <= '0;
            r_shadow_id     <= '0;
            r_match_addr    <= '0;
            r_match_id      <= '0;
            r_miss_pending  <= 1'b0;
            r_miss_addr     <= '0;
            r_miss_id       <= '0;
        end else begin
            // 1) MATCH payload. A fresh hit updates the latched address ONLY
            //    when that range's beat is not currently being presented --
            //    rewriting a beat already on the bus would change the payload
            //    under a held valid, which the monbus valid/ready contract
            //    forbids. While presented, the hit goes to the shadow slot and
            //    is installed when the beat is accepted, so "newest wins"
            //    still holds for every beat except the one on the wire.
            for (int i = 0; i < N_ADDR_RANGES; i++) begin
                if (w_range_accept[i]) begin
                    // Beat consumed: install whatever queued behind it, newest
                    // first (a hit this cycle beats an older shadow).
                    if (match_set[i]) begin
                        r_match_addr[i] <= cmd_addr;
                        r_match_id  [i] <= cmd_id;
                    end else if (r_shadow_valid[i]) begin
                        r_match_addr[i] <= r_shadow_addr[i];
                        r_match_id  [i] <= r_shadow_id  [i];
                    end
                end else if (match_set[i] && !w_presented[i]) begin
                    r_match_addr[i] <= cmd_addr;
                    r_match_id  [i] <= cmd_id;
                end
            end
            // 2) Shadow slot: filled by a hit that lands while the beat is
            //    presented, emptied when that beat is accepted (its value
            //    having just been installed above).
            for (int i = 0; i < N_ADDR_RANGES; i++) begin
                if (w_range_accept[i]) begin
                    r_shadow_valid[i] <= 1'b0;
                end else if (match_set[i] && w_presented[i]) begin
                    r_shadow_valid[i] <= 1'b1;
                    r_shadow_addr [i] <= cmd_addr;
                    r_shadow_id   [i] <= cmd_id;
                end
            end
            // 3) MATCH pending bits: set on hit; on accept stay pending only
            //    if a buffered hit remains to be emitted. Set wins on collision.
            for (int i = 0; i < N_ADDR_RANGES; i++) begin
                if (match_set[i])
                    r_match_pending[i] <= 1'b1;
                else if (w_range_accept[i])
                    r_match_pending[i] <= r_shadow_valid[i];
            end

            // 3) MISS slot: latch address on new miss; set/clear pending
            //    (set wins on collision with an emit of the miss slot).
            if (miss_set) begin
                r_miss_addr <= cmd_addr;
                r_miss_id   <= cmd_id;
            end
            if (miss_set)
                r_miss_pending <= 1'b1;
            else if (accept && emit_is_miss)
                r_miss_pending <= 1'b0;
        end
    )

    // -------------------------------------------------------------------------
    // Pack the emitted packet (128-bit format, 64-bit event_data)
    // -------------------------------------------------------------------------
    // event_data[63:60] = range_index (MATCH: matching range; MISS: 4'hF)
    // event_data[59: 0] = cmd_addr (full address, zero-padded if narrower)
    localparam logic [3:0] MISS_RANGE_SENTINEL = 4'hF;

    logic [3:0]     pkt_type_field;
    logic [7:0]     event_code_field;
    logic [3:0]     emit_idx;
    logic [M-1:0]   emit_addr;
    logic [IW-1:0]  emit_id;
    logic [8:0]     channel_id_field;
    logic [63:0]    event_data_field;
    logic [59:0]    addr_payload;

    always_comb begin
        if (emit_is_miss) begin
            pkt_type_field   = PktTypeError;
            event_code_field = AXI_ERR_ADDR_RANGE;      // 8'h0D
            emit_idx         = MISS_RANGE_SENTINEL;
            emit_addr        = r_miss_addr;
            emit_id          = r_miss_id;
        end else begin
            pkt_type_field   = PktTypeAddrMatch;
            event_code_field = AXI_ADDR_RANGE_MATCH;    // 8'h01
            emit_idx         = match_emit_idx;
            emit_addr        = '0;
            emit_id          = '0;
            for (int i = 0; i < N_ADDR_RANGES; i++) begin
                if (match_emit_oh[i]) begin
                    emit_addr = r_match_addr[i];
                    emit_id   = r_match_id[i];
                end
            end
        end
    end

    // channel_id is 9 bits in the packet — clip or zero-extend cmd_id.
    // Done as a generate-if so the dead branch's replication count never
    // goes negative when IW >= 9 (Verilator elaborates both arms of a
    // ternary and flags the negative {{(9-IW){...}}} otherwise).
    if (IW >= 9) begin : g_chan_id_wide
        assign channel_id_field = emit_id[8:0];
    end else begin : g_chan_id_narrow
        assign channel_id_field = {{(9-IW){1'b0}}, emit_id};
    end

    // Pad / truncate the address into the 60-bit payload slot.
    if (M >= 60) begin : g_addr_wide
        assign addr_payload = emit_addr[59:0];
    end else begin : g_addr_narrow
        assign addr_payload = {{(60-M){1'b0}}, emit_addr};
    end

    assign event_data_field = {emit_idx[3:0], addr_payload};

    assign addr_pkt_data = create_monitor_packet(
        pkt_type_field,                  // [127:124] packet_type
        protocol_type_t'(PROTOCOL_AXI),  // [108:105] protocol
        event_code_field,                // [104: 97] event_code
        channel_id_field,                // [ 96: 88] channel_id
        UNIT_ID,                         // [ 71: 64] unit_id
        AGENT_ID,                        // [ 87: 72] agent_id
        event_data_field                 // [ 63:  0] event_data
    );

    // Sample the broadcast monitor time on the cycle the packet asserts valid
    // (purely combinational pass-through — packet/timestamp move together).
    assign addr_pkt_timestamp = i_mon_time;

endmodule : axi_monitor_addr_check

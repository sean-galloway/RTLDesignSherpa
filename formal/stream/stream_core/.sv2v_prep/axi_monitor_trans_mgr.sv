// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_trans_mgr
// Purpose: AXI Monitor Transaction Manager (CAM-backed).
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18 (original) / 2026-06-08 (CAM-backed rewrite)
//
// ============================================================================
// Tracks AXI transactions through their lifecycle, handling out-of-order
// phase arrivals. Per-transaction (valid, id, payload) storage and the
// addr/data/resp ID-lookup + free-slot + priority-encoded alloc logic
// live in the shared monitor_trans_cam module; this module owns the
// trans-mgr-specific FSM (per-slot next-payload computation, cleanup
// eligibility, event_reported feedback, active_count).
//
// This version delegates to monitor_trans_cam:
//
//   * 3 ID lookup ports (addr/data/resp) -> monitor_trans_cam
//   * free-slot vector + 3 priority-encoded alloc one-hots -> monitor_trans_cam
//   * per-slot registered storage of (valid, id, payload) -> monitor_trans_cam
//
// The trans_mgr still owns:
//
//   * The WID-less write-data match (state predicate over the payload,
//     not an id match -- the CAM can't see state, only id).
//   * The per-slot combinational next-payload computation (the
//     "what does the new bus_transaction_t look like after this cycle's
//     handshakes" logic, copied from the production always_ff with
//     non-blocking writes turned into blocking assignments to a `next`
//     temporary).
//   * The wants_alloc derivation (= input_handshake && !hit_any).
//   * Cleanup, event_reported, active_count -- the trans-mgr-specific
//     status outputs.
//
// CAM payload contains the full bus_transaction_t (including its `id`
// field) for clean unpack to the trans_table output port. The CAM's
// `entry_id` port is the actual lookup key; trans_mgr writes both
// atomically so they always agree.
//
// Synthesis intent: each slot's next-state lives in its own always_comb
// inside a generate loop, so synth still sees N independent small
// update cones rather than one fused cone. The CAM's per-slot
// registered storage preserves the production module's "16 parallel
// small update cones" shape.
// ============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_monitor_trans_mgr
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    parameter int MAX_TRANSACTIONS    = 16,   // Maximum outstanding transactions
    parameter int ADDR_WIDTH          = 32,   // Width of address bus
    parameter int ID_WIDTH            = 8,    // Width of ID bus
    parameter bit IS_READ             = 1'b1, // 1 for read, 0 for write
    parameter bit IS_AXI              = 1'b1, // 1 for AXI, 0 for AXI-Lite
    parameter bit ENABLE_PERF_PACKETS = 1'b0, // Enable performance metrics tracking

    // Write-data ordering queue (writes only; ignored when IS_READ=1).
    //
    // AXI4 gives W beats no WID and requires them to be consumed in AW ISSUE
    // ORDER. The default path recovers that order by ranking every live entry
    // by age and running an O(N^2) oldest-select (pick_oldest) over the whole
    // table -- the structure that stops closing timing past ~16 slots.
    //
    // The order is already known at AW time, so it does not need to be
    // rediscovered per beat: push the slot on the AW handshake, pop it on
    // W last, and the head IS the target. O(1), no age ranks, no cross-slot
    // compare -- which is also what makes the table bankable, since every
    // remaining lookup is then keyed by ID.
    //
    // Default 0 -> the age-rank path, bit-identical to before.
    parameter bit USE_WDATA_ORDER_Q   = 1'b0,

    // Age/rank banking by low ID bits (1 = off, today's behaviour).
    //
    // The table's two O(N^2) structures are BOTH here, not in the CAM:
    // pick_oldest (every candidate compared against every other) and the rank
    // update (every survivor counting the freed entries ranked below it). The
    // CAM itself is per-slot compare plus a priority encode -- O(N) area, log
    // depth -- so it does not need replicating; measured 16 slots at
    // WNS +1.018 ns vs 40 at -25.183 ns is these two loops.
    //
    // Slot i belongs to bank i/(N/NUM_BANKS); an ID lands in bank
    // id[$clog2(NUM_BANKS)-1:0]. Every entry sharing an ID therefore shares a
    // bank, so both loops can be restricted to same-bank pairs and stay EXACT
    // -- ranks are only ever compared within a bank once USE_WDATA_ORDER_Q
    // carries the WID-less write order (that was the one cross-ID compare).
    //
    // The guards below are elaboration-time constants, so cross-bank
    // comparators are never generated: area falls from O(N^2) to
    // NUM_BANKS * O((N/NUM_BANKS)^2) -- 4096 -> 1024 terms at N=64, B=4, each
    // bank the size that is known to close.
    //
    // SIZING RULE -- the one that bites. Every transaction sharing an ID lands
    // in the SAME bank, so per-ID concurrency is capped by the BANK depth, not
    // by MAX_TRANSACTIONS:
    //
    //     MAX_TRANSACTIONS/NUM_BANKS >= (IDs per bank) * (outstanding per ID)
    //
    // The observer case: 8 channels x 8 outstanding over 4 banks = 2 channels
    // x 8 = 16 per bank, so MAX_TRANSACTIONS=64 with NUM_BANKS=4 -- and 16 is
    // the depth measured to close (WNS +1.018 ns).
    //
    // Undersize it and entries are refused rather than mis-tracked:
    // val/amba/test_axi_monitor_trans_mgr drives 4 outstanding on one ID and
    // reports "four outstanding AR(id=2) occupy 2 slot(s), expected 4" at
    // N=8/B=4 (2 per bank), while N=16/B=4 (4 per bank) passes. That is the
    // table being too small for the traffic, not a tracking defect -- but it
    // surfaces three layers up as missing packets, so size it deliberately.
    parameter int NUM_BANKS           = 1,

    // Short params (kept for API compatibility with the production module)
    parameter int AW                  = ADDR_WIDTH,
    parameter int IW                  = ID_WIDTH,

    // Address-range packet filter (TASK-015).
    //
    // Filters at REPORT time, not at admission. A filtered transaction is
    // still allocated and tracked exactly as before -- only its packets are
    // suppressed. That is deliberate: address exists ONLY on the command
    // channel, so refusing the ALLOCATION would leave the transaction's data
    // and resp beats arriving with no entry to match, landing in the
    // deliberately-ungated unmatched-data path and emitting ORPHAN ERRORS.
    // Filtering to reduce packet traffic would then increase it.
    //
    // Cost of doing it here instead: MAX_TRANSACTIONS flops. Doing it at
    // admission would need a counter per POSSIBLE id (2**ID_WIDTH counters,
    // 1280 flops at ID_WIDTH=8/MAX_TRANSACTIONS=16, ~20k at ID_WIDTH=12),
    // because one id can hold several outstanding transactions straddling the
    // range so a flag per id is not enough.
    //
    // Default 0 -> filtered_mask is always 0 and the build is bit-identical.
    parameter bit ADDR_FILTER_ENABLE  = 1'b0
)
(
    // Global Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,
    // Synchronous clear: empty the transaction CAM and zero the active-count
    // pipeline on the next edge (no full rst_n). Pulse only when idle.
    input  logic                        clear,

    // Address channel
    input  logic                        cmd_valid,
    input  logic                        cmd_ready,
    input  logic [IW-1:0]               cmd_id,
    input  logic [AW-1:0]               cmd_addr,
    input  logic [7:0]                  cmd_len,
    input  logic [2:0]                  cmd_size,
    input  logic [1:0]                  cmd_burst,

    // Data channel
    input  logic                        data_valid,
    input  logic                        data_ready,
    input  logic [IW-1:0]               data_id,
    input  logic                        data_last,
    input  logic [1:0]                  data_resp,

    // Response channel (write only)
    input  logic                        resp_valid,
    input  logic                        resp_ready,
    input  logic [IW-1:0]               resp_id,
    input  logic [1:0]                  resp_code,

    // Timestamp input
    input  logic [31:0]                 timestamp,

    // Event reported feedback from reporter (FIX-001)
    input  logic [MAX_TRANSACTIONS-1:0] i_event_reported_flags,

    // Timeout feedback from axi_monitor_timeout (issue #41).
    // The timeout block detects the stall but owns only a private copy of
    // the table, so it cannot move the entry to a terminal state. Without
    // this input a timed-out slot stays in ADDR/DATA phase forever, is
    // never cleanup-eligible, and leaks -- the documented
    // transaction-table-exhaustion path. trans_mgr consumes it here and
    // performs the state transition in the real table.
    input  logic [MAX_TRANSACTIONS-1:0] i_timeout_detected,

    // Address-range packet filter configuration (see ADDR_FILTER_ENABLE).
    // Inclusive [low, high]. An allocated command whose address falls OUTSIDE
    // the range is marked filtered; the reporters suppress its packets.
    input  logic                        cfg_addr_filter_enable,
    input  logic [AW-1:0]               cfg_addr_filter_low,
    input  logic [AW-1:0]               cfg_addr_filter_high,

    // One bit per table slot: 1 = this entry's packets are suppressed.
    // Consumed by the reporters, which already scan trans_table.
    output logic [MAX_TRANSACTIONS-1:0] filtered_mask,

    // Transaction table output
    output bus_transaction_t            trans_table[MAX_TRANSACTIONS],
    output logic [7:0]                  active_count
);

    localparam int N         = MAX_TRANSACTIONS;
    localparam int PAYLOAD_W = $bits(bus_transaction_t);

    // Age/rank banking (see NUM_BANKS). BANK_SLOTS is the divisor used by the
    // same-bank guards; at NUM_BANKS=1 it equals N so every pair is same-bank
    // and the guards fold away to the original all-pairs logic.
    localparam int BANK_SLOTS = N / NUM_BANKS;

    // Bank of an ID = its low $clog2(NUM_BANKS) bits. Modulo is the low bits
    // for the power-of-2 sizes this supports, and keeps the result in range
    // without a width-dependent part-select.
    function automatic int bank_of(input logic [IW-1:0] id);
        return (NUM_BANKS > 1) ? int'(32'(id) % NUM_BANKS) : 0;
    endfunction

    // NUM_BANKS must divide the table and be a power of 2: the bank index is
    // the low ID bits, and slot->bank is i/BANK_SLOTS. A ragged split would put
    // an ID's entries in a bank the guards do not agree on, which is silent
    // mis-ordering rather than a refused allocation.
    if ((NUM_BANKS < 1) || ((NUM_BANKS & (NUM_BANKS - 1)) != 0)) begin : gen_bad_banks
        $error("axi_monitor_trans_mgr: NUM_BANKS=%0d must be a power of 2.", NUM_BANKS);
    end
    if ((NUM_BANKS > 1) && ((MAX_TRANSACTIONS % NUM_BANKS) != 0)) begin : gen_ragged_banks
        $error("axi_monitor_trans_mgr: MAX_TRANSACTIONS=%0d is not divisible by NUM_BANKS=%0d.",
               MAX_TRANSACTIONS, NUM_BANKS);
    end

    // A BANKED WRITE MONITOR REQUIRES THE AWID FIFO. Without it the WID-less
    // write select falls back to a state predicate over the whole table, which
    // is not ID-matched -- and pick_oldest compares same-bank only, so the
    // select returns one winner per bank and one W beat advances one
    // transaction PER BANK. Measured at N=16/B=4 before the FIFO landed; see
    // the write-data ordering FIFO block below and
    // val/amba/test_axi_monitor_trans_mgr_wr_bank.py. Refusing the build is
    // the honest answer: the combination has no correct behaviour to fall
    // back to.
    if ((NUM_BANKS > 1) && !IS_READ && !USE_WDATA_ORDER_Q) begin : gen_banked_wr_needs_widq
        // ONE string literal: a {"a","b"} concatenation is a bit-vector concat,
        // not a format string, and renders the message as a 1000-digit number.
        $error("axi_monitor_trans_mgr: NUM_BANKS=%0d on a write monitor requires USE_WDATA_ORDER_Q=1 (the WID-less fallback double-counts one W beat across banks).",
               NUM_BANKS);
    end

    // ------------------------------------------------------------------------
    // Parameter width limits (issue #41 "width truncation").
    //
    // bus_transaction_t (rtl/amba/includes/monitor_amba4_pkg.sv) stores the
    // address in a 32-bit field and the ID in an 8-bit field. Neither width
    // is derived from this module's parameters, so wide configurations lose
    // bits. The two cases have very different severity and are handled
    // differently on purpose:
    //
    //   ID_WIDTH > 8  -- FUNCTIONAL BREAKAGE, rejected at elaboration.
    //     The 8-bit payload id and the ID_WIDTH-wide CAM key would hold
    //     different values, so lookups would match the wrong entry and
    //     transactions would be mis-attributed. There is no safe degraded
    //     behaviour, so this is a hard error.
    //
    //   ADDR_WIDTH > 32 -- REPORTED-ADDRESS PRECISION LOSS, permitted.
    //     Tracking still works: the CAM key is the ID, not the address, so
    //     only the address carried in the outgoing packet is truncated.
    //     ADDR_WIDTH=64 is an actively supported and tested configuration
    //     (see val/amba/test_axi4_monitor.py, the 'addr64' configs), so
    //     rejecting it would break working setups for a precision issue.
    //
    // KNOWN LIMITATION, deliberately not fixed here: axi_monitor_base
    // computes ADDR_BITS = min(ADDR_BITS_IN_PKT=38, AW), i.e. the packet
    // format intends to carry 38 address bits, but this table can only
    // supply 32 -- so with AW > 32 the top 6 intended bits are lost. The
    // real fix is widening bus_transaction_t.addr, which lives in
    // monitor_amba4_pkg.sv and ripples into the reporter and timeout
    // blocks; that is outside this module and is left as a follow-up rather
    // than half-done here. The truncation is made explicit at the
    // assignment site below instead of being silent.
    // ------------------------------------------------------------------------
    if (ID_WIDTH > 8) begin : gen_id_width_unsupported
        $error("axi_monitor_trans_mgr: ID_WIDTH=%0d exceeds the 8-bit id field in bus_transaction_t; the table and the CAM key would disagree. Widen bus_transaction_t.id or reduce ID_WIDTH.", ID_WIDTH);
    end

    // ------------------------------------------------------------------------
    // CAM signal nets
    // ------------------------------------------------------------------------
    logic [N-1:0]                 addr_match_oh;
    logic [N-1:0]                 data_match_oh;        // valid only for reads
    logic [N-1:0]                 resp_match_oh;
    logic [N-1:0]                 cam_data_match_first_oh; // unused (kept for clarity)
    logic [N-1:0]                 free_oh;

    logic [N-1:0]                 addr_alloc_oh;
    logic [N-1:0]                 data_alloc_oh;
    logic [N-1:0]                 resp_alloc_oh;

    // ------------------------------------------------------------------------
    // Address-range packet filter (TASK-015). See ADDR_FILTER_ENABLE.
    // ------------------------------------------------------------------------
    // Decided at ALLOCATION, from the command address, and held for the life
    // of the slot -- the address is not available again on the data or resp
    // channels, so it cannot be re-derived later.
    logic w_addr_filtered;
    assign w_addr_filtered = ADDR_FILTER_ENABLE && cfg_addr_filter_enable &&
                             !((cmd_addr >= cfg_addr_filter_low) &&
                               (cmd_addr <= cfg_addr_filter_high));

    logic [N-1:0] r_filtered;
    assign filtered_mask = r_filtered;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_filtered <= '0;
        end else if (clear) begin
            r_filtered <= '0;
        end else begin
            // Written only on allocation. A slot that is not being allocated
            // keeps its verdict; a reused slot is overwritten by the next
            // allocation, so no explicit free-side clear is needed.
            for (int i = 0; i < N; i++) begin
                if (addr_alloc_oh[i]) r_filtered[i] <= w_addr_filtered;
            end
        end
    )

    logic [N-1:0]                 cam_entry_valid;
    bus_transaction_t             cam_entry_payload [N];

    logic [N-1:0]                 cam_entry_we;
    logic [N-1:0]                 cam_entry_valid_next;
    logic [IW-1:0]                cam_entry_id_next      [N];
    bus_transaction_t             cam_entry_payload_next [N];

    logic                         addr_wants_alloc;
    logic                         data_wants_alloc;
    logic                         resp_wants_alloc;

    // Per-phase bank restriction for allocation (see NUM_BANKS). Constant all
    // ones when unbanked, so the CAM's free-slot scan is unrestricted exactly
    // as before.
    logic [N-1:0] w_addr_bank_mask, w_data_bank_mask, w_resp_bank_mask;
    always_comb begin
        for (int i = 0; i < N; i++) begin
            w_addr_bank_mask[i] = (NUM_BANKS == 1) || ((i / BANK_SLOTS) == bank_of(cmd_id));
            w_data_bank_mask[i] = (NUM_BANKS == 1) || ((i / BANK_SLOTS) == bank_of(data_id));
            w_resp_bank_mask[i] = (NUM_BANKS == 1) || ((i / BANK_SLOTS) == bank_of(resp_id));
        end
    end

    // ------------------------------------------------------------------------
    // monitor_trans_cam -- keys + payload storage live here.
    // ------------------------------------------------------------------------
    /* verilator lint_off PINCONNECTEMPTY */
    // ------------------------------------------------------------------------
    // monitor_trans_cam -- GENERATED NUM_BANKS TIMES.
    //
    // The point of the replication is TIMING: one table deep enough for the
    // real concurrency does not close (16 entries WNS +1.018 ns, 40 entries
    // -25.183 ns, 72 hopeless), so the CAM is generated NUM_BANKS times at
    // MAX_TRANSACTIONS/NUM_BANKS each and every instance is the depth that is
    // known to close.
    //
    // Bank b owns slots [b*BANK_SLOTS, (b+1)*BANK_SLOTS) and the IDs whose low
    // bits equal b. A generated CAM can only allocate within itself, so an
    // ID's entries cannot escape its bank -- which is what makes the same-bank
    // age comparisons complete. Per-bank one-hots are stitched back into the
    // flat N-wide vectors below, so everything downstream is unchanged.
    //
    // At NUM_BANKS=1 this is a single CAM of depth N: the original design.
    // ------------------------------------------------------------------------
    logic [BANK_SLOTS-1:0] wb_addr_match      [NUM_BANKS];
    logic [BANK_SLOTS-1:0] wb_data_match      [NUM_BANKS];
    logic [BANK_SLOTS-1:0] wb_resp_match      [NUM_BANKS];
    logic [BANK_SLOTS-1:0] wb_data_first      [NUM_BANKS];
    logic [BANK_SLOTS-1:0] wb_free            [NUM_BANKS];
    logic [BANK_SLOTS-1:0] wb_addr_alloc      [NUM_BANKS];
    logic [BANK_SLOTS-1:0] wb_data_alloc      [NUM_BANKS];
    logic [BANK_SLOTS-1:0] wb_resp_alloc      [NUM_BANKS];
    logic [BANK_SLOTS-1:0] wb_entry_valid     [NUM_BANKS];
    bus_transaction_t      wb_entry_payload   [NUM_BANKS][BANK_SLOTS];

    logic [BANK_SLOTS-1:0] wb_entry_we        [NUM_BANKS];
    logic [BANK_SLOTS-1:0] wb_valid_next      [NUM_BANKS];
    logic [IW-1:0]         wb_id_next         [NUM_BANKS][BANK_SLOTS];
    bus_transaction_t      wb_payload_next    [NUM_BANKS][BANK_SLOTS];

    // Flat -> per-bank (write side).
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            for (int i = 0; i < BANK_SLOTS; i++) begin
                wb_entry_we    [b][i] = cam_entry_we        [b*BANK_SLOTS + i];
                wb_valid_next  [b][i] = cam_entry_valid_next[b*BANK_SLOTS + i];
                wb_id_next     [b][i] = cam_entry_id_next   [b*BANK_SLOTS + i];
                wb_payload_next[b][i] = cam_entry_payload_next[b*BANK_SLOTS + i];
            end
        end
    end

    /* verilator lint_off PINCONNECTEMPTY */
    generate
        for (genvar gb = 0; gb < NUM_BANKS; gb++) begin : g_cam_bank
            monitor_trans_cam #(
                .DEPTH         (BANK_SLOTS),
                .ID_WIDTH      (IW),
                .PAYLOAD_WIDTH (PAYLOAD_W)
            ) u_cam (
                .clk                  (aclk),
                .rst_n                (aresetn),
                .clear                (clear),

                .lookup_addr_id       (cmd_id),
                .lookup_data_id       (data_id),
                .lookup_resp_id       (resp_id),

                .addr_match_oh        (wb_addr_match[gb]),
                .data_match_oh        (wb_data_match[gb]),
                .resp_match_oh        (wb_resp_match[gb]),
                .data_match_first_oh  (wb_data_first[gb]),

                .free_oh              (wb_free[gb]),

                // Only the bank owning the incoming ID may allocate for it.
                .addr_wants_alloc     (addr_wants_alloc && (bank_of(cmd_id)  == gb)),
                .data_wants_alloc     (data_wants_alloc && (bank_of(data_id) == gb)),
                .resp_wants_alloc     (resp_wants_alloc && (bank_of(resp_id) == gb)),

                // Redundant now that each bank is its own CAM, but kept as an
                // explicit guard: a generated CAM cannot allocate outside
                // itself, so these are all ones.
                .addr_alloc_mask      ({BANK_SLOTS{1'b1}}),
                .data_alloc_mask      ({BANK_SLOTS{1'b1}}),
                .resp_alloc_mask      ({BANK_SLOTS{1'b1}}),

                .addr_alloc_oh        (wb_addr_alloc[gb]),
                .data_alloc_oh        (wb_data_alloc[gb]),
                .resp_alloc_oh        (wb_resp_alloc[gb]),

                .entry_we             (wb_entry_we[gb]),
                .entry_valid_next     (wb_valid_next[gb]),
                .entry_id_next        (wb_id_next[gb]),
                .entry_payload_next   (wb_payload_next[gb]),

                .entry_valid          (wb_entry_valid[gb]),
                // entry_id port is informational only; the trans_mgr trusts the
                // payload's `id` field as the source of truth (the CAM and the
                // payload are written atomically so they always agree).
                .entry_id             (),
                .entry_payload        (wb_entry_payload[gb])
            );
        end
    endgenerate
    /* verilator lint_on PINCONNECTEMPTY */

    // Per-bank -> flat (read side). Single driver per flat vector.
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            for (int i = 0; i < BANK_SLOTS; i++) begin
                addr_match_oh          [b*BANK_SLOTS + i] = wb_addr_match   [b][i];
                data_match_oh          [b*BANK_SLOTS + i] = wb_data_match   [b][i];
                resp_match_oh          [b*BANK_SLOTS + i] = wb_resp_match   [b][i];
                cam_data_match_first_oh[b*BANK_SLOTS + i] = wb_data_first   [b][i];
                free_oh                [b*BANK_SLOTS + i] = wb_free         [b][i];
                addr_alloc_oh          [b*BANK_SLOTS + i] = wb_addr_alloc   [b][i];
                data_alloc_oh          [b*BANK_SLOTS + i] = wb_data_alloc   [b][i];
                resp_alloc_oh          [b*BANK_SLOTS + i] = wb_resp_alloc   [b][i];
                cam_entry_valid        [b*BANK_SLOTS + i] = wb_entry_valid  [b][i];
                cam_entry_payload      [b*BANK_SLOTS + i] = wb_entry_payload[b][i];
            end
        end
    end

    // ========================================================================
    // Per-slot AGE (issue order)  -- issue #41 defect 1.
    //
    // AXI4 permits several outstanding transactions with the SAME ID, and
    // requires their data/response phases to return in ISSUE order. The CAM
    // slot index carries no ordering information (allocation always takes the
    // lowest free index, so a recycled low slot can be YOUNGER than a live
    // high slot), so an explicit age is needed to attribute an incoming beat
    // to the correct one of several same-ID entries.
    //
    // Representation: r_age[i] is the RANK of slot i -- the number of live
    // entries older than it -- so the oldest live entry always has rank 0.
    // Ranks stay dense over [0, live_count), which keeps the field at
    // $clog2(N) bits and makes "oldest" a compare against a small constant
    // instead of a wide timestamp subtraction (and so has no wrap hazard).
    // When an entry is freed, every surviving entry ranked above it
    // decrements, keeping the sequence dense.
    // ========================================================================
    localparam int AGEW = (N > 1) ? $clog2(N) : 1;

    logic [AGEW-1:0] r_age [N];

    // Packed mirror of r_age for use as a FUNCTION ARGUMENT below.
    //
    // pick_oldest used to read module-scope r_age[] directly from inside its
    // body. That is legal SV, but sv2v then has to name the whole unpacked
    // array in the explicit sensitivity list it synthesizes for every
    // always_comb that calls the function -- and yosys rejects a memory
    // referenced without an index ("Insufficient number of array indices for
    // r_age"), which broke the formal flat build. Passing the ages in as a
    // packed argument keeps the function self-contained and the flat file
    // legal Verilog. Same hardware either way.
    logic [N*AGEW-1:0] w_age_flat;
    always_comb begin
        for (int i = 0; i < N; i++) begin
            w_age_flat[i*AGEW +: AGEW] = r_age[i];
        end
    end

    // Pick the OLDEST (lowest-rank) slot from a candidate set.
    // Returns '0 when the candidate set is empty.
    //
    // PARALLEL min-rank select: slot i wins iff it is a candidate and no other
    // candidate has a strictly lower age (index breaks the -- normally
    // impossible, ranks are dense-unique among live entries -- tie, keeping
    // the old scan order's lowest-index behavior bit-exact).
    //
    // The previous implementation scanned r x i with a `found` flag, which
    // SERIALIZED N^2 iterations into one priority chain: at the board sizing
    // (N=36) that synthesized to a 242-level, ~125 ns cone through r_age ->
    // CAM CE -- unroutable at any target clock. Sim and formal (BMC at small
    // N) were structurally blind to it; the first Genesys 2 synthesis caught
    // it. Each res[i] below is an independent OR-reduce of pairwise
    // comparators: O(N^2) area, O(log N) depth. Functionally identical.
    function automatic logic [N-1:0] pick_oldest(input logic [N-1:0] cand,
                                                 input logic [N*AGEW-1:0] ages);
        logic [N-1:0] res;
        logic         lose;
        for (int i = 0; i < N; i++) begin
            lose = 1'b0;
            for (int j = 0; j < N; j++) begin
                // SAME-BANK ONLY. Constant-folded at elaboration, so at
                // NUM_BANKS=1 this is the original all-pairs compare and at
                // B>1 the cross-bank comparators are simply never built.
                // Exact either way: candidates come from an ID-matched vector
                // and every entry with a given ID lives in one bank.
                if ((i / BANK_SLOTS) == (j / BANK_SLOTS) &&
                    j != i && cand[j] &&
                    ((ages[j*AGEW +: AGEW] <  ages[i*AGEW +: AGEW]) ||
                     ((ages[j*AGEW +: AGEW] == ages[i*AGEW +: AGEW]) && (j < i)))) begin
                    lose = 1'b1;
                end
            end
            res[i] = cand[i] && !lose;
        end
        return res;
    endfunction

    // ------------------------------------------------------------------------
    // WID-less write data-channel match.
    //
    // For AXI4 reads the data channel has a WID that matches the AR
    // channel's id, so cam_data_match_oh is what we want. For AXI4
    // writes the data channel has no WID; the upstream convention is
    // "first valid entry in ADDR_PHASE or DATA_PHASE that has
    // cmd_received && !data_completed wins". The CAM can't see state
    // (it stores payload as opaque bits) so this predicate is computed
    // locally over the CAM's payload outputs.
    // ------------------------------------------------------------------------
    (* keep = "true" *) logic [N-1:0] w_data_state_pred_oh;
    logic [N-1:0]                     w_data_state_first_oh;

    always_comb begin
        for (int i = 0; i < N; i++) begin
            w_data_state_pred_oh[i] = cam_entry_valid[i] &&
                                       ((cam_entry_payload[i].state == TRANS_ADDR_PHASE) ||
                                        (cam_entry_payload[i].state == TRANS_DATA_PHASE)) &&
                                       cam_entry_payload[i].cmd_received &&
                                       !cam_entry_payload[i].data_completed;
        end
    end

    // Declared here rather than beside its always_comb: the write-data
    // ordering FIFO below reads it, and the repo's pre-commit check
    // requires declaration before use.
    logic [N-1:0] w_freeing_oh;

    // ========================================================================
    // Write-data ordering FIFO of AWIDs (USE_WDATA_ORDER_Q, writes only).
    //
    // AXI4 W beats carry no WID, so the entry a beat belongs to cannot come
    // from the beat itself. This FIFO records the AWID at AW time and hands
    // it back at W time: PUSH on the AW handshake, POP on W-LAST, head == the
    // AWID of the burst currently on W.
    //
    // WHY AN ID AND NOT A SLOT INDEX. The previous version queued the
    // allocated SLOT, which orders correctly but leaves the write-data
    // candidate set outside the ID-matched world the rest of this module
    // lives in. `pick_oldest` compares SAME-BANK ONLY, and its correctness
    // argument is "candidates come from an ID-matched vector, and every entry
    // with a given ID lives in one bank". A state-predicate candidate set
    // spans every bank, so at NUM_BANKS=B the select returned one winner PER
    // BANK and a single W beat advanced up to B transactions -- the issue #41
    // double-count, reintroduced across banks. Measured at N=16/B=4: one W
    // beat advanced slots 0 and 4 together
    // (val/amba/test_axi_monitor_trans_mgr_wr_bank.py). Keying the candidates
    // on the head AWID restores the premise by construction: every candidate
    // shares one ID, therefore one bank, and the same-bank compare is exact.
    //
    // BUS REQUIREMENT -- W MUST NOT LEAD AW. A W beat is attributed by AW
    // order, so the AW naming it must already have been seen. Same-cycle AW+W
    // is supported (the empty-queue bypass takes the head straight off cmd_id
    // and w_data_cmd_bypass_oh binds the entry the command path is touching
    // this cycle), but W strictly BEFORE its AW is not: those beats have no
    // AWID to attribute them to and are treated as strays. This is the
    // restriction commercial VIPs commonly impose, and it is a REPO-WIDE
    // requirement for any bus these monitors are attached to. Recorded in
    // vault/handbook/design/valid-ready-contracts.md.
    //
    // AN ENTRY THAT DIES WITHOUT W-LAST must still retire its queue slot or
    // the head parks forever and stalls every later burst (the same leak
    // class as the stray-beat poison above). The head is dead when no live
    // entry carries its ID still awaiting data -- the ID-keyed equivalent of
    // the old w_freeing_oh[head_slot] test.
    // ========================================================================
    localparam int SLOTW = (N > 1) ? $clog2(N) : 1;
    localparam int WQW   = (N > 1) ? $clog2(N + 1) : 1;

    logic [IW-1:0]  r_widq [N];
    logic [WQW-1:0] r_widq_count;
    logic [IW-1:0]  w_widq_head;
    logic [N-1:0]   w_widq_cand_oh;
    logic w_widq_push, w_widq_pop, w_widq_head_dead, w_widq_bypass;

    // Push on the AW handshake. The ID comes off the command lines, so no
    // allocation one-hot is needed and a data-first orphan adopted by its AW
    // pushes exactly like a fresh allocation.
    assign w_widq_push   = !IS_READ && USE_WDATA_ORDER_Q && cmd_valid && cmd_ready;

    // Empty queue + a push this cycle == same-cycle AW+W: the head is the ID
    // arriving now, one cycle before it is registered.
    assign w_widq_bypass = (r_widq_count == '0) && w_widq_push;
    assign w_widq_head   = w_widq_bypass ? cmd_id : r_widq[0];

    // Entries owned by the head AWID that are still expecting W data.
    //
    // The queue must be NON-EMPTY (or pushing this cycle) for the head to mean
    // anything: r_widq[0] holds the last popped ID once the queue drains, and
    // matching against that stale value would attribute a stray W beat -- one
    // with no AW behind it at all -- to whatever unrelated transaction happens
    // to still be open on that ID. With no AW owed, there is no candidate, and
    // the beat falls through to the stray/orphan path as it should.
    always_comb begin
        w_widq_cand_oh = '0;
        if (!IS_READ && USE_WDATA_ORDER_Q &&
            ((r_widq_count != '0) || w_widq_bypass)) begin
            for (int i = 0; i < N; i++) begin
                w_widq_cand_oh[i] = w_data_state_pred_oh[i] &&
                                    (cam_entry_payload[i].id == w_widq_head) &&
                                    !w_freeing_oh[i];
            end
        end
    end

    assign w_widq_head_dead = (r_widq_count != '0) && !(|w_widq_cand_oh);
    assign w_widq_pop       = (r_widq_count != '0) &&
                              ((data_valid && data_ready && data_last) ||
                               w_widq_head_dead);

    // Oldest-first among the head ID's entries: AXI4 orders same-ID bursts by
    // issue order, and slot index does not track issue order once slots start
    // being recycled (issue #41 defect 1).
    assign w_data_state_first_oh = USE_WDATA_ORDER_Q
                                 ? pick_oldest(w_widq_cand_oh,       w_age_flat)
                                 : pick_oldest(w_data_state_pred_oh, w_age_flat);

    // Shift-out queue: N is small (table depth) and one entry moves per cycle,
    // so a shift register costs less than pointer wrap logic and keeps head at
    // index 0 for a flat mux.
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_widq_count <= '0;
            for (int i = 0; i < N; i++) r_widq[i] <= '0;
        end else if (clear) begin
            r_widq_count <= '0;
            for (int i = 0; i < N; i++) r_widq[i] <= '0;
        end else if (!IS_READ && USE_WDATA_ORDER_Q) begin
            automatic logic [WQW-1:0] v_cnt = r_widq_count;

            if (w_widq_pop && (v_cnt != '0)) begin
                for (int i = 0; i < N - 1; i++) r_widq[i] <= r_widq[i + 1];
                v_cnt = v_cnt - 1'b1;
            end
            if (w_widq_push && (v_cnt < WQW'(N))) begin
                // v_cnt is a 0..N count and the push is guarded to v_cnt < N
                // above, so the low SLOTW bits are the tail index.
                r_widq[v_cnt[SLOTW-1:0]] <= cmd_id;
                v_cnt = v_cnt + 1'b1;
            end
            r_widq_count <= v_cnt;
        end
    end

    // ------------------------------------------------------------------------
    // Cleanup eligibility (same policy as the production module).
    // Hoisted above the match/alloc logic because w_freeing_oh feeds it.
    // ------------------------------------------------------------------------
    logic [N-1:0] w_can_cleanup;
    always_comb begin
        for (int i = 0; i < N; i++) begin
            if (cam_entry_valid[i]) begin
                unique case (cam_entry_payload[i].state)
                    TRANS_COMPLETE,
                    TRANS_ERROR,
                    TRANS_ORPHANED: w_can_cleanup[i] = cam_entry_payload[i].event_reported;
                    default:        w_can_cleanup[i] = 1'b0;
                endcase
            end else begin
                w_can_cleanup[i] = 1'b0;
            end
        end
    end

    // Slots that are live now but go away at this clock edge.
    always_comb begin
        for (int i = 0; i < N; i++) begin
            w_freeing_oh[i] = cam_entry_valid[i] && w_can_cleanup[i];
        end
    end

    // ------------------------------------------------------------------------
    // Hit indicators + wants_alloc.
    //
    // ISSUE #41 DEFECT 1/2 FIX -- address phase.
    //
    // The old code suppressed allocation on ANY same-ID match
    // (`addr_wants_alloc = cmd_valid && !(|addr_match_oh)`) and merged the
    // new command into the matching entry. That is wrong: multiple
    // outstanding transactions with the same ID are legal AXI4, so a second
    // AR/AW must get its OWN slot.
    //
    // The update path still has one legitimate job. Allocation triggers on
    // cmd_valid (not on the handshake), so a command held across several
    // cycles waiting for cmd_ready must not allocate a fresh slot every
    // cycle. That in-flight entry is precisely the same-ID entry that has
    // not yet recorded its command handshake, so suppression is now scoped
    // to `!cmd_received` instead of "any id match".
    //
    // Entries being freed this cycle are excluded as well: on a cleanup
    // cycle the slot is neither free (free_oh comes from registered r_valid)
    // nor surviving, and the old code let it swallow the incoming command,
    // which then lost its completion and fabricated an EVT_DATA_ORPHAN
    // error on entirely legal traffic (defect 2).
    // ------------------------------------------------------------------------
    logic [N-1:0] w_addr_pend_oh;   // same-ID entry still awaiting its handshake
    always_comb begin
        for (int i = 0; i < N; i++) begin
            w_addr_pend_oh[i] = addr_match_oh[i] &&
                                !cam_entry_payload[i].cmd_received &&
                                !w_freeing_oh[i];
        end
    end

    // ------------------------------------------------------------------------
    // SAME-CYCLE AW+W BYPASS (write monitors only).
    //
    // The WID-less predicate above runs over REGISTERED entries and requires
    // cmd_received, so a W beat arriving in the SAME cycle as its AW matched
    // nothing -- and with IS_AXI=1 the write-data orphan path is compiled
    // dead, so the beat was silently LOST. The entry then waited for data
    // forever and the B response fabricated an EVT_PROTOCOL ("response
    // before data") error on entirely legal traffic (single-beat writes from
    // skid-buffered masters routinely present AW and W together).
    //
    // When no registered entry matches, the beat may target the entry the
    // COMMAND path is touching THIS cycle:
    //   * addr_alloc_oh  -- the slot being allocated for this AW, or
    //   * addr_update_oh -- the pending same-ID entry (allocated on an
    //     earlier stalled cycle, cmd_received still 0), qualified by
    //     cmd_valid because addr_update_oh is a pure combinational match on
    //     whatever value the cmd_id lines happen to hold, and by
    //     state==TRANS_ADDR_PHASE: addr_update_oh also selects ORPHANED
    //     entries being ADOPTED (a stray B allocates a resp-orphan, then a
    //     same-ID AW attaches to it). Binding a W beat to an orphan before
    //     the AW handshake promoted it out of ORPHANED, which destroyed its
    //     error-drain guarantee (EVT_RESP_ORPHAN only reports from a
    //     terminal state) and parked it outside every timeout cone -- the
    //     btormc counterexample for ap_wr_data_phase_has_cmd. Orphan
    //     adoption keeps its legacy behavior: pre-handshake beats are
    //     strays and are dropped.
    // The two terms are mutually exclusive by construction (alloc fires
    // only when no pending entry exists). This keeps monitor state
    // cycle-accurate -- cmd + first beat in one cycle records both, with no
    // side buffer.
    // ------------------------------------------------------------------------
    // The bypass reads a LOCAL MIRROR of the CAM's addr-alloc pick instead of
    // the CAM's addr_alloc_oh output. The CAM computes all three alloc
    // one-hots in a single always_comb, so Verilator fuses them into one
    // node; routing addr_alloc_oh into data_hit_any -> data_wants_alloc ->
    // (back into that node) then looks like a combinational loop and fails
    // the AXIL write build with UNOPTFLAT (warnings-as-errors), even though
    // the true dependency is acyclic (addr's pick never depends on the data
    // port). The mirror is exact by construction: the CAM allocates addr
    // first from the free vector, i.e. lowest free index when
    // addr_wants_alloc -- and is cross-checked against the CAM output by
    // ap_bypass_alloc_mirror below.
    // BANKED: the mirror must scan the SAME slots the CAM does. Bank gb's
    // generated CAM only sees its own slots, so it allocates the lowest free
    // slot WITHIN the ID's bank -- an unmasked "lowest free index" mirror
    // points at a slot in some other bank, and the same-cycle bypass then
    // binds the W beat to an entry that was never allocated. The beat is lost,
    // the write never completes, and the B fabricates an EVT_PROTOCOL
    // "response before data" on legal traffic (measured at N=16/B=4 by
    // test_axi_monitor_wr_same_cycle with USE_WDATA_ORDER_Q=1).
    //
    // Same defect class as the WID-less write select above: a stated
    // invariant -- here "the CAM allocates the lowest free index" -- that was
    // true of one flat table and silently stopped being true once the table
    // was banked. Masking with w_addr_bank_mask restores it; at NUM_BANKS=1
    // the mask is all ones and this is the original scan.
    logic [N-1:0] w_addr_alloc_mirror_oh;
    always_comb begin
        w_addr_alloc_mirror_oh = '0;
        if (addr_wants_alloc) begin
            for (int i = 0; i < N; i++) begin
                if ((w_addr_alloc_mirror_oh == '0) && free_oh[i] &&
                    w_addr_bank_mask[i]) begin
                    w_addr_alloc_mirror_oh[i] = 1'b1;
                end
            end
        end
    end

    logic [N-1:0] addr_update_oh;
    logic [N-1:0] data_update_oh;
    logic [N-1:0] resp_update_oh;

    logic [N-1:0] w_data_cmd_bypass_oh;
    always_comb begin
        w_data_cmd_bypass_oh = '0;
        if (!IS_READ && data_valid && data_ready && !(|w_data_state_pred_oh)) begin
            for (int i = 0; i < N; i++) begin
                w_data_cmd_bypass_oh[i] =
                    w_addr_alloc_mirror_oh[i] ||
                    (cmd_valid && addr_update_oh[i] &&
                     (cam_entry_payload[i].state == TRANS_ADDR_PHASE));
            end
        end
    end

    logic addr_hit_any, data_hit_any, resp_hit_any;

    assign addr_hit_any = |w_addr_pend_oh;
    assign resp_hit_any = |resp_match_oh;
    // The bypass counts as a hit so the beat cannot ALSO allocate an orphan
    // in the same cycle (live path for IS_AXI=0 write monitors).
    assign data_hit_any = IS_READ ? (|data_match_oh)
                                  : ((|w_data_state_pred_oh) ||
                                     (|w_data_cmd_bypass_oh));

    // ------------------------------------------------------------------------
    // COMMAND-ENTRY CAP (saturation-recovery fix).
    //
    // Command-originated entries may occupy at most N - CMD_ENTRY_RESERVE
    // slots. This guarantees RECOVERY of block_ready: axi_monitor_base
    // re-asserts block_ready when active_count < MAX - (CMD_ENTRY_RESERVE-1),
    // which is STRICTLY ABOVE this cap. So even a table whose command
    // entries are all permanently in flight (data never arrives, timeouts
    // disabled) sits below the reopen threshold once the ungated data/resp
    // (orphan) entries drain, and the command channel un-stalls. Without the
    // strict inequality, saturation parks occupancy exactly AT the blocking
    // threshold and block_ready can NEVER re-assert -- the stream_core
    // multi-channel permanent wedge (val/amba/test_axi_monitor_trans_mgr.py
    // phase_saturation_recovers).
    //
    // The cap counts COMMAND entries, deliberately NOT free slots. An
    // earlier version of this fix gated command allocation on
    // (free_count > RESERVE); under zero-delay oversubscription that
    // inverted the allocation priority -- every freed slot was immediately
    // taken by an ungated orphan allocation, free_count never climbed above
    // the reserve, and command tracking starved permanently (completion
    // rate collapsed from ~30% to ~13% in val/amba/test_axi4_monitor.py's
    // id_space/combined stress). Counting command entries instead lets a
    // command reclaim a freed slot the moment one of its own retires
    // (the CAM's alloc priority order addr > data > resp breaks the tie in
    // the command's favor), while orphans may still use every slot commands
    // are not entitled to.
    //
    // A command seen while the cap is reached is simply not tracked
    // (lossy-but-honest degrade); if it is still held valid when one of the
    // command entries retires, it allocates then.
    //
    // A "command entry" is one that was allocated by (or has absorbed) an
    // address-phase beat: cmd_received covers tracked handshakes and
    // orphans that later received their command; state==TRANS_ADDR_PHASE
    // covers commands seen valid but not yet accepted (cmd_received=0).
    // Orphan entries (ORPHANED / promoted DATA_PHASE, cmd_received=0) are
    // excluded -- they always drain via error reporting, so they cannot
    // pin occupancy above the reopen threshold.
    //
    // Tables smaller than 16 get NO cap and keep fully legacy allocation:
    // small tables cannot spare slots (>= 4 outstanding same-ID
    // transactions must be trackable even at MAX_TRANSACTIONS=4, and even
    // one reserved slot at MAX=8 measurably starves the id_space/addr64
    // oversubscription stress in val/amba/test_axi4_monitor.py). They trade
    // the saturation-recovery guarantee for full tracking capacity.
    //
    // The reserve value and the recovery contract live in
    // monitor_common_pkg::cmd_entry_reserve -- axi_monitor_base derives its
    // BLOCK_MARGIN from the same function, so the two cannot drift.
    // ------------------------------------------------------------------------
    localparam int CMD_ENTRY_RESERVE = cmd_entry_reserve(N);

    logic [$clog2(N+1)-1:0] w_cmd_entry_count;
    always_comb begin
        w_cmd_entry_count = '0;
        for (int i = 0; i < N; i++) begin
            if (cam_entry_valid[i] &&
                    (cam_entry_payload[i].cmd_received ||
                     (cam_entry_payload[i].state == TRANS_ADDR_PHASE))) begin
                w_cmd_entry_count += ($clog2(N+1))'(1);
            end
        end
    end

    logic w_cmd_headroom;
    assign w_cmd_headroom = (CMD_ENTRY_RESERVE == 0) ||
                            (w_cmd_entry_count <
                             ($clog2(N+1))'(N - CMD_ENTRY_RESERVE));

    assign addr_wants_alloc = cmd_valid && !addr_hit_any && w_cmd_headroom;
    always_comb begin
        if (IS_READ) begin
            data_wants_alloc = data_valid && data_ready && !data_hit_any;
        end else begin
            data_wants_alloc = data_valid && data_ready && !IS_AXI && !data_hit_any;
        end
        resp_wants_alloc = (!IS_READ) && resp_valid && resp_ready && !resp_hit_any;
    end

    // ------------------------------------------------------------------------
    // Effective update one-hot.
    //
    // ISSUE #41 DEFECT 1 FIX -- data/response phases.
    //
    // `data_update_oh = data_match_oh` updated EVERY entry sharing the id,
    // so with two outstanding same-ID reads a single R beat was counted
    // against both. AXI4 orders same-ID responses by issue order, so a beat
    // belongs to the OLDEST matching entry that is still expecting data.
    //
    // Two tiers: prefer an entry that has not completed its data/response
    // phase; if every match has already completed, fall back to the oldest
    // match so a stray extra beat is absorbed exactly as before rather than
    // being turned into a new orphan error.
    // ------------------------------------------------------------------------
    // (declarations hoisted above the same-cycle write bypass, which reads
    // addr_update_oh; assignments remain below.)

    logic [N-1:0] w_data_cand_open, w_data_cand_any;
    logic [N-1:0] w_resp_cand_open, w_resp_cand_any;

    always_comb begin
        for (int i = 0; i < N; i++) begin
            w_data_cand_any[i]  = data_match_oh[i] && !w_freeing_oh[i];
            w_data_cand_open[i] = w_data_cand_any[i] &&
                                  !cam_entry_payload[i].data_completed;
            w_resp_cand_any[i]  = resp_match_oh[i] && !w_freeing_oh[i];
            w_resp_cand_open[i] = w_resp_cand_any[i] &&
                                  !cam_entry_payload[i].resp_received;
        end
    end

    // At most one entry can be pending its command handshake, but resolve
    // through the same oldest-first path for uniformity.
    assign addr_update_oh = pick_oldest(w_addr_pend_oh, w_age_flat);

    // STRAY NON-LAST BEAT ABSORPTION (saturation-recovery fix, part 2).
    //
    // When a beat matches ONLY entries that have already closed their data
    // phase (the cand_any fallback), it is a stray from a transaction the
    // table no longer represents (e.g. a command that went untracked while
    // the reserve was exhausted, reusing a still-resident ID).
    //
    // A stray LAST beat keeps the legacy fallback: the update path re-runs
    // the completion logic and leaves the entry in a TERMINAL state
    // (TRANS_COMPLETE / TRANS_ERROR), which is harmless and, under heavy
    // ID-space oversubscription, reconstructs untracked bursts into
    // reportable completions (measured: dropping this halved the completion
    // rate in val/amba/test_axi4_monitor.py combined/id_space stress).
    //
    // A stray NON-LAST beat is the poison and is absorbed with no update at
    // all: the update path unconditionally promoted the entry's state to
    // TRANS_DATA_PHASE (unless TRANS_ERROR), so it dragged a
    // TRANS_COMPLETE/TRANS_ORPHANED entry back to TRANS_DATA_PHASE with
    // data_completed already set -- a state no data_last will ever close
    // (same-ID beats keep resolving to younger open entries) and that the
    // timeout block's !data_completed term can never age out. The entry
    // leaked permanently: one poisoned slot per stray, ratcheting the table
    // to saturation (the stream_core multi-channel wedge mechanism).
    //
    // Absorption = an empty update one-hot. The stray still counts as a hit
    // (data_hit_any uses the raw match vector), so it does not allocate an
    // orphan either -- the original intent, minus the state clobber.
    // Write side ORs in the same-cycle AW+W bypass; it is nonzero only when
    // w_data_state_first_oh is empty (the bypass requires no registered
    // match), so the two never select different slots in the same cycle.
    assign data_update_oh = IS_READ
        ? ((|w_data_cand_open) ? pick_oldest(w_data_cand_open, w_age_flat)
                               : (data_last ? pick_oldest(w_data_cand_any, w_age_flat) : '0))
        : (w_data_state_first_oh | w_data_cmd_bypass_oh);

    // Response fallback is unchanged: a stray B response updates fields of an
    // already-closed entry but every reachable outcome (COMPLETE / ERROR) is
    // terminal and cleanup-eligible, so it cannot leak a slot.
    assign resp_update_oh = (|w_resp_cand_open) ? pick_oldest(w_resp_cand_open, w_age_flat)
                                                : pick_oldest(w_resp_cand_any, w_age_flat);

    // Channel index from ID (used only by addr allocation -- kept for
    // source-compatibility with the production module).
    logic [5:0] w_addr_chan_idx;
    always_comb begin
        /* verilator lint_off WIDTHTRUNC */
        w_addr_chan_idx = IS_AXI ? (({24'h0, cmd_id} % 64)) : 0;
        /* verilator lint_on WIDTHTRUNC */
    end

    logic cmd_handshake;
    assign cmd_handshake = cmd_valid && cmd_ready;

    // ------------------------------------------------------------------------
    // Stale event_reported mask (issue #41 defect 3).
    //
    // Set when a slot is freed, cleared once the reporter's flag for that
    // slot finally drops. While set, the flag is understood to refer to the
    // slot's PREVIOUS occupant and is not applied to whatever is in the slot
    // now. The flag is guaranteed to drop: it is a function of a delayed
    // snapshot of an entry that has already been invalidated.
    // ------------------------------------------------------------------------
    logic [N-1:0] r_rpt_stale_mask;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rpt_stale_mask <= '0;
        end else if (clear) begin
            r_rpt_stale_mask <= '0;
        end else begin
            for (int i = 0; i < N; i++) begin
                if (w_freeing_oh[i]) begin
                    r_rpt_stale_mask[i] <= 1'b1;
                end else if (!i_event_reported_flags[i]) begin
                    r_rpt_stale_mask[i] <= 1'b0;
                end
            end
        end
    )

    // ------------------------------------------------------------------------
    // Age (rank) maintenance -- see the AGEW comment at the top.
    //
    // A newly allocated entry is the youngest, so it takes rank
    // = number of entries surviving this cycle, offset by its position in
    // the CAM's fixed (addr, data, resp) allocation order when more than one
    // phase allocates at once. A surviving entry decrements its rank by the
    // number of freed entries that were older than it, which keeps ranks
    // dense over [0, live_count).
    // ------------------------------------------------------------------------
    logic w_addr_alloc_fire, w_data_alloc_fire, w_resp_alloc_fire;

    assign w_addr_alloc_fire = |addr_alloc_oh;
    assign w_data_alloc_fire = |data_alloc_oh;
    assign w_resp_alloc_fire = |resp_alloc_oh;

    // Rank assigned to a slot allocated by each phase this cycle.
    logic [AGEW-1:0] w_age_addr_new, w_age_data_new, w_age_resp_new;

    // Ranks are dense within a BANK, so a new entry's rank is its own bank's
    // survivor count -- and a same-cycle allocation only bumps it when that
    // allocation lands in the same bank. At NUM_BANKS=1 every bank_of() is 0
    // and every same-bank test is true, so this reduces to the original
    // global count exactly.
    always_comb begin
        int surv_bank [NUM_BANKS];
        int ab, db, rb;

        for (int b = 0; b < NUM_BANKS; b++) surv_bank[b] = 0;
        for (int i = 0; i < N; i++) begin
            if (cam_entry_valid[i] && !w_freeing_oh[i]) begin
                surv_bank[i / BANK_SLOTS]++;
            end
        end

        ab = bank_of(cmd_id);
        db = bank_of(data_id);
        rb = bank_of(resp_id);

        w_age_addr_new = AGEW'(surv_bank[ab]);
        w_age_data_new = AGEW'(surv_bank[db]
                             + ((w_addr_alloc_fire && (ab == db)) ? 1 : 0));
        w_age_resp_new = AGEW'(surv_bank[rb]
                             + ((w_addr_alloc_fire && (ab == rb)) ? 1 : 0)
                             + ((w_data_alloc_fire && (db == rb)) ? 1 : 0));
    end

    // Combinational next-rank per slot. Kept separate from the registers
    // below for two reasons: Verilator rejects a delayed (NBA) assignment
    // to an unpacked array from inside a for loop (BLKLOOPINIT), and the
    // per-slot generate matches this module's stated synthesis intent of
    // N independent small update cones rather than one fused cone.
    logic [AGEW-1:0] w_age_next [N];

    always_comb begin
        for (int i = 0; i < N; i++) begin
            int dec;
            // Assign unconditionally: a variable written only inside a
            // branch infers a latch under Verilator -Wall.
            dec           = 0;
            w_age_next[i] = r_age[i];
            if (addr_alloc_oh[i]) begin
                w_age_next[i] = w_age_addr_new;
            end else if (data_alloc_oh[i]) begin
                w_age_next[i] = w_age_data_new;
            end else if (resp_alloc_oh[i]) begin
                w_age_next[i] = w_age_resp_new;
            end else if (cam_entry_valid[i] && !w_freeing_oh[i]) begin
                // Close the gaps left by entries freed ahead of us.
                // Same-bank only, for the reason given on NUM_BANKS: ranks are
                // dense within a bank and never compared across one.
                for (int j = 0; j < N; j++) begin
                    if ((i / BANK_SLOTS) == (j / BANK_SLOTS) &&
                        w_freeing_oh[j] && (r_age[j] < r_age[i])) begin
                        dec++;
                    end
                end
                w_age_next[i] = r_age[i] - AGEW'(dec);
            end
        end
    end

    generate
        for (genvar ga = 0; ga < N; ga++) begin : g_age
            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    r_age[ga] <= '0;
                end else if (clear) begin
                    r_age[ga] <= '0;
                end else begin
                    r_age[ga] <= w_age_next[ga];
                end
            )
        end
    endgenerate

    // ------------------------------------------------------------------------
    // Per-slot next-state computation.
    //
    // One always_comb per slot, mirroring the production module's
    // per-entry generate-loop always_ff. The body is a direct copy of
    // the production update logic with the non-blocking assignments
    // turned into blocking writes to a `next` temporary, so the
    // CAM's entry_payload_next port can take the whole struct at once.
    //
    // Mutex notes (preserved from production):
    //   * addr_alloc_oh[i] and addr_update_oh[i] can't both fire on the
    //     same slot (alloc is gated to free slots, update to valid).
    //   * Same for data_alloc/data_update and resp_alloc/resp_update.
    //   * Cleanup is applied last (overrides same-cycle valid set).
    //   * event_reported feedback is last. Ordering alone is NOT enough
    //     here: it stops a cleaned-up entry from having its flag re-set,
    //     but the reporter's flag outlives the entry it describes by
    //     ~2 cycles, so a slot REALLOCATED in that window would come up
    //     pre-marked. r_rpt_stale_mask covers that case -- see the
    //     feedback block below (issue #41 defect 3).
    // ------------------------------------------------------------------------
    generate
        for (genvar gi = 0; gi < N; gi++) begin : g_entry_next
            bus_transaction_t next;
            logic             next_we;
            logic [IW-1:0]    next_id;

            always_comb begin
                // Default: hold current state.
                next     = cam_entry_payload[gi];
                next_we  = 1'b0;
                next_id  = cam_entry_payload[gi].id[IW-1:0];

                // --- ADDR PHASE ---
                //
                // Field-by-field write to mirror the production module
                // exactly: fields that production touches via NBA are
                // assigned here; fields that production leaves alone
                // (data_timestamp, resp_timestamp on addr_alloc) MUST
                // be preserved across the alloc, so we do NOT pre-zero
                // `next`. Same rule applies to data_alloc and resp_alloc
                // below -- the equivalence test (this file's reason for
                // existing) catches any clobbered field.
                if (addr_alloc_oh[gi]) begin
                    next.valid                 = 1'b1;
                    next.state                 = TRANS_ADDR_PHASE;
                    next.id                    = '0;
                    next.id[IW-1:0]            = cmd_id;
                    // DELIBERATE TRUNCATION (issue #41): bus_transaction_t.addr
                    // is 32 bits. With ADDR_WIDTH > 32 the upper bits are
                    // dropped here and never reach the packet -- see the
                    // "KNOWN LIMITATION" note in the parameter block above.
                    next.addr                  = 32'(cmd_addr);
                    next.len                   = cmd_len;
                    next.size                  = cmd_size;
                    next.burst                 = cmd_burst;
                    next.cmd_received          = cmd_ready;
                    next.addr_timer            = '0;
                    next.data_started          = 1'b0;
                    next.data_completed        = 1'b0;
                    next.resp_received         = 1'b0;
                    next.event_code.raw_code   = 8'h0;
                    next.event_reported        = 1'b0;
                    next.data_timer            = '0;
                    next.resp_timer            = '0;
                    next.addr_timestamp        = timestamp;
                    next.expected_beats        = IS_AXI ? (cmd_len + 8'h1) : 8'h1;
                    next.data_beat_count       = '0;
                    next.channel               = w_addr_chan_idx;
                    next.eos_seen              = 1'b0;
                    next_we                    = 1'b1;
                    next_id                    = cmd_id;
                end
                if (addr_update_oh[gi] && cmd_handshake) begin
                    next.cmd_received   = 1'b1;
                    next.addr_timer     = '0;
                    next.addr_timestamp = timestamp;
                    next_we             = 1'b1;
                end

                // --- DATA PHASE ---
                if (data_valid && data_ready) begin
                    if (data_update_oh[gi]) begin
                        // Capture beats-after-increment for the
                        // "is this the last expected beat" test.
                        //
                        // SAME-CYCLE AW+W BYPASS NOTE: this branch reads
                        // beat count / expected_beats from `next`, NOT from
                        // the registered payload. With no addr action this
                        // cycle the two are identical (the addr blocks above
                        // never touch these fields on an update), but when
                        // addr_alloc fires on this slot in the SAME cycle,
                        // `next` holds the freshly initialised entry
                        // (beat_count 0, expected_beats from cmd_len) while
                        // the registered payload still holds the PREVIOUS
                        // occupant's fields -- counting against those
                        // corrupted the brand-new transaction.
                        next.data_started    = 1'b1;
                        next.data_beat_count = next.data_beat_count + 1'b1;
                        next.data_timer      = '0;
                        if (next.state != TRANS_ERROR) begin
                            // Hold ADDR_PHASE for a bypass beat whose AW has
                            // not handshaked yet (write-only case:
                            // cmd_received=0 in ADDR_PHASE). Promoting it
                            // would move the stalled AW out of the
                            // address-phase timeout's coverage
                            // (w_addr_pending requires ADDR_PHASE) and into
                            // a data-phase term that requires cmd_received
                            // -- i.e. no timeout coverage at all. Reads are
                            // untouched: their update path never selects a
                            // cmd_received=0 ADDR_PHASE entry.
                            if (IS_READ || next.cmd_received ||
                                (next.state != TRANS_ADDR_PHASE)) begin
                                next.state = TRANS_DATA_PHASE;
                            end
                        end

                        if (IS_READ) begin
                            if (data_last) begin
                                next.data_completed = 1'b1;
                                next.data_timestamp = timestamp;
                            end
                            if (data_resp[1]) begin
                                next.state = TRANS_ERROR;
                                next.event_code.axi_error =
                                    (data_resp[0]) ? EVT_RESP_DECERR : EVT_RESP_SLVERR;
                            end else if (data_last) begin
                                next.state = TRANS_COMPLETE;
                            end
                        end else begin
                            // WRITE: complete on data_last OR
                            // post-increment beat count == expected.
                            if (data_last ||
                                (next.data_beat_count ==
                                 next.expected_beats)) begin
                                next.data_completed = 1'b1;
                                next.data_timestamp = timestamp;
                            end
                        end
                        next_we = 1'b1;
                    end else if (data_alloc_oh[gi]) begin
                        // Production touches: valid, state, id, channel,
                        // expected_beats, data_started, data_completed,
                        // data_beat_count, data_timestamp,
                        // event_code.axi_error. Other fields
                        // (addr/len/size/burst, timers) are preserved.
                        //
                        // ISSUE #41 DEFECT 3: cmd_received and
                        // event_reported are explicitly CLEARED rather than
                        // preserved. A free slot still holds the previous
                        // occupant's payload, so inheriting those two bits
                        // gave a brand-new orphan a stale "already reported"
                        // (instantly cleanup-eligible, packet lost) and a
                        // stale "command received" (which would let it
                        // capture write-data beats it never asked for).
                        next.valid                 = 1'b1;
                        next.cmd_received          = 1'b0;
                        next.event_reported        = 1'b0;
                        next.state                 = TRANS_ORPHANED;
                        next.id                    = '0;
                        if (IS_AXI) begin
                            next.id[IW-1:0]        = data_id;
                            /* verilator lint_off WIDTHTRUNC */
                            next.channel           = ({24'h0, data_id} % 64);
                            /* verilator lint_on WIDTHTRUNC */
                            next.expected_beats    = IS_READ ? 8'h0 : 8'h1;
                        end else begin
                            next.expected_beats    = 8'h1;
                            next.channel           = 6'h0;
                        end
                        next.data_started          = 1'b1;
                        next.data_completed        = data_last;
                        next.data_beat_count       = 8'h1;
                        next.data_timestamp        = timestamp;
                        next.event_code.axi_error  = EVT_DATA_ORPHAN;
                        next_we                    = 1'b1;
                        next_id                    = IS_AXI ? data_id : '0;
                    end
                end

                // --- RESP PHASE (write only) ---
                //
                // For AXI4 writes the same slot can take BOTH a data
                // beat and the B response in the same cycle. Production
                // uses NBA, so the resp-update condition tests below
                // see the OLD (pre-cycle) value of data_completed and
                // state. With blocking writes we must explicitly read
                // from cam_entry_payload (the registered/old value),
                // not from `next` (which may already reflect the data
                // phase's update). The equivalence test catches this.
                if (!IS_READ && resp_valid && resp_ready) begin
                    if (resp_update_oh[gi]) begin
                        next.resp_received  = 1'b1;
                        next.resp_timestamp = timestamp;
                        next.resp_timer     = '0;
                        if (resp_code[1]) begin
                            next.state = TRANS_ERROR;
                            next.event_code.axi_error =
                                (resp_code[0]) ? EVT_RESP_DECERR : EVT_RESP_SLVERR;
                        end else if (cam_entry_payload[gi].data_completed) begin
                            if (cam_entry_payload[gi].state != TRANS_ERROR) begin
                                next.state = TRANS_COMPLETE;
                            end
                        end else begin
                            // Resp before data completion = protocol
                            // violation.
                            next.state = TRANS_ERROR;
                            next.event_code.axi_error = EVT_PROTOCOL;
                        end
                        next_we = 1'b1;
                    end else if (resp_alloc_oh[gi]) begin
                        // Production touches: valid, state, id, channel,
                        // resp_received, resp_timestamp,
                        // event_code.axi_error. Other fields are preserved.
                        // cmd_received / event_reported are cleared for the
                        // same reason as the data-orphan path above
                        // (issue #41 defect 3).
                        next.valid                 = 1'b1;
                        next.cmd_received          = 1'b0;
                        next.event_reported        = 1'b0;
                        next.state                 = TRANS_ORPHANED;
                        next.id                    = '0;
                        if (IS_AXI) begin
                            next.id[IW-1:0]        = resp_id;
                            /* verilator lint_off WIDTHTRUNC */
                            next.channel           = (resp_id % 64);
                            /* verilator lint_on WIDTHTRUNC */
                        end else begin
                            next.channel           = 6'h0;
                        end
                        next.resp_received         = 1'b1;
                        next.resp_timestamp        = timestamp;
                        next.event_code.axi_error  = EVT_RESP_ORPHAN;
                        next_we                    = 1'b1;
                        next_id                    = IS_AXI ? resp_id : '0;
                    end
                end

                // --- TIMEOUT -> TERMINAL STATE ---
                //
                // ISSUE #41 (cross-agent: axi_monitor_timeout owns detection,
                // trans_mgr owns the table). A timed-out transaction must be
                // moved to a terminal state so w_can_cleanup can eventually
                // free the slot; otherwise it sits in ADDR/DATA phase for
                // ever and the table leaks an entry per timeout.
                //
                // Which timeout code applies is derived from fields this
                // module already holds, so no extra sideband is needed. The
                // registered (pre-cycle) payload is read, matching the
                // convention used by the resp-phase block above.
                //
                // Entries already in a terminal state are left alone so a
                // real error/completion code is not overwritten by a
                // late-arriving timeout.
                if (i_timeout_detected[gi] && cam_entry_valid[gi] &&
                        (cam_entry_payload[gi].state != TRANS_COMPLETE) &&
                        (cam_entry_payload[gi].state != TRANS_ERROR) &&
                        (cam_entry_payload[gi].state != TRANS_ORPHANED)) begin
                    next.state = TRANS_ERROR;
                    if (!cam_entry_payload[gi].cmd_received) begin
                        // Command accepted into the table but never handshook.
                        next.event_code.axi_timeout = EVT_CMD_TIMEOUT;
                    end else if (cam_entry_payload[gi].data_completed &&
                                 !cam_entry_payload[gi].resp_received) begin
                        // Data done, waiting on B.
                        next.event_code.axi_timeout = EVT_RESP_TIMEOUT;
                    end else begin
                        // Waiting on data (either none yet, or mid-burst).
                        next.event_code.axi_timeout = EVT_DATA_TIMEOUT;
                    end
                    next_we = 1'b1;
                end

                // --- CLEANUP (last; overrides same-cycle valid set) ---
                if (cam_entry_valid[gi] && w_can_cleanup[gi]) begin
                    next.valid = 1'b0;
                    next_we    = 1'b1;
                end

                // --- EVENT-REPORTED FEEDBACK (last) ---
                //
                // ISSUE #41 DEFECT 3 FIX.
                //
                // The reporter derives its flag from a one-cycle-delayed
                // snapshot of the table, so the flag stays asserted for
                // ~2 cycles AFTER the slot it refers to has been freed. The
                // old guard only tested the registered payload, which
                // protects the OLD entry but says nothing about a NEW one:
                // a slot reallocated inside that window came up already
                // marked reported, so it became cleanup-eligible the moment
                // it completed and the reporter's emission window collapsed
                // from "hold until reported" to a single cycle.
                //
                // Three conditions now gate the feedback:
                //   * the slot must be live (an alloc lands on an invalid
                //     slot, so this covers the allocation cycle itself),
                //   * it must not be going away at this edge, and
                //   * r_rpt_stale_mask must not still be flagging the flag
                //     as belonging to the previous occupant.
                if (i_event_reported_flags[gi] &&
                        !r_rpt_stale_mask[gi] &&
                        cam_entry_valid[gi] &&
                        !w_can_cleanup[gi] &&
                        !cam_entry_payload[gi].event_reported) begin
                    next.event_reported = 1'b1;
                    next_we             = 1'b1;
                end
            end

            // Drive the CAM's per-slot write port.
            assign cam_entry_we[gi]             = next_we;
            assign cam_entry_valid_next[gi]     = next.valid;
            assign cam_entry_id_next[gi]        = next_id;
            assign cam_entry_payload_next[gi]   = next;
        end
    endgenerate

    // ------------------------------------------------------------------------
    // Outputs from the CAM's payload storage.
    // ------------------------------------------------------------------------
    assign trans_table = cam_entry_payload;

    // ========================================================================
    // Active-transaction counter (exact CAM occupancy) and state-change detection
    //
    // active_count is the number of LIVE CAM entries, derived directly as the
    // pop-count of cam_entry_valid and registered once -- NOT as a free-running
    // alloc-minus-cleanup accumulator.  The former accumulator (see git history)
    // could desync from true occupancy and UNDERFLOW to 0xFF under legal AXI,
    // sticking busy high and block_ready low for the rest of the session -- found
    // by the SymbiYosys proof (see
    // rtl/amba/KNOWN_ISSUES/axi_monitor_active_count_underflow.md).  A registered
    // pop-count is structurally bounded to [0, N] and can never underflow.
    //
    // Timing: cam_entry_valid is already a register, so the pop-count is a clean
    // adder tree sitting between two flops (one pipeline stage) -- it is NOT on
    // the match->alloc critical path the old comment worried about.  active_count
    // lags occupancy by a single cycle, which block_ready's BLOCK_MARGIN absorbs.
    // ========================================================================
    logic [7:0]             r_active_count;
    logic [$clog2(N+1)-1:0] w_occupancy;

    always_comb begin
        w_occupancy = '0;
        for (int i = 0; i < N; i++)
            w_occupancy += {{($clog2(N+1)-1){1'b0}}, cam_entry_valid[i]};
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_active_count <= '0;
        end else if (clear) begin
            r_active_count <= '0;   // synchronous CAM clear zeroes occupancy too
        end else begin
            r_active_count <= {{(8-$clog2(N+1)){1'b0}}, w_occupancy};
        end
    )

    assign active_count = r_active_count;


`ifdef FORMAL
    // ========================================================================
    // In-RTL formal properties (flattened into the formal build by sv2v, which
    // defines FORMAL -- see tools/gen_formal_deps.py). Living here rather than
    // in the harness gives them full visibility of internal state and means
    // every proof that includes this module checks them.
    //
    // Motivation: the multi-channel saturation wedge shipped under PASSING
    // formal because the old block_ready property restated the assign rather
    // than encoding an invariant. These properties encode the two contracts
    // the fix introduced, so they cannot silently regress.
    // ========================================================================
    logic f_past_ok;
    initial f_past_ok = 1'b0;
    always_ff @(posedge aclk) f_past_ok <= aresetn;

    // F1: no entry is ever in DATA_PHASE with data_completed set.
    //
    // This is the unclosable configuration behind the production saturation
    // wedge: a stray non-last data beat re-opened a terminal entry to
    // DATA_PHASE while data_completed stayed 1 -- no future data_last can
    // close it, no timeout term matched it, and in perf-only builds nothing
    // could retire it, so each occurrence leaked a table slot until
    // active_count pinned at MAX and block_ready wedged low permanently.
    //
    // Stated as a STATE INVARIANT rather than a transition property on
    // purpose. Two earlier transition drafts ("terminal states never move to
    // DATA_PHASE") were refuted by btormc with LEGAL traces: orphan adoption
    // (late command attaching to a data-first entry) and orphan continuation
    // (an ORPHANED entry receiving its next non-last beat) both legitimately
    // enter DATA_PHASE -- with an open burst. Every legal path into
    // DATA_PHASE has data_completed=0; only the poison sets it with the
    // burst already closed. The invariant needs no exemptions and catches
    // the wedge state however it might be reached.
    // READ-ONLY by construction: writes have no RESP_PHASE state, so a write
    // entry legitimately waits for B in DATA_PHASE with data_completed=1
    // (btormc produced exactly that trace when this was unscoped -- the
    // axi4_*_wr_mon proofs failed on legal write flows). The write data path
    // is structurally immune to the reopen poison anyway: its WID-less
    // predicate requires !data_completed, so a closed entry can never be
    // selected by a stray W beat.
    always_ff @(posedge aclk) begin
        if (IS_READ && aresetn && f_past_ok) begin
            for (int fi = 0; fi < N; fi++) begin
                if (cam_entry_valid[fi]) begin
                    ap_no_reopened_complete:
                        assert (!(cam_entry_payload[fi].state == 3'(TRANS_DATA_PHASE) &&
                                  cam_entry_payload[fi].data_completed));
                end
            end
        end
    end

    // F3: a WRITE entry in DATA_PHASE always has its command handshake
    // recorded. The same-cycle AW+W bypass lets a W beat bind to an entry
    // whose AW is still stalled (cmd_received=0); such an entry must be HELD
    // in ADDR_PHASE, because the address-phase timeout term requires
    // state==ADDR_PHASE and the data-phase term requires cmd_received -- a
    // cmd_received=0 entry promoted to DATA_PHASE would sit in neither
    // cone's coverage and leak its slot if the AW never completed (the
    // timeout-coverage-hole class of bug). Reads are exempt: orphan
    // continuation legitimately holds DATA_PHASE with cmd_received=0.
    always_ff @(posedge aclk) begin
        if (!IS_READ && aresetn && f_past_ok) begin
            for (int fi = 0; fi < N; fi++) begin
                if (cam_entry_valid[fi]) begin
                    ap_wr_data_phase_has_cmd:
                        assert (!(cam_entry_payload[fi].state == 3'(TRANS_DATA_PHASE) &&
                                  !cam_entry_payload[fi].cmd_received));
                end
            end
        end
    end

    // F4: the local addr-alloc mirror used by the same-cycle AW+W bypass
    // always agrees with the CAM's own pick (it exists only to break a
    // false UNOPTFLAT loop through the CAM's fused alloc always_comb; if
    // the CAM's allocation policy ever changes, this is the tripwire).
    always_ff @(posedge aclk) begin
        if (aresetn && f_past_ok) begin
            ap_bypass_alloc_mirror:
                assert (w_addr_alloc_mirror_oh == addr_alloc_oh);
        end
    end

    // F2: the command-entry cap holds. Command-originated entries never
    // exceed N - CMD_ENTRY_RESERVE, which is what guarantees occupancy can
    // always drain below the block_ready reopen threshold
    // (N - CMD_ENTRY_RESERVE + 1). Vacuous when CMD_ENTRY_RESERVE == 0
    // (small tables run uncapped by design); real for any N >= 16 proof.
    always_ff @(posedge aclk) begin
        if (aresetn && f_past_ok && CMD_ENTRY_RESERVE > 0) begin
            ap_cmd_entry_cap:
                assert (w_cmd_entry_count <= ($clog2(N+1))'(N - CMD_ENTRY_RESERVE));
        end
    end
`endif

endmodule : axi_monitor_trans_mgr

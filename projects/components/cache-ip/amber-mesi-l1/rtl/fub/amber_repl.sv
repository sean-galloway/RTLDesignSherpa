// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_repl
// Purpose:
//   Replacement-policy engine for the amber MESI L1. Selects the victim
//   way on a miss and maintains per-set policy state across hits and
//   installs. Policies: true LRU (default), FIFO, RANDOM (LFSR),
//   tree-PLRU (timing fallback). Exactly one policy elaborates per build.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/04_amber_repl.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-06

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: amber_repl
//==============================================================================
// Description:
//   Policy state is per-set control state (not SRAM), so it carries a
//   reset and initializes to a deterministic permutation / zero state.
//   The victim way is combinational on the current policy state; updates
//   are synchronous on repl_hit or repl_update (mutually exclusive in the
//   blocking pipeline -- a cycle is a hit service or a miss install, never
//   both).
//
//   LRU (default): rank array, 0 = most recent, WAYS-1 = victim. On an
//   access the touched way becomes MRU and ways more recent than it shift
//   down one rank.
//
//   FIFO: per-set ring of way indices; victim = ring head. On an install
//   the ring slot at the head is overwritten with the installed way and
//   the head advances -- exact when the installed way equals the victim
//   way, which amber_control guarantees (fills install into the victim
//   way; MAS ch02_blocks/04 invariant). Hits do not reorder a FIFO.
//
//   RANDOM: one 32-bit Fibonacci LFSR (taps 32,22,2,1) per set. The
//   victim is the LFSR truncated to WAY_INDEX_WIDTH bits, sampled and
//   then advanced on every repl_req. Requires WAYS to be a power of two
//   so the truncation is a full decoder (elaboration check).
//
//   TREE_PLRU: WAYS-1 bits per set in a binary tree (heap-indexed nodes).
//   On an access the bits along the path to the accessed way point away
//   from it; the victim is the leaf found by following the bits. Requires
//   power-of-two WAYS. No cache_sim golden exists for tree-PLRU (PRD D7
//   caveat); the TB carries an independent model.
//
//   REPL_POLICY is the typed amber_repl_t enum from amber_pkg (house
//   precedent: fifo_sync MEM_STYLE), not a string -- string parameters do
//   not elaborate reliably across tools, and the enum is the single
//   source shared with the kmap workbook and DV.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SETS:
//     Description: Number of sets (power of two)
//     Type: int
//     Range: 16 to 512
//     Default: amber_pkg.AMBER_SETS (128)
//
//   WAYS:
//     Description: Associativity (power of two required for random and
//                  tree_plru)
//     Type: int
//     Range: 2 to 8
//     Default: amber_pkg.AMBER_WAYS (4)
//
//   REPL_POLICY:
//     Description: Replacement policy selector; values are the
//                  amber_repl_t encodings from amber_pkg (declared int so
//                  -G elaboration overrides stay width-clean)
//     Type: int
//     Range: 0 = lru | 1 = tree_plru | 2 = fifo | 3 = random
//     Default: 0 (AMBER_REPL_LRU)
//
//   REPL_SEED:
//     Description: LFSR seed for the random policy (per set, all sets
//                  start at the same seed)
//     Type: int
//     Default: 32'h0000_ACE1
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - repl_hit and repl_update are mutually exclusive; driving both is a
//     contract violation and the update order is undefined.
//   - repl_hit_way is the hitting way on a hit and the installed way on
//     an install (the victim way just produced).
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - Instantiated by: amber_core (amber_control drives the ports)
//   - Package: amber_pkg (amber_repl_t, geometry defaults)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/fub/test_amber_repl.py
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/fub/test_amber_repl.py -v
//
//==============================================================================

module amber_repl
    import amber_pkg::*;
#(
    parameter int SETS       = AMBER_SETS,
    parameter int WAYS       = AMBER_WAYS,
    // Typed amber_repl_t in spirit (values are the pkg enum encodings) but
    // declared int so -G elaboration overrides stay width-clean; the
    // generate branches compare against int'(AMBER_REPL_*) casts.
    parameter int REPL_POLICY = int'(AMBER_REPL_LRU),
    parameter int REPL_SEED  = 32'h0000ACE1,
    localparam int SET_INDEX_WIDTH = $clog2(SETS),
    localparam int WAY_INDEX_WIDTH = $clog2(WAYS),
    localparam int RANK_WIDTH      = (WAYS <= 2) ? 1 : $clog2(WAYS)
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // Victim request (combinational victim way on the current state)
    input  logic                        repl_req,
    input  logic [SET_INDEX_WIDTH-1:0]  repl_set,
    output logic [WAY_INDEX_WIDTH-1:0]  repl_victim_way,

    // Policy update: exactly one of hit / update per cycle
    input  logic                        repl_hit,
    input  logic                        repl_update,
    input  logic [WAY_INDEX_WIDTH-1:0]  repl_hit_way
);

    // A cycle is a hit service or a miss install, never both (MAS).
    wire w_access = repl_hit | repl_update;

    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("amber_repl: SETS must be a power of two");
        if (WAYS < 2)
            $error("amber_repl: WAYS must be >= 2");
    end

    // =========================================================================
    // LRU (default): per-set rank array.
    // =========================================================================
    if (REPL_POLICY == int'(AMBER_REPL_LRU)) begin : gen_lru

        logic [RANK_WIDTH-1:0] rank [SETS * WAYS];

        wire [RANK_WIDTH-1:0] old_rank =
            rank[32'(repl_set) * WAYS + 32'(repl_hit_way)];

        always_comb begin
            repl_victim_way = '0;
            for (int w = 0; w < WAYS; w++) begin
                if (rank[32'(repl_set) * WAYS + w] == RANK_WIDTH'(WAYS - 1))
                    repl_victim_way = WAY_INDEX_WIDTH'(w);
            end
        end

        `ALWAYS_FF_RST(clk, rst_n,
            if (`RST_ASSERTED(rst_n)) begin
                for (int s = 0; s < SETS; s++) begin
                    for (int w = 0; w < WAYS; w++) begin
                        rank[s * WAYS + w] <= RANK_WIDTH'(w);
                    end
                end
            end else if (w_access) begin
                for (int w = 0; w < WAYS; w++) begin
                    if (WAY_INDEX_WIDTH'(w) == repl_hit_way)
                        rank[32'(repl_set) * WAYS + w] <= '0;
                    else if (rank[32'(repl_set) * WAYS + w] < old_rank)
                        rank[32'(repl_set) * WAYS + w] <=
                            rank[32'(repl_set) * WAYS + w] + 1'b1;
                end
            end
        )

    // =========================================================================
    // FIFO: per-set ring; install overwrites the victim slot and advances.
    // =========================================================================
    end else if (REPL_POLICY == int'(AMBER_REPL_FIFO)) begin : gen_fifo

        logic [WAY_INDEX_WIDTH-1:0] ring [SETS * WAYS];
        logic [WAY_INDEX_WIDTH-1:0] head [SETS];

        always_comb begin
            repl_victim_way = ring[32'(repl_set) * WAYS + 32'(head[repl_set])];
        end

        `ALWAYS_FF_RST(clk, rst_n,
            if (`RST_ASSERTED(rst_n)) begin
                for (int s = 0; s < SETS; s++) begin
                    for (int w = 0; w < WAYS; w++) begin
                        ring[s * WAYS + w] <= WAY_INDEX_WIDTH'(w);
                    end
                    head[s] <= '0;
                end
            end else if (repl_update) begin
                // Installed way == victim way: the slot at the head becomes
                // the tail after the head advances, so a single write and a
                // head bump is the whole update.
                ring[32'(repl_set) * WAYS + 32'(head[repl_set])] <= repl_hit_way;
                head[repl_set] <= (head[repl_set] == WAY_INDEX_WIDTH'(WAYS - 1))
                                  ? '0 : head[repl_set] + 1'b1;
            end
        )

    // =========================================================================
    // RANDOM: per-set 32-bit Fibonacci LFSR, victim = truncated value.
    // =========================================================================
    end else if (REPL_POLICY == int'(AMBER_REPL_RANDOM)) begin : gen_random

        logic [31:0] lfsr [SETS];

        initial begin
            if ((WAYS & (WAYS - 1)) != 0)
                $error("amber_repl: random policy requires power-of-two WAYS");
        end

        wire fb = ^{lfsr[repl_set][31], lfsr[repl_set][21],
                     lfsr[repl_set][1],  lfsr[repl_set][0]};

        always_comb begin
            repl_victim_way = lfsr[repl_set][WAY_INDEX_WIDTH-1:0];
        end

        `ALWAYS_FF_RST(clk, rst_n,
            if (`RST_ASSERTED(rst_n)) begin
                for (int s = 0; s < SETS; s++) begin
                    lfsr[s] <= REPL_SEED;
                end
            end else if (repl_req) begin
                lfsr[repl_set] <= {lfsr[repl_set][30:0], fb};
            end
        )

    // =========================================================================
    // TREE_PLRU: per-set binary tree, bits point away from recent.
    // =========================================================================
    end else if (REPL_POLICY == int'(AMBER_REPL_TREE_PLRU)) begin : gen_tree_plru

        localparam int LEVELS = (WAYS <= 2) ? 1 : $clog2(WAYS);

        logic [WAYS-1:0] tree [SETS];

        initial begin
            if ((WAYS & (WAYS - 1)) != 0)
                $error("amber_repl: tree_plru requires power-of-two WAYS");
        end

        always_comb begin
            int node;
            repl_victim_way = '0;
            node = 0;
            for (int lvl = 0; lvl < LEVELS; lvl++) begin
                repl_victim_way = (repl_victim_way << 1)
                                  | WAY_INDEX_WIDTH'(tree[repl_set][node]);
                node = 2 * node + 1 + tree[repl_set][node];
            end
        end

        `ALWAYS_FF_RST(clk, rst_n,
            if (`RST_ASSERTED(rst_n)) begin
                for (int s = 0; s < SETS; s++) begin
                    tree[s] <= '0;
                end
            end else if (w_access) begin
                logic [WAYS-1:0] ntree;
                int node;
                ntree = tree[repl_set];
                node = 0;
                for (int lvl = 0; lvl < LEVELS; lvl++) begin
                    ntree[node] = ~repl_hit_way[LEVELS-1-lvl];
                    node = 2 * node + 1 + repl_hit_way[LEVELS-1-lvl];
                end
                tree[repl_set] <= ntree;
            end
        )

    // =========================================================================
    // Unknown policy
    // =========================================================================
    end else begin : gen_unknown
        initial begin
            $error("amber_repl: unsupported REPL_POLICY");
        end
        always_comb repl_victim_way = '0;
    end

endmodule : amber_repl

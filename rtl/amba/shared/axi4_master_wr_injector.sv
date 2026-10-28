// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_master_wr_injector
// Purpose: Master-side write driver for memory-controller characterization.
//          Walks an algorithmic address mix (via dma_address_gen) and emits
//          LFSR-pattern data (via shifter_lfsr_fibonacci) through axi4_master_wr.
//          Accumulates a CRC-32 over the data written so the read-side
//          (axi4_master_rd_crc_check) has an expected value to compare against.
//
// Documentation: projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2-characterization/README.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-06-25

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: axi4_master_wr_injector
//==============================================================================
// Description:
//   Drives a CSR-programmed sequence of AXI4 write bursts at the FUB side of
//   `axi4_master_wr`, with addresses from `dma_address_gen` and data from a
//   Fibonacci LFSR seeded by the CSR. Pairs with `axi4_master_rd_crc_check`
//   for end-to-end data integrity validation.
//
//   Workflow:
//     1. Software programs the cfg_* ports (start addr, addr-gen knobs,
//        burst len, txn count, AXI id/size/burst attributes).
//     2. Software pulses `cfg_start`.
//     3. The block walks index_0 = 0..cfg_txn_count-1 through dma_address_gen,
//        issuing one AW per index. For each AW it streams `cfg_burst_len`
//        beats of LFSR data on W. The LFSR advances on every W beat
//        (regardless of burst boundary), so the data stream is a
//        deterministic function of (cfg_lfsr_seed, total_beats_so_far).
//     4. dataint_crc accumulates over the same LFSR stream; o_expected_crc
//        carries the running value, latched valid on cfg_done.
//     5. When all cfg_txn_count B responses have been received,
//        `cfg_done` asserts and stays high until the next cfg_start pulse.
//
//   Fully decoupled AW and W: two independent dma_address_gen instances
//   walk the same descriptor in parallel. AW runs as fast as awready +
//   addr-gen pipeline allow; W runs at slave's wready rate. awvalid
//   stays asserted from its first cycle to the last AW handshake when
//   cfg_wr_gap = 0 — the addr-gen produces 1 result/cycle once warmed
//   up. cfg_wr_gap > 0 pauses both AW and W together, and an AW never runs
//   ahead of the previous burst's W (no AW waits at the slave for W data
//   held by the gap). AXI4 outstanding
//   is bounded by MAX_OUTSTANDING (AWs issued minus Bs received) and by
//   the slave's awready throttling.
//
//   Address dimensions (TASK-049): the transaction index is shaped before it
//   reaches dma_address_gen. cfg_idx1_shift = 0 walks index_0 only (index_1
//   held at 0, the one-dimensional legacy walk); cfg_idx1_shift = k feeds the
//   index's low k bits to index_0 and the rest to index_1, so a two-row
//   alternation inside one bank is stride_0 = row, wrap_0 = 0, k = 1,
//   stride_1 = burst, wrap_1 = page. cfg_addr_lfsr = 1 replaces the counter
//   with a maximal INDEX_WIDTH-bit LFSR (pseudo-random inside the wrap
//   region); the AW and W paths step their own copies on their own request
//   accepts from the same seed, so they stay in lockstep, and a matched
//   reader with the same seed reads what was written. With repeated
//   addresses only the address-hash data mode validates. Hammer mode wins
//   over both.
//
//   One-bit split (pumice TASK-060): cfg_idx1_bit = 1 makes index_1 the
//   SINGLE bit k = cfg_idx1_shift of the transaction index and index_0 the
//   index with that bit removed. stride_1 then toggles every 2^k
//   transactions while stride_0 keeps walking: stride_0 = one DRAM burst,
//   stride_1 = half a burst, k = 3 issues the low halves of eight bursts,
//   then their high halves, then the next eight bursts. k = 0 is lo, hi,
//   lo, hi along the line. The same walk under the plain split would need a
//   third dimension.
//
//   Gap sweep (pumice TASK-060): cfg_gap_sweep = 1 makes the idle gap after
//   burst n equal to cfg_wr_gap + (n mod 8), saturating at the port width,
//   so the inter-burst delay walks 0..7 above the base and repeats. The
//   AW-behind-W pacing of a non-zero gap applies throughout a sweep.
//
// Parameters:
//   AXI_*          - standard AXI4 widths
//   LFSR_WIDTH     - LFSR width; defaults to 32. Matches the slave-side
//                    block so master/slave CRC values are interchangeable.
//   LFSR_TAPS      - maximal-length Fibonacci taps; default {23,3,2,1} (library table entry, verified primitive).
//   CRC_WIDTH      - CRC width; 32 by default
//   CRC_DATA_WIDTH - bytes per CRC update; we update 32 bits per LFSR step
//                    so this is fixed at 32 to match the slave side.
//   TXN_COUNT_WIDTH- width of cfg_txn_count; default 16 (up to 64K bursts)
//   INDEX_WIDTH    - dma_address_gen index width; default 16
//   STRIDE_WIDTH   - dma_address_gen signed stride width; default 24
//   (both dma_address_gen instances are built with INPUT_REG = 1: the shaped
//   index is registered before the multiplier, 3 cycles request to address)
//==============================================================================
module axi4_master_wr_injector #(
    // ---- AXI ----
    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W  = 4,
    parameter int SKID_DEPTH_B  = 2,
    parameter int AXI_ID_WIDTH    = 8,
    parameter int AXI_ADDR_WIDTH  = 32,
    parameter int AXI_DATA_WIDTH  = 64,
    parameter int AXI_USER_WIDTH  = 1,
    parameter int AXI_WSTRB_WIDTH = AXI_DATA_WIDTH / 8,

    // ---- LFSR ----
    parameter int                    LFSR_WIDTH = 32,
    parameter logic [31:0]           LFSR_SEED  = 32'hDEADBEEF,
    parameter logic [47:0]           LFSR_TAPS  = {12'd23, 12'd3, 12'd2, 12'd1},
    // Address-index LFSR (TASK-049): taps for a maximal INDEX_WIDTH-bit
    // Fibonacci LFSR. The default is x^16+x^15+x^13+x^4+1 for INDEX_WIDTH=16;
    // another INDEX_WIDTH needs its own maximal taps here.
    parameter logic [47:0]           ADDR_LFSR_TAPS = {12'd16, 12'd15, 12'd13, 12'd4},

    // ---- CRC (mirror slave-side defaults so the two are interchangeable) ----
    parameter int                    CRC_WIDTH      = 32,
    parameter int                    CRC_DATA_WIDTH = 32,
    parameter logic [CRC_WIDTH-1:0]  CRC_POLY       = 32'h04C11DB7,
    // Reflection MUST match the slave-side blocks (CRC_REFIN/REFOUT default 1
    // there) or writer-vs-slave CRC compares can never match. The old
    // hardcoded REFIN(0)/REFOUT(0) here broke the documented interchange --
    // unnoticed while the accumulate strobe was also tied off (both sides
    // emitted constant zero).
    parameter int                    CRC_REFIN      = 1,
    parameter int                    CRC_REFOUT     = 1,
    parameter logic [CRC_WIDTH-1:0]  CRC_POLY_INIT  = '1,
    parameter logic [CRC_WIDTH-1:0]  CRC_XOROUT     = '1,

    // ---- Workload ----
    parameter int TXN_COUNT_WIDTH = 16,
    parameter int INDEX_WIDTH     = 16,
    parameter int STRIDE_WIDTH    = 24,
    // Width of cfg_wr_gap. 4 (0..15 idle cycles) is the original port and
    // every existing instance's; a wider gap lets a characterization harness
    // throttle the writer far below what 15 cycles between bursts can.
    parameter int GAP_WIDTH       = 4,

    // Legal-AxLEN quantum: the number of AXI beats that make one DRAM burst, i.e.
    // cfg_burst_len MUST be a nonzero integer multiple of this (one AXI burst maps
    // to an integer number of DRAM bursts). Project-specific — depends on the DRAM
    // BL, the AXI:DRAM-beat gear, and the device width — so it is a PARAMETER. 1 =
    // unconstrained (default; no check). A non-conforming cfg_burst_len yields a
    // ragged final sub-command in pumice_wr_splitter -> SLVERR / partial write.
    parameter int BURST_LEN_MULTIPLE = 1,
    // Cap on bursts in flight (AWs issued minus B responses received). AW is
    // otherwise decoupled and issues as fast as the slave accepts.
    parameter int MAX_OUTSTANDING = 8,
    // Width of cfg_max_outstanding: enough to hold MAX_OUTSTANDING itself, so
    // the runtime dial can reach the ceiling and one value above it is still
    // representable (and clamps).
    parameter int OSW = $clog2(MAX_OUTSTANDING + 1),

    // ---- Aliases ----
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH,
    parameter int SW = AXI_WSTRB_WIDTH
) (
    input  logic                       aclk,
    input  logic                       aresetn,

    // ==========================================================================
    // Configuration — programmed by the harness CSR. Static during a run;
    // a new cfg_start pulse re-samples them.
    // ==========================================================================
    // Address generator descriptor (passed through to dma_address_gen)
    input  logic [AW-1:0]                       cfg_start_addr,
    input  logic signed [STRIDE_WIDTH-1:0]      cfg_addr_stride_0,
    input  logic signed [STRIDE_WIDTH-1:0]      cfg_addr_stride_1,
    input  logic [AW-1:0]                       cfg_addr_wrap_mask_0,
    input  logic [AW-1:0]                       cfg_addr_wrap_mask_1,

    // Burst shape
    input  logic [7:0]                          cfg_burst_len,    // beats (1..256). awlen = cfg_burst_len - 1
    input  logic [TXN_COUNT_WIDTH-1:0]          cfg_txn_count,    // total bursts to issue
    input  logic [IW-1:0]                       cfg_axi_id,       // FIXED-mode id / start seed for COUNTER+LFSR modes
    // AW ID generation mode:
    //   0 = FIXED:   every AW uses cfg_axi_id verbatim
    //   1 = COUNTER: 8-bit counter starting at cfg_axi_id[7:0], +1 per AW
    //   2 = LFSR:    8-bit Fibonacci LFSR seeded from cfg_axi_id[7:0]|1
    // Counter / LFSR widths are 8-bit internally and zero-extended (or
    // truncated) to IW at the awid output.
    input  logic [1:0]                          cfg_id_mode,
    input  logic [2:0]                          cfg_axi_size,     // awsize
    input  logic [1:0]                          cfg_axi_burst,    // awburst (INCR=1)

    // LFSR seed override — if 0, defaults to the LFSR_SEED parameter.
    // Lets the CSR re-seed without recompile.
    input  logic [LFSR_WIDTH-1:0]               cfg_lfsr_seed,

    // Rowhammer / aggressor-pair mode: when 1, the index fed to
    // dma_address_gen is the LSB of the transaction counter, so AW/W
    // addresses alternate base, base+stride_0 per transaction. stride_0
    // is reused as the aggressor-pair offset; no new stride port is
    // added. Both AW and W addr-gens see the same hammer index so the
    // two channels stay in lockstep.
    input  logic                                cfg_hammer_en,

    // Address index shaping (TASK-049; see the header). idx1_shift splits the
    // transaction index between dma_address_gen's two dimensions (0 = the
    // legacy one-dimensional walk); addr_lfsr replaces the counter with an
    // INDEX_WIDTH-bit LFSR. Both sampled at cfg_start like the rest.
    input  logic [3:0]                          cfg_idx1_shift,
    input  logic                                cfg_addr_lfsr,
    // idx1_bit = 1 (pumice TASK-060): dimension 1 is the single bit
    // idx1_shift of the index, dimension 0 the index with that bit removed
    // (see the header). Ignored in hammer mode.
    input  logic                                cfg_idx1_bit,

    // Data source select: 0 = phase-counter LFSR (default, OOO-unsafe);
    // 1 = address-derived hash (OOO-safe, data is f(beat_byte_addr));
    // 2 = fill_pattern replicated across the data bus.
    // Hash mode lets multi-id / OOO-completion traffic still validate
    // because each beat's expected data is a pure function of its
    // address — no phase counter to get out of sync. The 3 seeds drive
    // a Murmur3-fmix-style mixer (xor-shift + odd mul) so all-zero or
    // all-one input addresses don't collapse to stuck output patterns.
    input  logic [1:0]                          cfg_data_mode,
    input  logic [31:0]                         cfg_fill_pattern,
    input  logic [31:0]                         cfg_hash_seed0,
    input  logic [31:0]                         cfg_hash_seed1,
    input  logic [31:0]                         cfg_hash_seed2,

    // Inter-burst idle gap. Adds 0..2^GAP_WIDTH-1 idle cycles (0..15 at the
    // default width) between the end of one burst (wlast accepted) and the
    // next AW request. Used to vary the throughput stress on the downstream
    // controller during sweeps.
    input  logic [GAP_WIDTH-1:0]                cfg_wr_gap,
    // gap_sweep = 1 (pumice TASK-060): the gap after burst n is cfg_wr_gap +
    // (n mod 8), saturating at the port width (see the header).
    input  logic                                cfg_gap_sweep,

    // ---- Runtime cap on bursts in flight ----
    // MAX_OUTSTANDING is the hardware ceiling (queues and counters are built
    // for it); this dials the ACTIVE limit down without a rebuild, which is
    // what a bandwidth-vs-outstanding sweep needs -- one bitstream walks the
    // whole curve instead of one bitstream per point.
    //
    // 0 means "use MAX_OUTSTANDING", so an instance that ties this off behaves
    // exactly as it did before the port existed. Values above MAX_OUTSTANDING
    // clamp to it rather than wrapping: the counters are sized for the
    // parameter, and a host that writes 40 into a 32-deep engine should get 32
    // and a curve that flattens, not a silent wrap to 8.
    input  logic [OSW-1:0]                      cfg_max_outstanding,

    // Start / done handshake
    input  logic                                cfg_start,        // pulse → begin workload
    output logic                                cfg_done,         // high once all B's received

    // ==========================================================================
    // Telemetry
    // ==========================================================================
    output logic [CRC_WIDTH-1:0]                o_expected_crc,
    output logic                                o_expected_crc_valid,  // high with cfg_done
    output logic                                o_bresp_error,         // sticky on any non-OKAY BRESP

    // ==========================================================================
    // M-side AXI4 (out to the fabric → controller → DRAM)
    // ==========================================================================
    output logic [IW-1:0]              m_axi_awid,
    output logic [AW-1:0]              m_axi_awaddr,
    output logic [7:0]                 m_axi_awlen,
    output logic [2:0]                 m_axi_awsize,
    output logic [1:0]                 m_axi_awburst,
    output logic                       m_axi_awlock,
    output logic [3:0]                 m_axi_awcache,
    output logic [2:0]                 m_axi_awprot,
    output logic [3:0]                 m_axi_awqos,
    output logic [3:0]                 m_axi_awregion,
    output logic [UW-1:0]              m_axi_awuser,
    output logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    output logic [DW-1:0]              m_axi_wdata,
    output logic [SW-1:0]              m_axi_wstrb,
    output logic                       m_axi_wlast,
    output logic [UW-1:0]              m_axi_wuser,
    output logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,

    input  logic [IW-1:0]              m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [UW-1:0]              m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready
);

    //==========================================================================
    // Active outstanding limit
    //==========================================================================
    // Resolve the runtime dial against the built ceiling once, here, so every
    // use downstream reads one signal and cannot disagree about the policy.
    // Zero means "as built"; anything above the ceiling saturates at it.
    logic [OSW-1:0] w_os_limit;
    assign w_os_limit = (cfg_max_outstanding == '0)                    ? OSW'(MAX_OUTSTANDING)
                      : (cfg_max_outstanding > OSW'(MAX_OUTSTANDING))  ? OSW'(MAX_OUTSTANDING)
                                                                       : cfg_max_outstanding;

    //==========================================================================
    // Config guard — the AxLEN==integer-multiple-of-DRAM-burst requirement.
    // On each cfg_start, verify cfg_burst_len is a nonzero multiple of
    // BURST_LEN_MULTIPLE (AXI beats per DRAM burst). A non-conforming value would
    // otherwise SILENTLY produce a ragged final sub-command (pumice_wr_splitter)
    // that SLVERRs / partial-writes at pumice_wr_intake. Sim-only ($error); on
    // silicon the host must validate before programming BLEN_TXN. Skipped when
    // BURST_LEN_MULTIPLE==1 (unconstrained).
    //==========================================================================
`ifndef SYNTHESIS
    always_ff @(posedge aclk) begin
        if (aresetn && cfg_start && (BURST_LEN_MULTIPLE > 1)) begin
            assert (cfg_burst_len != 8'd0)
                else $error("axi4_master_wr_injector: cfg_burst_len=0 illegal");
            assert ((32'(cfg_burst_len) % BURST_LEN_MULTIPLE) == 0)
                else $error("axi4_master_wr_injector: cfg_burst_len=%0d not a multiple of BURST_LEN_MULTIPLE=%0d (AXI beats per DRAM burst) -> ragged burst -> SLVERR/partial write",
                            cfg_burst_len, BURST_LEN_MULTIPLE);
        end
    end
`endif

    //==========================================================================
    // FSM — fully decoupled AW and W (two independent addr-gens). awvalid
    // never drops from first assertion to last AW handshake at gap=0.
    //==========================================================================
    typedef enum logic [1:0] {
        S_IDLE = 2'd0,   // wait for cfg_start
        S_RUN  = 2'd1,   // AW + W paths active
        S_GAP  = 2'd2,   // cfg_wr_gap idle cycles between bursts
        S_DONE = 2'd3    // all wlast issued; await final B's
    } state_e;

    state_e                       r_state;

    // Latched workload program (sampled at cfg_start so software can change
    // cfg_* in the next cycle without disturbing the run).
    logic [AW-1:0]                r_base_addr;
    logic signed [STRIDE_WIDTH-1:0] r_stride_0, r_stride_1;
    logic [AW-1:0]                r_wrap_0, r_wrap_1;
    logic [7:0]                   r_burst_len;
    logic [GAP_WIDTH-1:0]         r_wr_gap;
    logic [TXN_COUNT_WIDTH-1:0]   r_txn_count;
    logic [IW-1:0]                r_axi_id;
    logic [2:0]                   r_axi_size;
    logic [1:0]                   r_axi_burst;
    logic [LFSR_WIDTH-1:0]        r_lfsr_seed_eff;
    logic                         r_hammer_en;       // rowhammer address mode
    logic [3:0]                   r_idx1_shift;      // TASK-049 index split (0 = legacy)
    logic                         r_addr_lfsr;       // TASK-049 LFSR index source
    logic                         r_idx1_bit;        // TASK-060 one-bit split
    logic                         r_gap_sweep;       // TASK-060 gap walks 0..7 above the base
    logic [2:0]                   r_gap_phase;       // bursts done mod 8 (the sweep index)
    logic [1:0]                   r_data_mode;       // 0=LFSR, 1=ADDR_HASH, 2=FILL
    logic [31:0]                  r_fill_pattern;
    logic [31:0]                  r_hash_seed0;
    logic [31:0]                  r_hash_seed1;
    logic [31:0]                  r_hash_seed2;
    logic [1:0]                   r_id_mode;         // 0=FIXED, 1=COUNTER, 2=LFSR
    logic [7:0]                   r_id_counter;      // 8-bit AW ID counter

    // Progress counters — AW and W paths advance independently. AW path
    // tracks request + handshake counts for the AW addr-gen. W path
    // tracks request + handshake counts for the W addr-gen.
    logic [TXN_COUNT_WIDTH-1:0]   r_aw_req_count;     // AW addr-gen req handshakes
    logic [TXN_COUNT_WIDTH-1:0]   r_aw_issued;        // AW handshakes
    logic [TXN_COUNT_WIDTH-1:0]   r_w_req_count;      // W addr-gen req handshakes
    logic [TXN_COUNT_WIDTH-1:0]   r_w_bursts_done;    // wlast handshakes
    logic [TXN_COUNT_WIDTH-1:0]   r_b_received;       // B handshakes
    logic [7:0]                   r_w_beat_idx;       // beat in current W burst
    logic [GAP_WIDTH-1:0]         r_gap_left;         // S_GAP countdown

    //==========================================================================
    // dma_address_gen — two independent instances walking the same
    // descriptor. AW path uses u_addr_gen_aw; W path uses u_addr_gen_w.
    // Same cfg + same indices => same address sequence in both.
    //
    // In hammer mode the index is the LSB of the transaction counter so
    // addresses alternate base / base+stride_0 per transaction. The mux
    // is applied identically to AW and W to keep the two channels in
    // lockstep.
    //
    // The index below is shaped combinationally (LFSR / counter mux, the
    // idx1_shift split, the lo mask) and the generator's first stage is a
    // DSP multiply plus the wrap mask. In one clock that was 6 LUT levels +
    // an unregistered DSP48, 10.5 ns on the Nexys A7 harness at 100 MHz, the
    // single largest failing class on the board (2026-10-28). INPUT_REG puts a
    // flop between the two; the address arrives one cycle later, which the
    // valid/ready plumbing absorbs.
    //==========================================================================
    logic [INDEX_WIDTH-1:0]       w_aw_addr_index;
    logic [INDEX_WIDTH-1:0]       w_w_addr_index;

    logic [INDEX_WIDTH-1:0]       w_aw_addr_index_1;
    logic [INDEX_WIDTH-1:0]       w_w_addr_index_1;
    // assigned with the index shaping below (TASK-049), after the LFSRs

    logic                         w_aw_addr_req_valid;
    logic                         w_aw_addr_req_ready;
    logic                         w_aw_addr_result_valid;
    logic                         w_aw_addr_result_ready;
    logic [AW-1:0]                w_aw_addr_result;

    logic                         w_w_addr_req_valid;
    logic                         w_w_addr_req_ready;
    logic                         w_w_addr_result_valid;
    logic                         w_w_addr_result_ready;
    logic [AW-1:0]                w_w_addr_result;

    dma_address_gen #(
        .ADDR_WIDTH  (AW),
        .INDEX_WIDTH (INDEX_WIDTH),
        .STRIDE_WIDTH(STRIDE_WIDTH),
        .TAG_WIDTH   (8),
        .INPUT_REG   (1'b1)
    ) u_addr_gen_aw (
        .i_clk             (aclk),
        .i_rst_n           (aresetn),

        .i_cfg_base_addr   (r_base_addr),
        .i_cfg_stride_0    (r_stride_0),
        .i_cfg_stride_1    (r_stride_1),
        .i_cfg_wrap_mask_0 (r_wrap_0),
        .i_cfg_wrap_mask_1 (r_wrap_1),

        .i_req_valid       (w_aw_addr_req_valid),
        .o_req_ready       (w_aw_addr_req_ready),
        .i_req_index_0     (w_aw_addr_index),
        .i_req_index_1     (w_aw_addr_index_1),
        .i_req_tag         (8'd0),

        .o_result_valid    (w_aw_addr_result_valid),
        .i_result_ready    (w_aw_addr_result_ready),
        .o_result_addr     (w_aw_addr_result),
        .o_result_tag      ()
    );

    dma_address_gen #(
        .ADDR_WIDTH  (AW),
        .INDEX_WIDTH (INDEX_WIDTH),
        .STRIDE_WIDTH(STRIDE_WIDTH),
        .TAG_WIDTH   (8),
        .INPUT_REG   (1'b1)
    ) u_addr_gen_w (
        .i_clk             (aclk),
        .i_rst_n           (aresetn),

        .i_cfg_base_addr   (r_base_addr),
        .i_cfg_stride_0    (r_stride_0),
        .i_cfg_stride_1    (r_stride_1),
        .i_cfg_wrap_mask_0 (r_wrap_0),
        .i_cfg_wrap_mask_1 (r_wrap_1),

        .i_req_valid       (w_w_addr_req_valid),
        .o_req_ready       (w_w_addr_req_ready),
        .i_req_index_0     (w_w_addr_index),
        .i_req_index_1     (w_w_addr_index_1),
        .i_req_tag         (8'd0),

        .o_result_valid    (w_w_addr_result_valid),
        .i_result_ready    (w_w_addr_result_ready),
        .o_result_addr     (w_w_addr_result),
        .o_result_tag      ()
    );

    //==========================================================================
    // LFSR — advances on every accepted W beat (or seed-load at cfg_start).
    //==========================================================================
    logic                         w_w_beat;       // accepted W beat at FUB side
    logic                         w_lfsr_load;    // pulse cfg_start to load seed
    logic [LFSR_WIDTH-1:0]        w_lfsr_out;

    // Seed value to drive on cfg_start. r_lfsr_seed_eff updates one
    // cycle later (NBA from the FSM block), so to load the *correct*
    // seed at cfg_start we must mux it combinationally here.
    logic [LFSR_WIDTH-1:0] w_lfsr_seed_data;
    assign w_lfsr_seed_data = w_lfsr_load
                            ? ((cfg_lfsr_seed == '0) ? LFSR_SEED
                                                     : cfg_lfsr_seed)
                            : r_lfsr_seed_eff;

    shifter_lfsr_fibonacci #(
        .WIDTH          (LFSR_WIDTH),
        .TAP_INDEX_WIDTH(12),
        .TAP_COUNT      (4)
    ) u_lfsr (
        .clk      (aclk),
        .rst_n    (aresetn),
        .enable   (w_w_beat || w_lfsr_load),
        .seed_load(w_lfsr_load),
        .seed_data(w_lfsr_seed_data),
        .taps     (LFSR_TAPS),
        .lfsr_out (w_lfsr_out),
        .lfsr_done()
    );

    //==========================================================================
    // Address index shaping (TASK-049). Two INDEX_WIDTH-bit LFSRs, one per
    // address path, seeded together at cfg_start from the same seed as the
    // data LFSR (forced odd so it is never the all-zero lock-up state) and
    // stepped on their own path's request accept -- the k-th AW/W request
    // therefore reads the k-th value on both paths. The index then splits:
    // low idx1_shift bits to dimension 0, the rest to dimension 1.
    //==========================================================================
    logic [INDEX_WIDTH-1:0] w_aw_idx_lfsr, w_w_idx_lfsr, w_idx_seed;
    logic [INDEX_WIDTH-1:0] w_aw_idx_raw,  w_w_idx_raw,  w_idx_lo_mask;
    assign w_idx_seed = INDEX_WIDTH'(w_lfsr_seed_data) | INDEX_WIDTH'(1);

    shifter_lfsr_fibonacci #(
        .WIDTH          (INDEX_WIDTH),
        .TAP_INDEX_WIDTH(12),
        .TAP_COUNT      (4)
    ) u_idx_lfsr_aw (
        .clk      (aclk),
        .rst_n    (aresetn),
        .enable   ((w_aw_addr_req_valid && w_aw_addr_req_ready) || w_lfsr_load),
        .seed_load(w_lfsr_load),
        .seed_data(w_idx_seed),
        .taps     (ADDR_LFSR_TAPS),
        .lfsr_out (w_aw_idx_lfsr),
        .lfsr_done()
    );

    shifter_lfsr_fibonacci #(
        .WIDTH          (INDEX_WIDTH),
        .TAP_INDEX_WIDTH(12),
        .TAP_COUNT      (4)
    ) u_idx_lfsr_w (
        .clk      (aclk),
        .rst_n    (aresetn),
        .enable   ((w_w_addr_req_valid && w_w_addr_req_ready) || w_lfsr_load),
        .seed_load(w_lfsr_load),
        .seed_data(w_idx_seed),
        .taps     (ADDR_LFSR_TAPS),
        .lfsr_out (w_w_idx_lfsr),
        .lfsr_done()
    );

    assign w_aw_idx_raw  = r_addr_lfsr ? w_aw_idx_lfsr : INDEX_WIDTH'(r_aw_req_count);
    assign w_w_idx_raw  = r_addr_lfsr ? w_w_idx_lfsr : INDEX_WIDTH'(r_w_req_count);
    assign w_idx_lo_mask  = (r_idx1_shift == 4'd0) ? {INDEX_WIDTH{1'b1}}
                          : ((INDEX_WIDTH'(1) << r_idx1_shift) - INDEX_WIDTH'(1));
    // one-bit split (TASK-060): dimension 1 = bit k, dimension 0 = the index
    // with bit k squeezed out (low k bits kept, the rest shifted down one)
    logic [INDEX_WIDTH-1:0] w_idx_bit_lo_mask, w_aw_idx_bit0, w_w_idx_bit0, w_aw_idx_bit1, w_w_idx_bit1;
    logic [4:0]             w_idx1_shift_p1;
    assign w_idx_bit_lo_mask = (INDEX_WIDTH'(1) << r_idx1_shift) - INDEX_WIDTH'(1);
    assign w_idx1_shift_p1   = 5'(r_idx1_shift) + 5'd1;
    assign w_aw_idx_bit0 = (w_aw_idx_raw & w_idx_bit_lo_mask) | ((w_aw_idx_raw >> w_idx1_shift_p1) << r_idx1_shift);
    assign w_w_idx_bit0  = (w_w_idx_raw  & w_idx_bit_lo_mask) | ((w_w_idx_raw  >> w_idx1_shift_p1) << r_idx1_shift);
    assign w_aw_idx_bit1 = (w_aw_idx_raw >> r_idx1_shift) & INDEX_WIDTH'(1);
    assign w_w_idx_bit1  = (w_w_idx_raw  >> r_idx1_shift) & INDEX_WIDTH'(1);
    // hammer mode keeps its legacy meaning: index_0 = counter LSB, index_1 = 0
    assign w_aw_addr_index   = r_hammer_en ? INDEX_WIDTH'(r_aw_req_count[0])
                             : r_idx1_bit  ? w_aw_idx_bit0 : (w_aw_idx_raw & w_idx_lo_mask);
    assign w_w_addr_index   = r_hammer_en ? INDEX_WIDTH'(r_w_req_count[0])
                             : r_idx1_bit  ? w_w_idx_bit0  : (w_w_idx_raw & w_idx_lo_mask);
    assign w_aw_addr_index_1 = r_hammer_en ? INDEX_WIDTH'(0)
                             : r_idx1_bit  ? w_aw_idx_bit1
                             : (r_idx1_shift == 4'd0) ? INDEX_WIDTH'(0) : (w_aw_idx_raw >> r_idx1_shift);
    assign w_w_addr_index_1 = r_hammer_en ? INDEX_WIDTH'(0)
                             : r_idx1_bit  ? w_w_idx_bit1
                             : (r_idx1_shift == 4'd0) ? INDEX_WIDTH'(0) : (w_w_idx_raw >> r_idx1_shift);

    // gap after the burst now finishing: the base, or base + phase in a sweep,
    // saturating at the port width
    localparam int GSW = GAP_WIDTH + 1;
    logic [GSW-1:0]       w_gap_sum;
    logic [GAP_WIDTH-1:0] w_gap_now;
    assign w_gap_sum = GSW'(r_wr_gap) + GSW'(r_gap_phase);
    assign w_gap_now = !r_gap_sweep ? r_wr_gap
                     : (w_gap_sum[GSW-1] ? {GAP_WIDTH{1'b1}} : w_gap_sum[GAP_WIDTH-1:0]);

    //==========================================================================
    // CRC — accumulates over the SAME LFSR stream we send out on W.
    //==========================================================================
    logic [CRC_WIDTH-1:0]         w_expected_crc;
    logic [1:0]                   r_crc_capture_pending;
    logic                         w_crc_load_start;

    assign w_crc_load_start = w_lfsr_load;

    // dataint_crc's CHUNKS = DATA_WIDTH / 8 → 4 for 32-bit. cascade_sel
    // selects which byte index drives the cascade; tie all 4 hot so every
    // byte of every LFSR output participates in the CRC.
    localparam int W_CRC_CHUNKS = CRC_DATA_WIDTH / 8;

    dataint_crc #(
        .DATA_WIDTH(CRC_DATA_WIDTH),
        .CRC_WIDTH (CRC_WIDTH),
        .REFIN     (CRC_REFIN),
        .REFOUT    (CRC_REFOUT)
    ) u_crc (
        .POLY              (CRC_POLY),
        .POLY_INIT         (CRC_POLY_INIT),
        .XOROUT            (CRC_XOROUT),
        .clk               (aclk),
        .rst_n             (aresetn),
        .load_crc_start    (w_crc_load_start),
        .load_from_cascade (w_w_beat),  // accumulate pre-advance LFSR word on every accepted W beat
        .cascade_sel       ({W_CRC_CHUNKS{1'b1}}),
        .data              (w_lfsr_out),
        .crc               (w_expected_crc)
    );

    //==========================================================================
    // FUB-side AXI handshakes — driven from FSM + LFSR
    //==========================================================================
    logic                         fub_awvalid;
    logic                         fub_awready;
    logic                         fub_wvalid;
    logic                         fub_wready;
    logic                         fub_wlast;
    logic                         fub_bvalid;
    logic                         fub_bready;
    logic [1:0]                   fub_bresp;

    // Production-side W-beat signals (into the hash pipeline). Distinct from
    // the master-facing fub_wvalid/fub_wlast, which are driven by the staging
    // FIFO output (see Data path). Pipelining the hash decouples the two.
    logic                         w_gen_valid;
    logic                         w_gen_wlast;

    //==========================================================================
    // AW ID generator — three modes muxed by r_id_mode.
    //   FIXED:   pass r_axi_id through.
    //   COUNTER: 8-bit counter, seeded with cfg_axi_id[7:0] at cfg_start,
    //            +1 per AW handshake (wraps).
    //   LFSR:    8-bit maximal-length Fibonacci LFSR with taps {7,6,5,1},
    //            seeded with cfg_axi_id[7:0] | 8'h01 (avoid all-zero seed).
    //==========================================================================
    logic [7:0]  w_id_lfsr_out;
    logic        w_id_lfsr_advance;

    assign w_id_lfsr_advance = fub_awvalid && fub_awready;

    shifter_lfsr_fibonacci #(
        .WIDTH          (8),
        .TAP_INDEX_WIDTH(4),
        .TAP_COUNT      (4)
    ) u_id_lfsr (
        .clk      (aclk),
        .rst_n    (aresetn),
        .enable   (w_id_lfsr_advance || w_lfsr_load),
        .seed_load(w_lfsr_load),
        .seed_data(cfg_axi_id[7:0] | 8'h01),
        .taps     ({4'd7, 4'd6, 4'd5, 4'd1}),
        .lfsr_out (w_id_lfsr_out),
        .lfsr_done()
    );

    // Mode mux for awid
    logic [IW-1:0] w_aw_id_out;
    always_comb begin
        unique case (r_id_mode)
            2'd0:    w_aw_id_out = r_axi_id;
            2'd1:    w_aw_id_out = IW'(r_id_counter);
            2'd2:    w_aw_id_out = IW'(w_id_lfsr_out);
            default: w_aw_id_out = r_axi_id;
        endcase
    end

    // w_w_beat (pipeline admit) is defined in the Data path section below,
    // where the staging-FIFO occupancy is known.

    // ---- AW path ----
    // Keep the AW addr-gen requested for every AW we'll issue. addr-gen
    // self-throttles via req_ready.
    assign w_aw_addr_req_valid = (r_state == S_RUN)
                              && (r_aw_req_count < r_txn_count);

    // awvalid stays asserted as long as we have AWs left and the addr-gen
    // has produced the next address. No outstanding cap — slave's awready
    // throttles. Gap pauses by switching state away from S_RUN.
    //
    // With a gap, an AW may not run ahead of the W data: the next burst's AW
    // issues only once every earlier burst's W has finished (wlast accepted).
    // Otherwise AWs pipelined during burst k reach the slave and then wait
    // out the gap for their W data -- and AXI4 W follows AW order at the
    // slave (no WID), so every OTHER master's write behind them waits too.
    // On a shared slave that turned the gap into head-of-line blocking: a
    // second writer was paced to the injector's gap instead of using the
    // idle time (Genesys 2 fabric benchmark W3 mirror, 2026-10-16). At gap 0
    // AWs still pipeline freely.
    assign fub_awvalid       = (r_state == S_RUN)
                            && (r_aw_issued < r_txn_count)
                            && ((r_aw_issued - r_b_received) < TXN_COUNT_WIDTH'(w_os_limit))
                            && (((r_wr_gap == '0) && !r_gap_sweep) || (r_aw_issued == r_w_bursts_done))
                            && w_aw_addr_result_valid;
    assign w_aw_addr_result_ready = fub_awvalid && fub_awready;

    // ---- W path ----
    // Same shape on the W addr-gen: keep requesting per-burst base
    // addresses. Pop on wlast so the next burst's base lines up.
    assign w_w_addr_req_valid = (r_state == S_RUN)
                             && (r_w_req_count < r_txn_count);

    // W-beat PRODUCTION (into the hash pipeline). Produce when (a) the slave
    // has at least seen this burst's AW (r_w_bursts_done < r_aw_issued) and
    // (b) the W addr-gen has produced the base address. The actual admit
    // (w_w_beat) additionally requires staging-FIFO room — see Data path.
    // The master's fub_wvalid/fub_wlast are driven from the FIFO output.
    assign w_gen_valid       = (r_state == S_RUN)
                            && (r_w_bursts_done < r_aw_issued)
                            && w_w_addr_result_valid;
    assign w_gen_wlast       = w_gen_valid
                            && (r_w_beat_idx == r_burst_len - 8'd1);
    assign w_w_addr_result_ready = w_w_beat && w_gen_wlast;

    // B is always ready once we're past IDLE so the slave can drain B's
    // even during S_GAP or S_DONE.
    assign fub_bready        = (r_state != S_IDLE);

    //==========================================================================
    // Data path — three sources, muxed by r_data_mode:
    //   mode 0: 32-bit Fibonacci LFSR replicated across DW (phase-counter,
    //           breaks under multi-id / OOO completion)
    //   mode 1: 32-bit Murmur3-fmix-style address hash, per-32-bit slice
    //           (OOO-safe: each beat's data is f(byte_addr, seeds), so
    //           reorder doesn't perturb the per-beat compare)
    //   mode 2: cfg_fill_pattern replicated across DW (constant per beat,
    //           used for rowhammer aggressor fills)
    //
    // In modes 1 and 2 the CRC pipeline (built for the phase-counter
    // contract) is not load-bearing; o_expected_crc_valid is gated low and
    // the harness must use per-beat compare (o_data_error) for integrity.
    //==========================================================================
    localparam int REP     = (DW + 31) / 32;   // 32-bit slices per beat

    logic [REP*32-1:0] w_data_replicated;
    assign w_data_replicated = {REP{w_lfsr_out}};

    // Per-beat byte address for the CURRENT W burst. Anchored on
    // w_w_addr_result (the W addr-gen's current output) and stepped by
    // 2**axsize bytes per beat. Full-beat writes only — strobes all-ones.
    logic [AW-1:0]                w_byte_addr_for_beat;
    assign w_byte_addr_for_beat = w_w_addr_result
        + (AW'({{(AW-8){1'b0}}, r_w_beat_idx}) << r_axi_size);

    //-------------------------------------------------------------------------
    // Address hash: four seeded rotate-XOR rounds, combinational
    //-------------------------------------------------------------------------
    // Each beat's data is a pure function of its byte address, which is what
    // lets a reader validate a beat wherever it lands (out of order, any id).
    // The function used to be Murmur3 fmix -- two 32-bit multiplies -- and two
    // multiplies do not fit in a cycle, so it was cut into a four-stage
    // pipeline, and because a fixed-latency pipeline cannot stall it needed a
    // 16-deep staging FIFO behind it to catch beats already in flight.
    //
    // A rotate is free on an FPGA: it is wiring. Four `x ^= rotl(x, k)` rounds
    // with the seeds folded in reach the same place in a few LUT levels, so
    // the pipeline, its multipliers and the staging FIFO all go away. The
    // engine is an artificial traffic source; it should not cost DSPs.
    //
    // Rotate constants (23, 21, 17, 7) were chosen by measuring avalanche --
    // the mean fraction of output bits that flip per input bit flipped, where
    // 0.5 is ideal -- over the address space this drives:
    //
    //                          zero seeds    board seeds
    //   Murmur3 fmix              0.050          0.500
    //   rotate-XOR (this)         0.500          0.500
    //
    // It is not merely cheaper, it is better where it was worst. With the
    // default all-zero seeds the old function degenerated: `s|1` makes both
    // multipliers 1, so fmix collapsed to two right-shifts and adjacent beats
    // differed by as little as ONE bit. An off-by-one-beat addressing bug
    // could compare almost equal. Here adjacent beats differ by 8 bits at
    // worst, 16.8 on average, seeds or no seeds.
    //
    // Changing the function changes every expected data value, which is fine
    // and checked: writer, reader and the Python mirror in
    // bin/TBClasses/axi4/axi4_master_wr_injector_tb.py::addr_hash32 must
    // agree bit for bit, and the cross-block CRC compare fails loudly if they
    // do not. Keep all three in step.
    // Argument is `v`, not `x`: f_addr_hash32 below declares its own local
    // `x`, and the declaration-order checker reads the file linearly -- a
    // function argument sharing a name with a later local reads as a use
    // before declaration. Cheap to avoid, and the checker is right to be
    // literal about it.
    function automatic logic [31:0] f_rotl32(input logic [31:0] v,
                                             input int unsigned k);
        return (v << k) | (v >> (32 - k));
    endfunction

    function automatic logic [31:0] f_addr_hash32(input logic [31:0] addr);
        logic [31:0] x;
        x = addr ^ r_hash_seed0;
        x = x ^ f_rotl32(x, 23);
        x = x ^ r_hash_seed1;
        x = x ^ f_rotl32(x, 21);
        x = x ^ f_rotl32(x, 17);
        x = x ^ r_hash_seed2;
        x = x ^ f_rotl32(x, 7);
        return x;
    endfunction

    // Lanes are keyed on the BUS-ALIGNED beat address: lane s carries the bytes
    // at aligned + 4s whatever the transfer size, so a narrow beat (axi_size
    // below the bus width) puts its data in the lanes its strobes enable and a
    // reader can check any lane from the address alone. Full-width beats start
    // bus-aligned, so for them this is the previous function bit for bit.
    localparam int LANE_B = $clog2(SW);
    logic [AW-1:0] w_beat_addr_aligned;
    assign w_beat_addr_aligned = {w_byte_addr_for_beat[AW-1:LANE_B], {LANE_B{1'b0}}};
    logic [DW-1:0] w_hash_wdata;
    always_comb begin
        w_hash_wdata = '0;
        for (int s = 0; s < REP; s++) begin
            w_hash_wdata[s*32 +: 32] =
                f_addr_hash32(w_beat_addr_aligned[31:0] + 32'(s * 4));
        end
    end
    // Strobes: all lanes for a full-width beat; for a narrow beat the 2**size
    // bytes at the beat's offset within the bus (AXI A3.4.3). The injector
    // used to drive all-ones for every size, which made a "narrow" write a
    // full write (pumice TASK-060 needed real half-burst writes).
    logic [SW-1:0] w_wstrb_out;
    always_comb begin
        if (r_axi_size >= 3'(LANE_B)) w_wstrb_out = {SW{1'b1}};
        else begin
            automatic logic [SW:0] ones = ((SW+1)'(1) << (1 << r_axi_size)) - (SW+1)'(1);
            w_wstrb_out = SW'(ones << w_byte_addr_for_beat[LANE_B-1:0]);
        end
    end

    // FILL mode: cfg_fill_pattern replicated across the data bus.
    logic [DW-1:0] w_fill_wdata;
    assign w_fill_wdata = {REP{cfg_fill_pattern}};

    // Mode mux: hash data, raw LFSR stream, or replicated fill pattern.
    // All three are available this cycle.
    logic [DW-1:0] w_wdata_out;
    always_comb begin
        unique case (r_data_mode)
            2'd0:    w_wdata_out = w_data_replicated[DW-1:0];
            2'd1:    w_wdata_out = w_hash_wdata;
            2'd2:    w_wdata_out = w_fill_wdata[DW-1:0];
            default: w_wdata_out = w_data_replicated[DW-1:0];
        endcase
    end

    // W is driven straight from the generator now. There is no pipeline to
    // decouple from, so a beat is admitted exactly when the AXI W channel
    // takes one -- which is also what makes the engine stallable rather than
    // free-running.
    assign fub_wlast  = w_gen_wlast;
    assign fub_wvalid = w_gen_valid;
    assign w_w_beat   = fub_wvalid && fub_wready;

    //==========================================================================
    // Sequential FSM + counters
    //==========================================================================
    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_state           <= S_IDLE;
            r_base_addr       <= '0;
            r_stride_0        <= '0;
            r_stride_1        <= '0;
            r_wrap_0          <= '0;
            r_wrap_1          <= '0;
            r_burst_len       <= 8'd0;
            r_wr_gap          <= '0;
            r_txn_count       <= '0;
            r_axi_id          <= '0;
            r_axi_size        <= 3'd0;
            r_axi_burst       <= 2'd1;   // INCR
            r_lfsr_seed_eff   <= LFSR_SEED;
            r_hammer_en       <= 1'b0;
            r_idx1_shift      <= 4'd0;
            r_addr_lfsr       <= 1'b0;
            r_idx1_bit        <= 1'b0;
            r_gap_sweep       <= 1'b0;
            r_gap_phase       <= 3'd0;
            r_data_mode       <= 2'b00;
            r_fill_pattern    <= 32'd0;
            r_hash_seed0      <= 32'd0;
            r_hash_seed1      <= 32'd0;
            r_hash_seed2      <= 32'd0;
            r_id_mode         <= 2'd0;
            r_id_counter      <= 8'd0;
            r_aw_req_count    <= '0;
            r_aw_issued       <= '0;
            r_w_req_count     <= '0;
            r_w_bursts_done   <= '0;
            r_b_received      <= '0;
            r_w_beat_idx      <= 8'd0;
            r_gap_left        <= '0;
            o_expected_crc       <= '0;
            o_expected_crc_valid <= 1'b0;
            r_crc_capture_pending <= 2'b00;
            o_bresp_error        <= 1'b0;
        end else begin
            unique case (r_state)
                S_IDLE: begin
                    if (cfg_start) begin
                        // Latch the program
                        r_base_addr     <= cfg_start_addr;
                        r_stride_0      <= cfg_addr_stride_0;
                        r_stride_1      <= cfg_addr_stride_1;
                        r_wrap_0        <= cfg_addr_wrap_mask_0;
                        r_wrap_1        <= cfg_addr_wrap_mask_1;
                        r_burst_len     <= (cfg_burst_len == 8'd0) ? 8'd1 : cfg_burst_len;
                        r_wr_gap        <= cfg_wr_gap;
                        r_txn_count     <= cfg_txn_count;
                        r_axi_id        <= cfg_axi_id;
                        r_axi_size      <= cfg_axi_size;
                        r_axi_burst     <= cfg_axi_burst;
                        r_lfsr_seed_eff <= (cfg_lfsr_seed == '0) ? LFSR_SEED : cfg_lfsr_seed;
                        r_hammer_en     <= cfg_hammer_en;
                        r_idx1_shift    <= cfg_idx1_shift;
                        r_addr_lfsr     <= cfg_addr_lfsr;
                        r_idx1_bit      <= cfg_idx1_bit;
                        r_gap_sweep     <= cfg_gap_sweep;
                        r_gap_phase     <= 3'd0;
                        r_data_mode     <= cfg_data_mode;
                        r_fill_pattern  <= cfg_fill_pattern;
                        r_hash_seed0    <= cfg_hash_seed0;
                        r_hash_seed1    <= cfg_hash_seed1;
                        r_hash_seed2    <= cfg_hash_seed2;
                        r_id_mode       <= cfg_id_mode;
                        r_id_counter    <= cfg_axi_id[7:0];
                        r_aw_req_count   <= '0;
                        r_aw_issued      <= '0;
                        r_w_req_count    <= '0;
                        r_w_bursts_done  <= '0;
                        r_b_received     <= '0;
                        r_w_beat_idx     <= 8'd0;
                        r_gap_left       <= '0;
                        o_expected_crc_valid <= 1'b0;
                        o_bresp_error        <= 1'b0;
                        r_state         <= (cfg_txn_count == '0) ? S_DONE : S_RUN;
                    end
                end

                S_RUN: begin
                    // ---- AW addr-gen req counter ----
                    if (w_aw_addr_req_valid && w_aw_addr_req_ready) begin
                        r_aw_req_count <= r_aw_req_count + 1'b1;
                    end
                    // ---- AW handshake ----
                    if (fub_awvalid && fub_awready) begin
                        r_aw_issued  <= r_aw_issued + 1'b1;
                        // Advance the ID counter regardless of mode — it's
                        // only sourced when r_id_mode==COUNTER, but keeping
                        // it free-running is harmless and avoids a mode
                        // branch in the critical path.
                        r_id_counter <= r_id_counter + 8'd1;
                    end
                    // ---- W addr-gen req counter ----
                    if (w_w_addr_req_valid && w_w_addr_req_ready) begin
                        r_w_req_count <= r_w_req_count + 1'b1;
                    end

                    // ---- W beat handshake (production/admit into pipeline) ----
                    if (w_w_beat) begin
                        if (w_gen_wlast) begin
                            r_w_beat_idx    <= 8'd0;
                            r_w_bursts_done <= r_w_bursts_done + 1'b1;
                            r_gap_phase     <= r_gap_phase + 3'd1;
                            if (r_w_bursts_done + 1'b1 == r_txn_count) begin
                                r_state <= S_DONE;
                            end else if (w_gap_now != '0) begin
                                r_state    <= S_GAP;
                                r_gap_left <= w_gap_now;
                            end
                        end else begin
                            r_w_beat_idx <= r_w_beat_idx + 8'd1;
                        end
                    end
                end

                S_GAP: begin
                    if (r_gap_left == GAP_WIDTH'(1)) begin
                        r_state    <= S_RUN;
                        r_gap_left <= '0;
                    end else begin
                        r_gap_left <= r_gap_left - GAP_WIDTH'(1);
                    end
                end

                S_DONE: begin
                    if (cfg_start) begin
                        // Re-arm directly — same latch set as S_IDLE.
                        r_base_addr     <= cfg_start_addr;
                        r_stride_0      <= cfg_addr_stride_0;
                        r_stride_1      <= cfg_addr_stride_1;
                        r_wrap_0        <= cfg_addr_wrap_mask_0;
                        r_wrap_1        <= cfg_addr_wrap_mask_1;
                        r_burst_len     <= (cfg_burst_len == 8'd0) ? 8'd1 : cfg_burst_len;
                        r_wr_gap        <= cfg_wr_gap;
                        r_txn_count     <= cfg_txn_count;
                        r_axi_id        <= cfg_axi_id;
                        r_axi_size      <= cfg_axi_size;
                        r_axi_burst     <= cfg_axi_burst;
                        r_lfsr_seed_eff <= (cfg_lfsr_seed == '0) ? LFSR_SEED : cfg_lfsr_seed;
                        r_hammer_en     <= cfg_hammer_en;
                        r_idx1_shift    <= cfg_idx1_shift;
                        r_addr_lfsr     <= cfg_addr_lfsr;
                        r_idx1_bit      <= cfg_idx1_bit;
                        r_gap_sweep     <= cfg_gap_sweep;
                        r_gap_phase     <= 3'd0;
                        r_data_mode     <= cfg_data_mode;
                        r_fill_pattern  <= cfg_fill_pattern;
                        r_hash_seed0    <= cfg_hash_seed0;
                        r_hash_seed1    <= cfg_hash_seed1;
                        r_hash_seed2    <= cfg_hash_seed2;
                        r_id_mode       <= cfg_id_mode;
                        r_id_counter    <= cfg_axi_id[7:0];
                        r_aw_req_count   <= '0;
                        r_aw_issued      <= '0;
                        r_w_req_count    <= '0;
                        r_w_bursts_done  <= '0;
                        r_b_received     <= '0;
                        r_w_beat_idx     <= 8'd0;
                        r_gap_left       <= '0;
                        o_expected_crc_valid <= 1'b0;
                        o_bresp_error        <= 1'b0;
                        r_state              <= (cfg_txn_count == '0) ? S_DONE : S_RUN;
                    end
                end

                default: r_state <= S_IDLE;
            endcase

            // B-response accounting (independent of FSM phase, except we
            // never accept B while in IDLE pre-start).
            if (fub_bvalid && fub_bready) begin
                r_b_received <= r_b_received + 1'b1;
                if (fub_bresp != 2'b00) begin
                    o_bresp_error <= 1'b1;
                end
            end

            // Latch the expected CRC two cycles AFTER the last W beat of the
            // last burst: dataint_crc's accumulator absorbs the final beat one
            // cycle after the strobe, and its conditioned `crc` OUTPUT register
            // lags one more. A same-cycle capture misses the whole final beat
            // (a 1-beat run would latch the bare init constant). Only
            // meaningful in LFSR mode; hash mode uses per-beat compare
            // (o_data_error on the read side) as the integrity contract.
            r_crc_capture_pending <= {r_crc_capture_pending[0], 1'b0};
            if (r_crc_capture_pending[1]) begin
                o_expected_crc        <= w_expected_crc;
                o_expected_crc_valid  <= 1'b1;
            end
            if (r_state == S_RUN && w_w_beat && w_gen_wlast
                && r_w_bursts_done + 1'b1 == r_txn_count
                && r_data_mode == 2'd0) begin
                r_crc_capture_pending <= 2'b01;
            end
        end
    end)

    // Pulse on any cfg_start that initiates a run — IDLE→RUN OR the
    // S_DONE direct re-arm.
    assign w_lfsr_load = cfg_start && ((r_state == S_IDLE) || (r_state == S_DONE));

    // cfg_done: all txn_count B's received AND we're past the active run.
    assign cfg_done = (r_state == S_DONE)
                   && (r_b_received == r_txn_count);

    //==========================================================================
    // axi4_master_wr — bundles the AW/W/B skid buffers + protocol.
    // The FUB side is the pattern-gen handshake; the M side goes out to the
    // controller / fabric.
    //==========================================================================
    axi4_master_wr #(
        .SKID_DEPTH_AW (SKID_DEPTH_AW),
        .SKID_DEPTH_W  (SKID_DEPTH_W),
        .SKID_DEPTH_B  (SKID_DEPTH_B),
        .AXI_ID_WIDTH  (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
        .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH(AXI_WSTRB_WIDTH)
    ) u_master_wr (
        .aclk            (aclk),
        .aresetn         (aresetn),

        // FUB AW
        .fub_axi_awid    (w_aw_id_out),
        .fub_axi_awaddr  (w_aw_addr_result),
        .fub_axi_awlen   (r_burst_len - 8'd1),
        .fub_axi_awsize  (r_axi_size),
        .fub_axi_awburst (r_axi_burst),
        .fub_axi_awlock  (1'b0),
        .fub_axi_awcache (4'b0011),
        .fub_axi_awprot  (3'b000),
        .fub_axi_awqos   (4'b0000),
        .fub_axi_awregion(4'b0000),
        .fub_axi_awuser  ('0),
        .fub_axi_awvalid (fub_awvalid),
        .fub_axi_awready (fub_awready),

        // FUB W
        .fub_axi_wdata   (w_wdata_out),
        .fub_axi_wstrb   (w_wstrb_out),  // lanes of the beat (all for a full-width beat)
        .fub_axi_wlast   (fub_wlast),
        .fub_axi_wuser   ('0),
        .fub_axi_wvalid  (fub_wvalid),
        .fub_axi_wready  (fub_wready),

        // FUB B
        .fub_axi_bid     (),
        .fub_axi_bresp   (fub_bresp),
        .fub_axi_buser   (),
        .fub_axi_bvalid  (fub_bvalid),
        .fub_axi_bready  (fub_bready),

        // M-side AXI — passthrough to outer ports
        .m_axi_awid      (m_axi_awid),
        .m_axi_awaddr    (m_axi_awaddr),
        .m_axi_awlen     (m_axi_awlen),
        .m_axi_awsize    (m_axi_awsize),
        .m_axi_awburst   (m_axi_awburst),
        .m_axi_awlock    (m_axi_awlock),
        .m_axi_awcache   (m_axi_awcache),
        .m_axi_awprot    (m_axi_awprot),
        .m_axi_awqos     (m_axi_awqos),
        .m_axi_awregion  (m_axi_awregion),
        .m_axi_awuser    (m_axi_awuser),
        .m_axi_awvalid   (m_axi_awvalid),
        .m_axi_awready   (m_axi_awready),
        .m_axi_wdata     (m_axi_wdata),
        .m_axi_wstrb     (m_axi_wstrb),
        .m_axi_wlast     (m_axi_wlast),
        .m_axi_wuser     (m_axi_wuser),
        .m_axi_wvalid    (m_axi_wvalid),
        .m_axi_wready    (m_axi_wready),
        .m_axi_bid       (m_axi_bid),
        .m_axi_bresp     (m_axi_bresp),
        .m_axi_buser     (m_axi_buser),
        .m_axi_bvalid    (m_axi_bvalid),
        .m_axi_bready    (m_axi_bready),
        .busy            ()
    );

endmodule : axi4_master_wr_injector

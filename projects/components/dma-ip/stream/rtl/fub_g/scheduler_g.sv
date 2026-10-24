// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: scheduler_g
// Purpose: STREAM scheduler sequenced by gatling firmware (stream-g, stream
//          TASK-020). Same ports as fub/scheduler.sv plus a sequencer
//          register window; the datapath is the same scheduler_core. The
//          window is the rapids-g one (rapids fub_g/scheduler_g.sv), word for
//          word and bit for bit, so one firmware image serves both.
//
// What the firmware does, through the window (rapids_seq_g serves every
// channel of a STREAM core from one gatling):
//   - the channel policy: take a descriptor, validate it, start it, finish
//     it, chain (next_ptr != 0 && !last) or go idle;
//   - the EXT run bases, pushed ahead into a 4-deep FIFO per direction
//     (the depth of stream_run_addr_gen's own FIFO).
// What stays hardware: everything at cycle rate (scheduler_core), including
// STREAM's read-ahead prefetch -- a chained legacy head the firmware has
// STAGEd is peeked by the read side and advanced in place by the write side
// exactly as under the FSM, the channel never leaving XFER_DATA; the beat
// totals (the descriptor's length, loaded from the skid head on the cycle
// it is taken -- the firmware only reads them); and two interlocks that are
// not policy -- a channel reset forces CH_IDLE and a fatal fault (engine /
// descriptor error, escalated timeout, or the serving hart halted) forces
// CH_ERROR, both in the same cycle the FSM scheduler would take them.
//
// Commands.  A CMD write names the next state.  An edge the table below does
// not allow is ignored and counted (CMD_ERR, sticky cmd_err in STATUS):
//   IDLE      -> FETCH_DESC  channel enabled and a descriptor at the skid
//                            head; the head is taken on the same edge
//   NEXT_DESC -> FETCH_DESC  a descriptor at the skid head; taken
//   FETCH     -> XFER_DATA   descriptor valid: a PENDING request, taken the
//                            next cycle (STREAM has no packet records to wait for)
//   XFER      -> COMPLETE    exec_complete
//   COMPLETE  -> IDLE | NEXT_DESC   NEXT_DESC at once; IDLE once every write
//                            has committed (write_complete), as the FSM holds
//   FETCH | XFER | COMPLETE | NEXT_DESC -> ERROR
// CH_ERROR is left only by a channel reset, as in the FSM scheduler.
//
// Register window (word index; reads combinational, the sequencer registers):
//   R 0  STATUS   [6:0] state  [7] attn  [8] desc at head  [9] channel enable
//                 [10] channel reset  [11] desc valid  [13:12] opcode (0: DATA)
//                 [14] last  [15] gen_irq  [16] chain (next_ptr != 0)
//                 [17] tile_bad (0)  [18] pkt_ok (1)  [19] exec_complete
//                 [20] start pending  [21] cmd_err  [22] EXT  [23] header only (0)
//                 [24] rd per-beat  [25] wr per-beat  [26] rd bases done
//                 [27] wr bases done  [28] armed  [29] staged  [30] gen need
//                 [31] declined
//   R 1-6  SRC_LO SRC_HI DST_LO DST_HI LENGTH (beats) NEXT_PTR
//   R 7-12 EXT chunk-1 words 0..5 (rd_stride_0, rd_stride_1,
//          {rd_wrap1, rd_wrap0, rd_inner}, wr_stride_0, wr_stride_1,
//          {wr_wrap1, wr_wrap0, wr_inner}), stream_pkg::descriptor_ext_t
//   R 13 FIFO     [2:0] rd bases queued  [6:4] wr bases queued
//                 [15:8] CMD_ERR count (saturating)  [16] firmware packet pending
//                 [17] write_complete  [18] rd_ahead (STREAM: the prefetch)
//   R 14 CFG      [15:0] BYTE_LANES  [19:16] OFF_W  [20] EN_READ (1)
//                 [21] EN_WRITE (1)  [22] USE_ROW_COL_MAJOR_ADDRESSING
//   R 15-18 the skid head: src low, dst low, length, descriptor [223:192]
//   R 19-20 the beat totals in use (read, write)
//   R 21 HEAD_SUM [0] head valid (and its next-address selector one the
//                 image runs)  [1] head last  [2] head next_ptr != 0
//                 [3] head open: a head not yet staged or declined, in a
//                 state where STAGE / DECLINE are legal
//   R 22 ALG      [7:0] the latched descriptor's next-address selector
//                 (chunk 0 [224:217], reserved bits in STREAM's legacy layout)
//   R 23 ALG_MAX  [7:0] seq_alg_max: the highest selector the firmware image
//                 runs. A descriptor with a selector above it, or a non-zero
//                 selector without TYPE=EXT, is invalid (STATUS [11] = 0).
//   W 0  CMD      [6:0] next state (0 = none)  [8] rd bases done
//                 [9] wr bases done  [10] STAGE the head  [11] ARM this
//                 descriptor  [12] its ARM_NEXT  [13] run bases set up
//                 [14] DECLINE the head  [15] STAGE_ARM: take the staged
//                 head armed  [16] its ARM_NEXT
//   W 1  FW_ERROR [31:0] high word of a firmware error packet (low word W 7)
//   W 7  FW_LO    [31:0] the low word, written first
//   W 8  FW_DEBUG [31:0] high word of a firmware debug packet. One packet
//                 buffered; a send while one waits is dropped and counted in CMD_ERR.
//   W 3  RD_BASE_LO  W 4 RD_BASE_HI    the HI write pushes {HI, LO}
//   W 5  WR_BASE_LO  W 6 WR_BASE_HI
// The bases FIFOs hold only while the channel is in FETCH_DESC or XFER_DATA;
// anywhere else (and on a channel reset) they are empty, so a stale base can
// never reach a later descriptor.  A push to a full FIFO is dropped and
// counted.
//
// attn (also the sequencer's per-slot event) is high when the firmware has
// something to do: IDLE with a descriptor (channel enabled), NEXT_DESC with
// a descriptor, FETCH_DESC not yet started, XFER_DATA complete or wanting
// bases or with an unjudged head, COMPLETE not armed.
//
// Documentation: projects/components/dma-ip/stream/docs/stream_mas (stream-g)
// Subsystem: stream fub_g
//
// Author: sean galloway
// Created: 2026-10-24

`timescale 1ns / 1ps

`include "stream_imports.svh"
`include "reset_defs.svh"

module scheduler_g #(
    parameter int CHANNEL_ID = 0,
    parameter bit GEN_MON = 1'b1,
    parameter int NUM_CHANNELS = 8,
    parameter int CHAN_WIDTH = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1,
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    // Monitor Bus Parameters
    parameter logic [15:0] MON_AGENT_ID = 16'h0040,  // STREAM Scheduler Agent ID
    parameter logic [7:0]  MON_UNIT_ID = 8'h01,      // Unit identifier
    parameter logic [8:0]  MON_CHANNEL_ID = 9'h000,  // Base channel ID
    parameter int DESC_WIDTH = 256,
    parameter int USE_ROW_COL_MAJOR_ADDRESSING = 1
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    // Configuration Interface
    input  logic                        cfg_channel_enable,     // Enable this channel
    input  logic                        cfg_channel_reset,      // Channel reset
    input  logic [31:0]                 cfg_sched_timeout_cycles, // Timeout threshold (cycles)
    input  logic [7:0]                  cfg_sched_timeout_limit,  // Consecutive-timeout windows before fatal escalation (0=never)
    input  logic                        cfg_sched_timeout_enable, // Enable timeout detection
    input  logic                        cfg_rd_prefetch_enable,   // read-ahead prefetch (see fub/scheduler.sv)

    // Sequencer port (rapids_seq_g): one word-addressed register window.
    // Reads are combinational here; the sequencer registers them.
    input  logic                        seq_wr_en,
    input  logic [4:0]                  seq_wr_addr,            // word index
    input  logic [31:0]                 seq_wr_data,
    input  logic [4:0]                  seq_rd_addr,            // word index
    output logic [31:0]                 seq_rd_data,
    output logic                        seq_attn,               // needs the firmware
    input  logic                        seq_fault,              // the serving hart halted: fatal
    input  logic [7:0]                  seq_alg_max,            // the firmware image's highest selector

    // Status Interface
    output logic                        scheduler_idle,         // Scheduler idle
    output logic [6:0]                  scheduler_state,        // Current state (for debug) - ONE-HOT

    // Descriptor Engine Interface
    input  logic                        descriptor_valid,
    output logic                        descriptor_ready,
    input  logic [DESC_WIDTH-1:0]       descriptor_packet,     // 256-bit STREAM descriptor (chunk 0)
    input  logic [255:0]                descriptor_ext_packet, // Extended chunk 1 (ignored unless desc_type=EXT)
    input  logic                        descriptor_error,      // Error signal FROM descriptor engine

    // Data Read Interface (to AXI Read Engine)
    output logic                        sched_rd_valid,         // Channel requests read
    output logic [ADDR_WIDTH-1:0]       sched_rd_addr,          // Source address (aligned)
    output logic [31:0]                 sched_rd_beats,         // Beats remaining to read

    // Data Write Interface (to AXI Write Engine)
    output logic                        sched_wr_valid,         // Channel requests write
    input  logic                        sched_wr_ready,         // Engine ready for channel (used for completion)
    output logic [ADDR_WIDTH-1:0]       sched_wr_addr,          // Destination address (aligned)
    output logic [31:0]                 sched_wr_beats,         // Beats remaining to write

    // Completion Interface (from Engines to Scheduler)
    input  logic                        sched_rd_done_strobe,   // Read burst completed (pulsed)
    input  logic [31:0]                 sched_rd_beats_done,    // Number of beats completed
    input  logic                        sched_wr_done_strobe,   // Write burst ISSUED - AW handshake (pulsed)
    input  logic [31:0]                 sched_wr_beats_done,    // Number of beats issued this pulse
    input  logic                        sched_wr_commit_strobe, // Write burst COMMITTED - B response (pulsed)
    input  logic [31:0]                 sched_wr_commit_beats,  // Number of beats committed this pulse

    // Error Signals (from Engines to Scheduler)
    input  logic                        sched_rd_error,         // Read engine error
    input  logic                        sched_wr_error,         // Write engine error
    output logic                        sched_error,            // Scheduler error output (sticky)

    // Sticky/latched error visibility (OBS)
    output logic                        dbg_descriptor_error,
    output logic                        dbg_read_error_sticky,
    output logic                        dbg_write_error_sticky,
    output logic                        dbg_timeout_expired,

    // Free-running monitor-time broadcast (sampled on packet emit)
    input  ocelus_common_pkg::monbus_timestamp_t   i_mon_time,

    // Monitor Bus Interface (128-bit packet + 64-bit side-band timestamp)
    output logic                                    mon_valid,
    input  logic                                    mon_ready,
    output ocelus_common_pkg::monitor_packet_t     mon_packet,
    output ocelus_common_pkg::monbus_timestamp_t   mon_timestamp
);

    localparam int BASE_DEPTH = 4;
    localparam int BYTE_LANES = DATA_WIDTH / 8;
    localparam int OFF_W      = (BYTE_LANES > 1) ? $clog2(BYTE_LANES) : 1;
    // The next-address selector rides chunk 0 [224:217] (rapids TASK-035);
    // reserved bits in STREAM's legacy layout, so a plain descriptor reads 0.
    localparam int DESC_ALG_LO  = 217;
    localparam int DESC_ALG_HI  = 224;
    localparam int DESC_TYPE_LO = 208;
    localparam int DESC_TYPE_HI = 210;

    //=========================================================================
    // Datapath (shared with the FSM scheduler)
    //=========================================================================

    channel_state_t              r_state;
    descriptor_t                 w_desc;
    descriptor_ext_t             w_desc_ext;
    logic                        w_desc_head_valid, w_desc_is_ext;
    logic                        w_rd_per_beat, w_wr_per_beat;
    logic                        w_wr_advance, w_rd_ahead, w_exec_complete, w_write_complete;
    logic                        w_hard_error, w_timeout_escalate, w_channel_reset_active;
    logic                        w_desc_take;
    logic                        w_launch;           // FETCH_DESC -> XFER_DATA this cycle
    logic [31:0]                 r_rd_beats_total, r_wr_beats_total;
    logic                        w_rd_base_valid, w_rd_base_ready, w_wr_base_valid, w_wr_base_ready;
    logic [ADDR_WIDTH-1:0]       w_rd_base_addr, w_wr_base_addr;
    logic                        r_start_pending;
    logic [255:0]                w_head_pkt;         // the skid head, before it is taken
    logic [7:0]                  w_desc_alg;         // the latched next-address selector
    logic                        w_head_alg_ok;      // the head's selector is one the firmware runs

    // Pre-validation (as rapids-g, owner 2026-10-21): while a descriptor
    // transfers, the firmware validates the next one at the skid head and
    // stages it (STAGE), and decides this one's chain outcome (ARM). On
    // completion the hardware then takes the approved edges itself --
    // XFER -> COMPLETE -> IDLE/NEXT -> FETCH (the staged head) -> XFER -- in
    // the FSM's own cycles. On STREAM a staged legacy head is also what the
    // read-ahead prefetch may peek and advance to in place (head_ok).
    // STAGE_ARM stages the head with its own chain outcome, so it is taken
    // already armed: a chain then runs with one firmware write per
    // descriptor, made any time before its predecessor completes.
    logic                        r_armed, r_arm_next;    // this descriptor: complete on exec_complete, then IDLE / NEXT
    logic                        r_staged, r_declined;   // the head: validated and staged / refused
    logic                        r_stage_arm, r_stage_arm_next;  // the staged head: arm it on the take, and how
    logic                                   w_core_mon_valid;  // scheduler_core's MonBus, before the
    ocelus_common_pkg::monitor_packet_t     w_core_mon_packet; // firmware packets merge in
    ocelus_common_pkg::monbus_timestamp_t   w_core_mon_timestamp;
    logic                                   r_fw_valid;        // a firmware packet waiting
    logic                        r_gen_need;             // an EXT descriptor taken: its run bases are not set up yet
    logic                        r_rd_bases_done, r_wr_bases_done;   // the firmware has pushed every base

    scheduler_core #(
        .CHANNEL_ID                  (CHANNEL_ID),
        .GEN_MON                     (GEN_MON),
        .NUM_CHANNELS                (NUM_CHANNELS),
        .CHAN_WIDTH                  (CHAN_WIDTH),
        .ADDR_WIDTH                  (ADDR_WIDTH),
        .DATA_WIDTH                  (DATA_WIDTH),
        .MON_AGENT_ID                (MON_AGENT_ID),
        .MON_UNIT_ID                 (MON_UNIT_ID),
        .MON_CHANNEL_ID              (MON_CHANNEL_ID),
        .DESC_WIDTH                  (DESC_WIDTH),
        .USE_ROW_COL_MAJOR_ADDRESSING(USE_ROW_COL_MAJOR_ADDRESSING)
    ) u_core (
        .clk                     (clk),
        .rst_n                   (rst_n),
        .cfg_channel_enable      (cfg_channel_enable),
        .cfg_channel_reset       (cfg_channel_reset),
        .cfg_sched_timeout_cycles(cfg_sched_timeout_cycles),
        .cfg_sched_timeout_limit (cfg_sched_timeout_limit),
        .cfg_sched_timeout_enable(cfg_sched_timeout_enable),
        .cfg_rd_prefetch_enable  (cfg_rd_prefetch_enable),
        .scheduler_idle          (scheduler_idle),
        .descriptor_valid        (descriptor_valid),
        .descriptor_ready        (descriptor_ready),
        .descriptor_packet       (descriptor_packet),
        .descriptor_ext_packet   (descriptor_ext_packet),
        .descriptor_error        (descriptor_error),
        .sched_rd_valid          (sched_rd_valid),
        .sched_rd_addr           (sched_rd_addr),
        .sched_rd_beats          (sched_rd_beats),
        .sched_wr_valid          (sched_wr_valid),
        .sched_wr_ready          (sched_wr_ready),
        .sched_wr_addr           (sched_wr_addr),
        .sched_wr_beats          (sched_wr_beats),
        .sched_rd_done_strobe    (sched_rd_done_strobe),
        .sched_rd_beats_done     (sched_rd_beats_done),
        .sched_wr_done_strobe    (sched_wr_done_strobe),
        .sched_wr_beats_done     (sched_wr_beats_done),
        .sched_wr_commit_strobe  (sched_wr_commit_strobe),
        .sched_wr_commit_beats   (sched_wr_commit_beats),
        .sched_rd_error          (sched_rd_error),
        .sched_wr_error          (sched_wr_error),
        .sched_error             (sched_error),
        .dbg_descriptor_error    (dbg_descriptor_error),
        .dbg_read_error_sticky   (dbg_read_error_sticky),
        .dbg_write_error_sticky  (dbg_write_error_sticky),
        .dbg_timeout_expired     (dbg_timeout_expired),
        .i_mon_time              (i_mon_time),
        .mon_valid               (w_core_mon_valid),
        .mon_ready               (mon_ready),
        .mon_packet              (w_core_mon_packet),
        .mon_timestamp           (w_core_mon_timestamp),
        .state                   (r_state),
        .desc_take               (w_desc_take),
        .launch                  (w_launch),
        .desc_alg_max            (seq_alg_max),
        .rd_beats_total          (r_rd_beats_total),
        .wr_beats_total          (r_wr_beats_total),
        .head_ok                 (r_staged),              // the prefetch may take only a staged head
        .rd_base_valid           (w_rd_base_valid),
        .rd_base_addr            (w_rd_base_addr),
        .rd_base_ready           (w_rd_base_ready),
        .wr_base_valid           (w_wr_base_valid),
        .wr_base_addr            (w_wr_base_addr),
        .wr_base_ready           (w_wr_base_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .addrgen_start           (),                      // the firmware generates the bases
        /* verilator lint_on PINCONNECTEMPTY */
        .desc_head_valid         (w_desc_head_valid),
        .desc_head_packet        (w_head_pkt),
        .desc_latched            (w_desc),
        .desc_ext_latched        (w_desc_ext),
        .desc_is_ext             (w_desc_is_ext),
        .desc_alg                (w_desc_alg),
        .desc_rd_per_beat        (w_rd_per_beat),
        .desc_wr_per_beat        (w_wr_per_beat),
        .wr_advance              (w_wr_advance),
        .rd_ahead                (w_rd_ahead),
        .exec_complete           (w_exec_complete),
        .write_complete          (w_write_complete),
        .hard_error              (w_hard_error),
        .timeout_escalate        (w_timeout_escalate),
        .channel_reset_active    (w_channel_reset_active)
    );

    assign scheduler_state = r_state;

    //=========================================================================
    // Commands
    //=========================================================================

    wire w_in_idle     = (r_state == CH_IDLE);
    wire w_in_fetch    = (r_state == CH_FETCH_DESC);
    wire w_in_xfer     = (r_state == CH_XFER_DATA);
    wire w_in_complete = (r_state == CH_COMPLETE);
    wire w_in_next     = (r_state == CH_NEXT_DESC);
    wire w_in_error    = (r_state == CH_ERROR);
    wire w_active      = w_in_fetch || w_in_xfer;       // the bases FIFOs hold only here

    wire       w_cmd_wr  = seq_wr_en && (seq_wr_addr == 5'd0);
    wire [6:0] w_cmd_st  = seq_wr_data[6:0];
    wire       w_cmd_go  = w_cmd_wr && (w_cmd_st != 7'd0);
    // CMD flag bits beside the state: [10] STAGE the head, [11] ARM this
    // descriptor ([12] = 1: then NEXT_DESC, 0: IDLE), [13] run bases set up,
    // [14] DECLINE the head (the normal path will take and judge it)
    wire       w_cmd_stage   = w_cmd_wr && seq_wr_data[10];
    wire       w_cmd_arm     = w_cmd_wr && seq_wr_data[11];
    wire       w_cmd_gen_ok  = w_cmd_wr && seq_wr_data[13];
    wire       w_cmd_decline = w_cmd_wr && seq_wr_data[14];
    // [15] STAGE_ARM ([16] its ARM_NEXT): with STAGE, the head is armed when taken
    wire       w_cmd_stage_arm = w_cmd_wr && seq_wr_data[15];

    wire w_fault = w_hard_error || w_timeout_escalate || seq_fault;

    // The latched descriptor is valid only with a selector the image runs:
    // scheduler_core applies seq_alg_max as it latches (the FSM scheduler runs
    // selector 0 only; a non-zero selector is a firmware algorithm)
    wire   w_desc_valid  = w_desc.valid;

    logic w_cmd_legal;
    always_comb begin
        case (w_cmd_st)
            CH_FETCH_DESC: w_cmd_legal = w_desc_head_valid &&
                                         ((w_in_idle && cfg_channel_enable) || w_in_next);
            CH_XFER_DATA:  w_cmd_legal = w_in_fetch && !r_start_pending && w_desc_valid;
            CH_COMPLETE:   w_cmd_legal = w_in_xfer && w_exec_complete && !w_wr_advance;
            CH_IDLE,
            CH_NEXT_DESC:  w_cmd_legal = w_in_complete;
            CH_ERROR:      w_cmd_legal = w_in_fetch || w_in_xfer || w_in_complete || w_in_next;
            default:       w_cmd_legal = 1'b0;
        endcase
    end

    // Flags: ARM in XFER_DATA, once; STAGE / DECLINE while a descriptor is at
    // the head and not yet judged, before it is taken; run bases set up in
    // FETCH_DESC / XFER_DATA.
    wire w_head_open  = w_desc_head_valid && !r_staged && !r_declined &&
                        (w_in_xfer || w_in_complete || w_in_idle || w_in_next);
    wire w_flag_bad   = (w_cmd_arm && !(w_in_xfer && !r_armed)) ||
                        ((w_cmd_stage || w_cmd_decline) && !w_head_open) ||
                        (w_cmd_stage_arm && !w_cmd_stage) ||
                        (w_cmd_gen_ok && !w_active);
    wire w_live       = !w_channel_reset_active && !w_fault;

    // a COMPLETE command on the cycle of an in-place advance is simply too
    // late (the hardware moved on); it is dropped, not counted
    wire w_cmd_late = w_cmd_go && (w_cmd_st == CH_COMPLETE) && w_in_xfer && w_exec_complete && w_wr_advance;
    wire w_cmd_ok  = w_cmd_go && w_cmd_legal && w_live;
    wire w_cmd_bad = ((w_cmd_go && !w_cmd_legal && !w_cmd_late) || w_flag_bad) && w_live;

    // The automatic edges, in order: complete an armed descriptor, leave
    // COMPLETE the way it was armed, take a staged head.
    // An EXT descriptor completes automatically only once the firmware has
    // marked all its run bases out (it writes "done" after its last push).
    // Leaving COMPLETE for IDLE waits for every write to commit, as the FSM
    // does (the channel is not idle while data still lands); for NEXT_DESC
    // it is immediate, so a chain streams while commits drain.
    wire w_bases_out     = !w_desc_is_ext || (r_rd_bases_done && r_wr_bases_done);
    // The prefetch's in-place advance and the completion can be true in the
    // same cycle (the last writes issued, the reads done, a staged chained
    // head present): the advance wins, as it does in the FSM scheduler, and
    // the channel stays in XFER_DATA on the new descriptor. Taking COMPLETE
    // instead left that descriptor loaded and never issued (found by the
    // stream-g equivalence bench with the prefetch on).
    wire w_auto_complete = w_in_xfer && r_armed && w_exec_complete && w_bases_out && !w_wr_advance;
    wire w_auto_leave    = w_in_complete && r_armed && (r_arm_next || w_write_complete);
    wire w_auto_take     = r_staged && w_desc_head_valid &&
                           ((w_in_idle && cfg_channel_enable) || w_in_next);

    // The skid head is taken by the FETCH command or the automatic take, on
    // the edge the state leaves IDLE / NEXT_DESC (the core adds the prefetch's
    // in-place advance itself, and reports it on wr_advance).
    assign w_desc_take = (w_cmd_ok && (w_cmd_st == CH_FETCH_DESC)) ||
                         (w_live && !(w_in_fetch && r_start_pending) && w_auto_take);

    // FETCH_DESC -> XFER_DATA: the cycle after the start was requested, with a
    // valid descriptor (the FSM scheduler takes this edge on its own)
    wire w_start_go = w_in_fetch && r_start_pending && w_desc_valid;
    assign w_launch = w_live && w_start_go;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_state         <= CH_IDLE;
            r_start_pending <= 1'b0;
        end else if (w_channel_reset_active) begin
            r_state         <= CH_IDLE;          // interlock 1
            r_start_pending <= 1'b0;
        end else if (w_fault) begin
            r_state         <= CH_ERROR;         // interlock 2
            r_start_pending <= 1'b0;
        end else if (w_start_go) begin
            r_state         <= CH_XFER_DATA;
            r_start_pending <= 1'b0;
        end else if (w_auto_complete) begin
            r_state         <= CH_COMPLETE;
        end else if (w_auto_leave) begin
            r_state         <= r_arm_next ? CH_NEXT_DESC : CH_IDLE;
        end else if (w_auto_take) begin
            r_state         <= CH_FETCH_DESC;    // validated: start at once
            r_start_pending <= 1'b1;
        end else if (w_cmd_ok) begin
            if (w_cmd_st == CH_XFER_DATA) begin
                r_start_pending <= 1'b1;
            end else if (w_in_complete && (w_cmd_st == CH_IDLE) && !w_write_complete) begin
                r_state         <= r_state;      // IDLE waits for the commits: armed below
            end else begin
                r_state         <= channel_state_t'(w_cmd_st);
                r_start_pending <= 1'b0;
            end
        end
    )

    // Pre-validation state
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_armed          <= 1'b0;
            r_arm_next       <= 1'b0;
            r_staged         <= 1'b0;
            r_declined       <= 1'b0;
            r_gen_need       <= 1'b0;
            r_stage_arm      <= 1'b0;
            r_stage_arm_next <= 1'b0;
        end else if (!w_live) begin
            r_armed     <= 1'b0;
            r_staged    <= 1'b0;
            r_declined  <= 1'b0;
            r_gen_need  <= 1'b0;
            r_stage_arm <= 1'b0;
        end else begin
            if (w_cmd_arm && !w_flag_bad) begin
                r_armed    <= 1'b1;
                r_arm_next <= seq_wr_data[12];
            end else if (w_cmd_ok && w_in_complete && (w_cmd_st == CH_IDLE) && !w_write_complete) begin
                r_armed    <= 1'b1;              // leave for IDLE once the commits land
                r_arm_next <= 1'b0;
            end else if (w_auto_leave) begin
                r_armed    <= 1'b0;
            end
            if (w_desc_take || w_wr_advance) begin
                // the head is consumed: by the take (IDLE / NEXT_DESC) or by
                // the prefetch's in-place advance (XFER_DATA, a staged head)
                r_staged    <= 1'b0;
                r_declined  <= 1'b0;
                // a head staged with STAGE_ARM starts armed (only the
                // automatic take and the prefetch can find it staged)
                r_armed     <= r_staged && r_stage_arm;
                r_arm_next  <= r_stage_arm_next;
                r_stage_arm <= 1'b0;
                r_gen_need  <= 1'b1;             // read as EXT && gen_need
            end else begin
                if (w_cmd_stage && !w_flag_bad) begin
                    r_staged         <= 1'b1;
                    r_stage_arm      <= w_cmd_stage_arm;
                    r_stage_arm_next <= seq_wr_data[16];
                end
                if (w_cmd_decline && !w_flag_bad) r_declined <= 1'b1;
                if (w_cmd_gen_ok && !w_flag_bad)  r_gen_need <= 1'b0;
            end
        end
    )

    // Illegal commands and dropped pushes: sticky flag plus a saturating count
    logic       r_cmd_err;
    logic [7:0] r_cmd_err_cnt;
    logic       w_push_drop;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_cmd_err     <= 1'b0;
            r_cmd_err_cnt <= 8'h0;
        end else if (w_channel_reset_active) begin
            r_cmd_err     <= 1'b0;
            r_cmd_err_cnt <= 8'h0;
        end else if (w_cmd_bad || w_push_drop) begin
            r_cmd_err     <= 1'b1;
            if (!(&r_cmd_err_cnt)) r_cmd_err_cnt <= r_cmd_err_cnt + 8'h1;
        end
    )

    //=========================================================================
    // Beat totals (hardware) and the bases-done flags
    //=========================================================================
    // STREAM's length is in beats, so each direction moves the length: taken
    // from the skid head on the edge it is taken (by the FETCH command, the
    // automatic take, or the prefetch's in-place advance), so the totals are
    // in place when the latched descriptor is.
    localparam int H_LEN_LO = 128;

    logic [31:0] w_head_len;
    assign w_head_len = w_head_pkt[H_LEN_LO +: 32];

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_rd_beats_total <= 32'h0;
            r_wr_beats_total <= 32'h0;
            r_rd_bases_done  <= 1'b0;
            r_wr_bases_done  <= 1'b0;
        end else begin
            if (w_desc_take || w_wr_advance) begin
                r_rd_beats_total <= w_head_len;
                r_wr_beats_total <= w_head_len;
            end
            if (!w_active || w_channel_reset_active) begin
                r_rd_bases_done <= 1'b0;
                r_wr_bases_done <= 1'b0;
            end else if (w_cmd_wr) begin
                if (seq_wr_data[8]) r_rd_bases_done <= 1'b1;
                if (seq_wr_data[9]) r_wr_bases_done <= 1'b1;
            end
        end
    )

    //=========================================================================
    // EXT run-base FIFOs (firmware -> scheduler_core)
    //=========================================================================

    logic [2:0] w_rd_cnt, w_wr_cnt;
    logic       w_rd_drop, w_wr_drop;
    wire        w_flush = !w_active || w_channel_reset_active;

    scheduler_g_base_fifo #(.ADDR_WIDTH(ADDR_WIDTH), .DEPTH(BASE_DEPTH)) u_rd_bases (
        .clk       (clk),
        .rst_n     (rst_n),
        .flush     (w_flush),
        .lo_wr     (seq_wr_en && (seq_wr_addr == 5'd3)),
        .hi_wr     (seq_wr_en && (seq_wr_addr == 5'd4)),
        .wr_data   (seq_wr_data),
        .drop      (w_rd_drop),
        .count     (w_rd_cnt),
        .rd_valid  (w_rd_base_valid),
        .rd_ready  (w_rd_base_ready),
        .rd_addr   (w_rd_base_addr)
    );

    scheduler_g_base_fifo #(.ADDR_WIDTH(ADDR_WIDTH), .DEPTH(BASE_DEPTH)) u_wr_bases (
        .clk       (clk),
        .rst_n     (rst_n),
        .flush     (w_flush),
        .lo_wr     (seq_wr_en && (seq_wr_addr == 5'd5)),
        .hi_wr     (seq_wr_en && (seq_wr_addr == 5'd6)),
        .wr_data   (seq_wr_data),
        .drop      (w_wr_drop),
        .count     (w_wr_cnt),
        .rd_valid  (w_wr_base_valid),
        .rd_ready  (w_wr_base_ready),
        .rd_addr   (w_wr_base_addr)
    );

    //=========================================================================
    // Firmware packets (FW_DEBUG / FW_ERROR), merged onto the MonBus port
    //=========================================================================
    // scheduler_core's packets are one-cycle pulses and always win the cycle;
    // a firmware packet is offered on every other cycle and leaves on the
    // handshake. mon_valid never depends on mon_ready (the MonBus arbiter's
    // ready is combinational on valid; the rapids-g form made a loop here).

    ocelus_common_pkg::monitor_packet_t     r_fw_packet;
    ocelus_common_pkg::monbus_timestamp_t   r_fw_timestamp;
    logic [31:0]                            r_fw_lo;

    wire w_fw_err  = seq_wr_en && (seq_wr_addr == 5'd1);
    wire w_fw_dbg  = seq_wr_en && (seq_wr_addr == 5'd8);
    wire w_fw_out  = r_fw_valid && !w_core_mon_valid && mon_ready;
    wire w_fw_take = (w_fw_err || w_fw_dbg) && (!r_fw_valid || w_fw_out);
    wire w_fw_drop = (w_fw_err || w_fw_dbg) && !w_fw_take;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_fw_valid     <= 1'b0;
            r_fw_packet    <= '0;
            r_fw_timestamp <= '0;
            r_fw_lo        <= 32'h0;
        end else begin
            if (seq_wr_en && (seq_wr_addr == 5'd7)) r_fw_lo <= seq_wr_data;
            if (w_fw_take) begin
                r_fw_valid     <= 1'b1;
                r_fw_packet    <= ocelus_common_pkg::create_monitor_packet(
                                      w_fw_err ? ocelus_common_pkg::PktTypeError : ocelus_common_pkg::PktTypeDebug,
                                      ocelus_common_pkg::PROTOCOL_CORE,
                                      w_fw_err ? STREAM_EVENT_FW_ERROR : STREAM_EVENT_FW_DEBUG,
                                      MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID,
                                      {seq_wr_data, r_fw_lo});
                r_fw_timestamp <= i_mon_time;
            end else if (w_fw_out) begin
                r_fw_valid     <= 1'b0;
            end
        end
    )

    assign mon_valid     = GEN_MON ? (w_core_mon_valid || r_fw_valid) : 1'b0;
    assign mon_packet    = !GEN_MON ? '0 : (w_core_mon_valid ? w_core_mon_packet    : r_fw_packet);
    assign mon_timestamp = !GEN_MON ? '0 : (w_core_mon_valid ? w_core_mon_timestamp : r_fw_timestamp);

    assign w_push_drop = w_rd_drop || w_wr_drop || w_fw_drop;

    //=========================================================================
    // Attention and the read window
    //=========================================================================

    wire w_base_want = w_desc_is_ext &&
                       ((!r_rd_bases_done && (w_rd_cnt < 3'(BASE_DEPTH))) ||
                        (!r_wr_bases_done && (w_wr_cnt < 3'(BASE_DEPTH))));

    wire w_gen_need = r_gen_need && w_desc_is_ext;

    assign seq_attn = w_live &&
                      ((w_in_idle  && cfg_channel_enable && w_desc_head_valid && !r_staged) ||
                       (w_in_next  && w_desc_head_valid && !r_staged) ||
                       (w_in_fetch && !r_start_pending) ||
                       (w_in_xfer  && (!r_armed || w_gen_need || (w_base_want && !w_gen_need) ||
                                       (w_desc_head_valid && !r_staged && !r_declined))) ||
                       (w_in_complete && !r_armed));

    // The head's selector against the image's: the same test applied when
    // the descriptor is latched, so a head HEAD_SUM calls valid is one the
    // take will call valid.
    wire w_head_is_ext = (USE_ROW_COL_MAJOR_ADDRESSING != 0) &&
                         (desc_type_e'(w_head_pkt[DESC_TYPE_HI:DESC_TYPE_LO]) == DESC_TYPE_EXT);
    assign w_head_alg_ok = (w_head_pkt[DESC_ALG_HI:DESC_ALG_LO] == 8'd0) ||
                           (w_head_is_ext && (w_head_pkt[DESC_ALG_HI:DESC_ALG_LO] <= seq_alg_max));

    logic [31:0] w_status;
    assign w_status = {r_declined, w_gen_need, r_staged, r_armed,
                        r_wr_bases_done, r_rd_bases_done, w_wr_per_beat, w_rd_per_beat,
                        1'b0 /* header only */, w_desc_is_ext, r_cmd_err, r_start_pending,
                        w_exec_complete, 1'b1 /* pkt_ok */, 1'b0 /* tile_bad */,
                        (w_desc.next_descriptor_ptr != 32'h0),
                        w_desc.gen_irq, w_desc.last, 2'b00 /* opcode: DATA */, w_desc_valid,
                        w_channel_reset_active, cfg_channel_enable, w_desc_head_valid,
                        seq_attn, r_state};

    logic [255:0] w_ext_raw;
    assign w_ext_raw = w_desc_ext;

    always_comb begin
        case (seq_rd_addr)
            5'd0:    seq_rd_data = w_status;
            5'd1:    seq_rd_data = w_desc.src_addr[31:0];
            5'd2:    seq_rd_data = w_desc.src_addr[63:32];
            5'd3:    seq_rd_data = w_desc.dst_addr[31:0];
            5'd4:    seq_rd_data = w_desc.dst_addr[63:32];
            5'd5:    seq_rd_data = w_desc.length;
            5'd6:    seq_rd_data = w_desc.next_descriptor_ptr;
            5'd7:    seq_rd_data = w_ext_raw[ 31:  0];
            5'd8:    seq_rd_data = w_ext_raw[ 63: 32];
            5'd9:    seq_rd_data = w_ext_raw[ 95: 64];
            5'd10:   seq_rd_data = w_ext_raw[127: 96];
            5'd11:   seq_rd_data = w_ext_raw[159:128];
            5'd12:   seq_rd_data = w_ext_raw[191:160];
            5'd13:   seq_rd_data = {13'h0, w_rd_ahead, w_write_complete, r_fw_valid,
                                    r_cmd_err_cnt, 1'b0, w_wr_cnt, 1'b0, w_rd_cnt};
            5'd14:   seq_rd_data = {8'h0, 1'b0 /* TILE_HDR */, (USE_ROW_COL_MAJOR_ADDRESSING != 0),
                                    1'b1 /* EN_WRITE */, 1'b1 /* EN_READ */,
                                    4'(OFF_W), 16'(BYTE_LANES)};
            5'd15:   seq_rd_data = w_head_pkt[ 31:  0];    // the head: src low word
            5'd16:   seq_rd_data = w_head_pkt[ 95: 64];    // dst low word
            5'd17:   seq_rd_data = w_head_pkt[159:128];    // length (beats)
            5'd18:   seq_rd_data = w_head_pkt[223:192];    // valid, gen_irq, last, ..., type
            5'd19:   seq_rd_data = r_rd_beats_total;       // the beat totals in use
            5'd20:   seq_rd_data = r_wr_beats_total;
            5'd21:   seq_rd_data = {28'h0, w_head_open,                                       // HEAD_SUM: open,
                                    (w_head_pkt[191:160] != 32'h0),                       // chain,
                                    w_head_pkt[194], w_head_pkt[192] && w_head_alg_ok};   // last, valid
            5'd22:   seq_rd_data = {24'h0, w_desc_alg};    // the latched next-address selector
            5'd23:   seq_rd_data = {24'h0, seq_alg_max};   // the highest selector this image runs
            default: seq_rd_data = 32'h0;
        endcase
    end

endmodule : scheduler_g

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: chi_monitor_lite
// Purpose: the CHI (Arm IHI 0050) ocelus in the lite discipline (amba TASK-050)
//
// Documentation: docs/markdown/rtl-amba/monitor/chi_monitor_lite.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-10-30
//
// ============================================================================
// A CHI port is a pair of credited links carrying transactions: a request
// is answered by a completion and read data, a write is pulled by a DBID
// and sends write data, a CompAck closes it, and the home can snoop the
// requester at any time. cxs_monitor_lite (credits and packets) and
// axi_monitor_lite (commands and responses) each fit half of that; this
// block watches what a CHI port does and emits it as Error / Timeout /
// Completion plus the stream classes Credit / Channel / Stream, tagged
// PROTOCOL_CHI with the ocelus_chi_pkg event codes. The delivery contract
// is the lite one, unchanged: events decided and REGISTERED, up to two
// queued per cycle, a 4-deep unreset output queue, drop-and-count with the
// count reported as Error/EVENT_DROPPED into an empty queue, microsecond
// timeouts, `clear`.
//
// What it taps (all inputs; it drives nothing). The owner rule for monitors
// -- tap the FUB side, never the external link pins, for timing -- holds:
//   - the port's six FUB handshakes, presented by MESSAGE DIRECTION rather
//     than by pin so one block serves an RN-F port and an HN-F port: req
//     (requester -> completer), cpl_rsp / cpl_dat (toward the requester),
//     rq_rsp / rq_dat (from the requester: CompAck, write data, snoop
//     responses), snp (toward the requester). The wrapper maps fub_tx* and
//     fub_rx* onto these; IS_REQUESTER says which three are the port's
//     receive channels, for backpressure;
//   - the port's REGISTERED status (tx_link_state, rx_link_state,
//     credit_starved, protocol_error). None of those is a raw pin.
//
// Why it is small (the axi_monitor_lite recipe): one allocation port (the
// request handshake), a table of MAX_TRANSACTIONS slots holding stamps not
// counters, the TxnID of the request and the DBID the completer handed
// out; a RSP or DAT toward the requester finds its slot by TxnID, a
// CompAck or write data from the requester by DBID (TxnID == DBID, B2.4.3),
// each a one-hot compare over the slots; a slot's remaining data packets
// are a 3-bit decrement; a slot retires when nothing is owed and ONE
// retire is picked per cycle (a slot waits, so nothing is lost); timeouts
// are a one-slot-per-cycle scan. Snoops get their own MAX_SNOOPS table
// keyed by the snoop's TxnID. The events of a cycle are registered before
// the packet pick. No per-slot state machine, no CAM ports, no scan of the
// whole table for a match.
//
// What is owed per request (B2.3, B2.7.3): a completion (Comp, CompDBIDResp,
// RespSepData, CompPersist, CompStashDone, or the last CompData; a RetryAck
// retires the slot instead); for a write, atomic or DVMOp opcode, a DBID
// response, then data_packets(Size) packets of write data (none for the Zero
// writes; WriteDataCancel forgives them; a CopyBack answered by a plain Comp
// owes no data but a CompAck); for a read opcode, data_packets(Size) packets
// of CompData or DataSepResp; a CompAck when the request set ExpCompAck.
// PrefetchTgt is not tracked (no response). A TxnID is matched only while a
// TxnID-addressed response is still owed, so the requester may reuse it as
// B2.5 allows while write data or a CompAck is still outstanding. Everything
// else in a flit is payload this block does not read. Not modelled: MultiReq,
// stash DataPull (CompData keyed by a snoop DBID), and snoops from more than
// one home to the same port (snoop slots are keyed by TxnID alone).
//
// Events (priority when several fire in one cycle, highest first):
//   Error/PROTOCOL          protocol_error rose (the port's sticky flag)
//   Error/RESP_ERR          a completion or read data carried DERR / NDERR
//   Error/ORPHAN_RSP, ORPHAN_DAT, ORPHAN_ACK, ORPHAN_SNP_RSP
//   Error/TABLE_FULL, SNP_TABLE_FULL
//   Timeout/TXN, SNP        a slot older than cfg_timeout_cnt us (once per slot)
//   Timeout/CREDIT, LINK    as the CXS lite
//   Completion/TXN, RETRY, SNP
//   Credit/STARVED, BACKPRESSURE
//   Channel/PCRD_GRANT, PCRD_RETURN, READ_RECEIPT
//   Stream/TX_*, RX_*       a direction entered ACTIVATE, RUN, DEACTIVATE, STOP
// ============================================================================
`timescale 1ns / 1ps
`include "reset_defs.svh"

module chi_monitor_lite
    import ocelus_common_pkg::*;
    import ocelus_chi_pkg::*;
    import chi_pkg::*;
#(
    parameter logic [7:0]  UNIT_ID          = 8'h0B,
    parameter logic [15:0] AGENT_ID         = 16'h00D0,
    parameter bit          IS_REQUESTER     = 1'b1,  // 1: an RN-F port (req is its TX); 0: an HN-F port
    // The interface the tapped port was built with (sizes the flits and the field offsets)
    parameter int          NODEID_WIDTH     = 7,
    parameter int          ADDR_WIDTH       = 44,
    parameter int          DATA_WIDTH       = 128,
    parameter int          MECID_WIDTH      = 0,
    parameter int          REQ_W            = 137,
    parameter int          RSP_W            = 71,
    parameter int          SNP_W            = 94,
    parameter int          DAT_W            = 240,
    parameter int          MAX_TRANSACTIONS = 8,     // request slots
    parameter int          MAX_SNOOPS       = 4,     // snoop slots
    parameter int          TS_WIDTH         = 16,    // cycle stamp: latency
    parameter int          AGE_WIDTH        = 16,    // microsecond age: timeout (cfg is 16 bits)
    parameter int          OUT_DEPTH        = 4,     // output queue entries, two interleaved gaxi_fifo_sync banks, any depth >= 1
    parameter int          CFI_MIN_FREQ_MHZ     = 5,
    parameter int          CFI_MAX_FREQ_MHZ     = 220,
    parameter int          CFI_NUM_FREQ_ENTRIES = 16,
    parameter int          CFI_FREQ_STRATEGY    = 0,
    // Short params (do not override)
    parameter int          N    = MAX_TRANSACTIONS,
    parameter int          M    = MAX_SNOOPS,
    parameter int          SW   = (N > 1) ? $clog2(N) : 1,
    parameter int          MW   = (M > 1) ? $clog2(M) : 1,
    parameter int          CW   = $clog2(N + 1),
    parameter int          SELW = (CFI_NUM_FREQ_ENTRIES > 1) ? $clog2(CFI_NUM_FREQ_ENTRIES) : 1
) (
    input  logic                  aclk,
    input  logic                  aresetn,
    input  logic                  clear,          // synchronous: forget every slot and episode, zero the counters. Legal only while idle

    input  monbus_timestamp_t     i_mon_time,

    // The FUB handshakes, tapped, by message direction
    input  logic                  req_valid,      // requests, requester -> completer
    input  logic                  req_ready,
    input  logic [REQ_W-1:0]      req_flit,
    input  logic                  cpl_rsp_valid,  // responses toward the requester
    input  logic                  cpl_rsp_ready,
    input  logic [RSP_W-1:0]      cpl_rsp_flit,
    input  logic                  cpl_dat_valid,  // read data toward the requester
    input  logic                  cpl_dat_ready,
    input  logic [DAT_W-1:0]      cpl_dat_flit,
    input  logic                  rq_rsp_valid,   // CompAck / snoop responses from the requester
    input  logic                  rq_rsp_ready,
    input  logic [RSP_W-1:0]      rq_rsp_flit,
    input  logic                  rq_dat_valid,   // write data / snoop data from the requester
    input  logic                  rq_dat_ready,
    input  logic [DAT_W-1:0]      rq_dat_flit,
    input  logic                  snp_valid,      // snoops toward the requester
    input  logic                  snp_ready,
    input  logic [SNP_W-1:0]      snp_flit,

    // The port's registered status
    input  logic [1:0]            tx_link_state,  // {REQ, ACK}: 00 STOP 10 ACTIVATE 11 RUN 01 DEACTIVATE
    input  logic [1:0]            rx_link_state,
    input  logic                  credit_starved,
    input  logic                  protocol_error, // sticky

    // Configuration (cfg_timeout_cnt in MICROSECONDS, 16'hFFFF = never)
    input  logic [SELW-1:0]       cfg_freq_sel,
    input  logic [15:0]           cfg_timeout_cnt,
    input  logic                  cfg_error_enable,
    input  logic                  cfg_timeout_enable,
    input  logic                  cfg_compl_enable,
    input  logic                  cfg_credit_enable,
    input  logic                  cfg_channel_enable,
    input  logic                  cfg_stream_enable,
    input  logic [31:0]           cfg_stall_threshold,   // CYCLES; 0 = Credit events off
    input  logic [15:0]           cfg_chi_pkt_mask,      // bit[type] = 1 drops that packet type

    // Ocelus bus
    output logic                  monbus_valid,
    input  logic                  monbus_ready,
    output monitor_packet_t       monbus_packet,
    output monbus_timestamp_t     monbus_timestamp,

    // Status
    output logic                  busy,
    output logic [CW-1:0]         active_count,   // request slots in use
    output logic [31:0]           txn_count,      // requests retired (Completion/TXN + RETRY)
    output logic [31:0]           snoop_count,    // snoops answered
    output logic [15:0]           error_count,    // error packets emitted (drop reports excluded)
    output logic [15:0]           dropped_count   // events lost since the last report
);

    // ------------------------------------------------------------------
    // Field offsets for the tapped interface (chi_pkg, Tables B13.6-B13.9)
    // ------------------------------------------------------------------
    localparam int REQ_TXNID_LSB = req_txnid_lsb(NODEID_WIDTH);
    localparam int REQ_OPC_LSB   = req_opcode_lsb(NODEID_WIDTH);
    localparam int REQ_SIZE_LSB  = req_size_lsb(NODEID_WIDTH);
    localparam int REQ_ECA_LSB   = req_expcompack_lsb(NODEID_WIDTH, ADDR_WIDTH);
    localparam int RSP_TXNID_LSB = rsp_txnid_lsb(NODEID_WIDTH);
    localparam int RSP_OPC_LSB   = rsp_opcode_lsb(NODEID_WIDTH);
    localparam int RSP_RERR_LSB  = rsp_resperr_lsb(NODEID_WIDTH);
    localparam int RSP_DBID_LSB  = rsp_dbid_lsb(NODEID_WIDTH);
    localparam int RSP_PCRD_LSB  = rsp_pcrdtype_lsb(NODEID_WIDTH);
    localparam int DAT_TXNID_LSB = dat_txnid_lsb(NODEID_WIDTH);
    localparam int DAT_OPC_LSB   = dat_opcode_lsb(NODEID_WIDTH);
    localparam int DAT_RERR_LSB  = dat_resperr_lsb(NODEID_WIDTH);
    localparam int DAT_DBID_LSB  = dat_dbid_lsb(NODEID_WIDTH, MECID_WIDTH);
    localparam int SNP_TXNID_LSB = snp_txnid_lsb(NODEID_WIDTH);
    localparam int TW            = CHI_TXNID_W;
    localparam int LINE_PKTS     = data_packets(6, DATA_WIDTH);   // a 64-byte line

    // ------------------------------------------------------------------
    // The tap, this cycle
    // ------------------------------------------------------------------
    wire w_req  = req_valid     && req_ready;
    wire w_crsp = cpl_rsp_valid && cpl_rsp_ready;
    wire w_cdat = cpl_dat_valid && cpl_dat_ready;
    wire w_qrsp = rq_rsp_valid  && rq_rsp_ready;
    wire w_qdat = rq_dat_valid  && rq_dat_ready;
    wire w_snp  = snp_valid     && snp_ready;

    wire [6:0]    w_req_opc    = req_flit[REQ_OPC_LSB +: 7];
    wire [TW-1:0] w_req_txnid  = req_flit[REQ_TXNID_LSB +: TW];
    wire [2:0]    w_req_size   = req_flit[REQ_SIZE_LSB +: 3];
    wire          w_req_eca    = req_flit[REQ_ECA_LSB];
    wire [3:0]    w_req_pkts4  = 4'(data_packets(int'(w_req_size), DATA_WIDTH));
    wire [2:0]    w_req_pkts   = w_req_pkts4[3] ? 3'd7 : w_req_pkts4[2:0];   // Size 7 is reserved; clamp rather than wrap
    wire [4:0]    w_crsp_opc   = cpl_rsp_flit[RSP_OPC_LSB +: 5];
    wire [TW-1:0] w_crsp_txnid = cpl_rsp_flit[RSP_TXNID_LSB +: TW];
    wire [1:0]    w_crsp_rerr  = cpl_rsp_flit[RSP_RERR_LSB +: 2];
    wire [TW-1:0] w_crsp_dbid  = cpl_rsp_flit[RSP_DBID_LSB +: TW];
    wire [3:0]    w_crsp_pcrd  = cpl_rsp_flit[RSP_PCRD_LSB +: 4];
    wire [3:0]    w_cdat_opc   = cpl_dat_flit[DAT_OPC_LSB +: 4];
    wire [TW-1:0] w_cdat_txnid = cpl_dat_flit[DAT_TXNID_LSB +: TW];
    wire [1:0]    w_cdat_rerr  = cpl_dat_flit[DAT_RERR_LSB +: 2];
    wire [TW-1:0] w_cdat_dbid  = cpl_dat_flit[DAT_DBID_LSB +: TW];
    wire [4:0]    w_qrsp_opc   = rq_rsp_flit[RSP_OPC_LSB +: 5];
    wire [TW-1:0] w_qrsp_txnid = rq_rsp_flit[RSP_TXNID_LSB +: TW];
    wire [3:0]    w_qdat_opc   = rq_dat_flit[DAT_OPC_LSB +: 4];
    wire [TW-1:0] w_qdat_txnid = rq_dat_flit[DAT_TXNID_LSB +: TW];
    wire [TW-1:0] w_snp_txnid  = snp_flit[SNP_TXNID_LSB +: TW];

    // Message classes
    wire w_req_alloc    = w_req && (w_req_opc != 7'h00) && (w_req_opc != CHI_REQ_PCRD_RETURN) &&
                                   (w_req_opc != CHI_REQ_PREFETCH_TGT);                    // PrefetchTgt gets no response
    wire w_req_pcrdret  = w_req && (w_req_opc == CHI_REQ_PCRD_RETURN);
    wire w_crsp_comp    = w_crsp && ((w_crsp_opc == CHI_RSP_COMP) || (w_crsp_opc == CHI_RSP_COMP_DBID_RESP) ||
                                     (w_crsp_opc == CHI_RSP_RESP_SEP_DATA) || (w_crsp_opc == CHI_RSP_COMP_PERSIST) ||
                                     (w_crsp_opc == CHI_RSP_COMP_STASH_DONE));
    wire w_crsp_plain   = w_crsp && (w_crsp_opc == CHI_RSP_COMP);
    wire w_crsp_is_dbid = w_crsp && ((w_crsp_opc == CHI_RSP_COMP_DBID_RESP) || (w_crsp_opc == CHI_RSP_DBID_RESP) ||
                                     (w_crsp_opc == CHI_RSP_DBID_RESP_ORD));
    wire w_crsp_retry   = w_crsp && (w_crsp_opc == CHI_RSP_RETRY_ACK);
    wire w_crsp_is_pcrd = w_crsp && (w_crsp_opc == CHI_RSP_PCRD_GRANT);
    wire w_crsp_receipt = w_crsp && (w_crsp_opc == CHI_RSP_READ_RECEIPT);
    // Addressed to a slot by TxnID and expected: an unmatched one is an orphan. ReadReceipt, Persist, StashDone,
    // TagMatch and CompCMO are NOT in the set: they carry no debt the table tracks and may land after the retire.
    wire w_crsp_txn     = w_crsp_comp || w_crsp_is_dbid || w_crsp_retry;
    wire w_cdat_read    = w_cdat && ((w_cdat_opc == CHI_DAT_COMP_DATA) || (w_cdat_opc == CHI_DAT_DATA_SEP_RESP));
    wire w_qrsp_ack     = w_qrsp && (w_qrsp_opc == CHI_RSP_COMP_ACK);
    wire w_qrsp_snp     = w_qrsp && ((w_qrsp_opc == CHI_RSP_SNP_RESP) || (w_qrsp_opc == CHI_RSP_SNP_RESP_FWDED));
    wire w_qdat_wr      = w_qdat && ((w_qdat_opc == CHI_DAT_NONCOPYBACK_WDATA) || (w_qdat_opc == CHI_DAT_COPYBACK_WDATA) ||
                                     (w_qdat_opc == CHI_DAT_NONCOPYBACK_WDATA_COMP_ACK) || (w_qdat_opc == CHI_DAT_WRITE_DATA_CANCEL));
    wire w_qdat_wr_ack  = w_qdat && (w_qdat_opc == CHI_DAT_NONCOPYBACK_WDATA_COMP_ACK);
    wire w_qdat_cancel  = w_qdat && (w_qdat_opc == CHI_DAT_WRITE_DATA_CANCEL);
    wire w_qdat_snp     = w_qdat && ((w_qdat_opc == CHI_DAT_SNP_RESP_DATA) || (w_qdat_opc == CHI_DAT_SNP_RESP_DATA_PTL) ||
                                     (w_qdat_opc == CHI_DAT_SNP_RESP_DATA_FWDED));

    // The port's receive channels, for backpressure (FUB valid without ready)
    wire w_bp = IS_REQUESTER ? ((cpl_rsp_valid && !cpl_rsp_ready) || (cpl_dat_valid && !cpl_dat_ready) ||
                                (snp_valid && !snp_ready))
                             : ((req_valid && !req_ready) || (rq_rsp_valid && !rq_rsp_ready) ||
                                (rq_dat_valid && !rq_dat_ready));

    // ------------------------------------------------------------------
    // Time
    // ------------------------------------------------------------------
    logic [AGE_WIDTH-1:0] r_us;
    logic [TS_WIDTH-1:0]  r_cyc;
    logic                 w_tick;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_us  <= '0;
            r_cyc <= '0;
        end else begin
            r_cyc <= r_cyc + 1'b1;
            if (w_tick) r_us <= r_us + 1'b1;
        end
    )

    counter_freq_invariant #(
        .COUNTER_WIDTH    (1),
        .MIN_FREQ_MHZ     (CFI_MIN_FREQ_MHZ),
        .MAX_FREQ_MHZ     (CFI_MAX_FREQ_MHZ),
        .NUM_FREQ_ENTRIES (CFI_NUM_FREQ_ENTRIES),
        .FREQ_STRATEGY    (CFI_FREQ_STRATEGY)
    ) u_tick (
        .clk          (aclk),
        .rst_n        (aresetn),
        .sync_reset_n (1'b1),
        .freq_sel     (cfg_freq_sel),
        .tick         (w_tick),
        /* verilator lint_off PINCONNECTEMPTY */
        .o_counter    ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // ------------------------------------------------------------------
    // Request table
    // ------------------------------------------------------------------
    logic [N-1:0]         r_valid;
    logic [TW-1:0]        r_txnid    [N];
    logic [TW-1:0]        r_dbid     [N];
    logic [N-1:0]         r_dbid_ok;             // r_dbid holds the completer's DBID
    logic [6:0]           r_opcode   [N];
    logic [N-1:0]         r_need_comp;
    logic [N-1:0]         r_need_dbid;           // a DBID response is owed (writes, atomics, DVMOp)
    logic [N-1:0]         r_need_ack;
    logic [2:0]           r_pkts     [N];        // data packets the request's Size names
    logic [2:0]           r_dat_rem  [N];        // read data packets still owed
    logic [2:0]           r_wdat_rem [N];        // write data packets still owed (set by the DBID response)
    logic [AGE_WIDTH-1:0] r_us_stamp [N];
    logic [TS_WIDTH-1:0]  r_cyc_stamp[N];
    logic [N-1:0]         r_tmo;                 // timeout reported for this slot

    // free slot (lowest index)
    logic          w_free;
    logic [SW-1:0] w_free_idx;
    always_comb begin
        w_free     = 1'b0;
        w_free_idx = '0;
        for (int i = N - 1; i >= 0; i--) begin
            if (!r_valid[i]) begin
                w_free     = 1'b1;
                w_free_idx = SW'(i);
            end
        end
    end

    // matches: TxnID for messages toward the requester, DBID for messages from it.
    // A TxnID is the requester's to reuse once every TxnID-addressed response is in (B2.4.2, B2.5), even while
    // the write data or CompAck that the DBID names is still owed; so a slot that owes only DBID-keyed debts
    // is invisible to the TxnID compare, and a reused TxnID lands on the new slot.
    logic [N-1:0] w_txn_open, w_m_crsp, w_m_cdat, w_m_qrsp, w_m_qdat;
    always_comb begin
        for (int i = 0; i < N; i++) begin
            w_txn_open[i] = r_valid[i] && (r_need_comp[i] || r_need_dbid[i] || (r_dat_rem[i] != 3'd0));
            w_m_crsp[i] = w_txn_open[i] && (r_txnid[i] == w_crsp_txnid);
            w_m_cdat[i] = w_txn_open[i] && (r_txnid[i] == w_cdat_txnid);
            w_m_qrsp[i] = r_valid[i] && r_dbid_ok[i] && (r_dbid[i] == w_qrsp_txnid);
            w_m_qdat[i] = r_valid[i] && r_dbid_ok[i] && (r_dbid[i] == w_qdat_txnid);
        end
    end
    wire w_hit_crsp = |w_m_crsp;
    wire w_hit_cdat = |w_m_cdat;
    wire w_hit_qrsp = |w_m_qrsp;
    wire w_hit_qdat = |w_m_qdat;

    function automatic logic [SW-1:0] onehot_idx(input logic [N-1:0] v);
        logic [SW-1:0] r;
        r = '0;
        for (int i = 0; i < N; i++) if (v[i]) r = SW'(i);
        return r;
    endfunction

    // the one retire per cycle: lowest slot that owes nothing
    logic [N-1:0] w_done;
    always_comb begin
        for (int i = 0; i < N; i++)
            w_done[i] = r_valid[i] && !r_need_comp[i] && !r_need_dbid[i] && !r_need_ack[i] &&
                        (r_dat_rem[i] == 3'd0) && (r_wdat_rem[i] == 3'd0);
    end
    logic          w_retire;
    logic [SW-1:0] w_retire_idx;
    always_comb begin
        w_retire     = 1'b0;
        w_retire_idx = '0;
        for (int i = N - 1; i >= 0; i--) begin
            if (w_done[i]) begin
                w_retire     = 1'b1;
                w_retire_idx = SW'(i);
            end
        end
    end
    // a RetryAck retires its slot in the same cycle, ahead of the normal pick
    wire           w_retry_hit = w_crsp_retry && w_hit_crsp;
    wire  [SW-1:0] w_retry_idx = onehot_idx(w_m_crsp);
    wire           w_retire_go = w_retire && !(w_retry_hit && (w_retry_idx == w_retire_idx));

    // slot-level timeout scan, one slot per cycle
    logic [SW-1:0] r_scan;
    wire w_never = (cfg_timeout_cnt == 16'hFFFF);
    // cfg_timeout_cnt is 16 bits; a narrower AGE_WIDTH saturates (never silently wraps to a small value)
    logic [AGE_WIDTH-1:0] w_tmo;
    if (AGE_WIDTH >= 16) begin : g_tmo_wide
        assign w_tmo = AGE_WIDTH'(cfg_timeout_cnt);
    end else begin : g_tmo_narrow
        assign w_tmo = (|cfg_timeout_cnt[15:AGE_WIDTH]) ? '1 : cfg_timeout_cnt[AGE_WIDTH-1:0];
    end
    wire [AGE_WIDTH-1:0] w_scan_age = r_us - r_us_stamp[r_scan];
    wire w_scan_hit = cfg_timeout_enable && !w_never && r_valid[r_scan] && !r_tmo[r_scan] && (w_scan_age >= w_tmo);

    logic [CW-1:0] w_occupancy;
    always_comb begin
        w_occupancy = '0;
        for (int i = 0; i < N; i++) w_occupancy = w_occupancy + CW'(r_valid[i]);
    end

    // ------------------------------------------------------------------
    // Snoop table
    // ------------------------------------------------------------------
    logic [M-1:0]         r_s_valid;
    logic [TW-1:0]        r_s_txnid  [M];
    logic [2:0]           r_s_rem    [M];        // snoop data packets still owed (0 after SnpResp)
    logic [AGE_WIDTH-1:0] r_s_us     [M];
    logic [TS_WIDTH-1:0]  r_s_cyc    [M];
    logic [M-1:0]         r_s_tmo;

    logic          w_s_free;
    logic [MW-1:0] w_s_free_idx;
    always_comb begin
        w_s_free     = 1'b0;
        w_s_free_idx = '0;
        for (int i = M - 1; i >= 0; i--) begin
            if (!r_s_valid[i]) begin
                w_s_free     = 1'b1;
                w_s_free_idx = MW'(i);
            end
        end
    end
    logic [M-1:0] w_sm_rsp, w_sm_dat;
    always_comb begin
        for (int i = 0; i < M; i++) begin
            w_sm_rsp[i] = r_s_valid[i] && (r_s_txnid[i] == w_qrsp_txnid);
            w_sm_dat[i] = r_s_valid[i] && (r_s_txnid[i] == w_qdat_txnid);
        end
    end
    function automatic logic [MW-1:0] s_onehot_idx(input logic [M-1:0] v);
        logic [MW-1:0] r;
        r = '0;
        for (int i = 0; i < M; i++) if (v[i]) r = MW'(i);
        return r;
    endfunction
    wire           w_s_hit_rsp = |w_sm_rsp;
    wire           w_s_hit_dat = |w_sm_dat;
    // SnpDVMOp is two flits with one TxnID and one SnpResp (B8.2.3.2): the second flit joins the open slot
    logic [M-1:0]  w_sm_new;
    always_comb begin
        for (int i = 0; i < M; i++) w_sm_new[i] = r_s_valid[i] && (r_s_txnid[i] == w_snp_txnid);
    end
    wire           w_s_dup   = |w_sm_new;
    wire           w_s_alloc = w_snp && !w_s_dup;
    wire  [MW-1:0] w_s_rsp_idx = s_onehot_idx(w_sm_rsp);
    wire  [MW-1:0] w_s_dat_idx = s_onehot_idx(w_sm_dat);
    // a snoop completes on SnpResp, or on the last of its data packets
    wire           w_s_done_rsp = w_qrsp_snp && w_s_hit_rsp;
    wire           w_s_done_dat = w_qdat_snp && w_s_hit_dat && (r_s_rem[w_s_dat_idx] <= 3'd1);
    wire           w_s_done     = w_s_done_rsp || w_s_done_dat;
    wire           w_s_done_two = w_s_done_rsp && w_s_done_dat && (w_s_rsp_idx != w_s_dat_idx);   // both retire; one packet
    wire  [MW-1:0] w_s_done_idx = w_s_done_rsp ? w_s_rsp_idx : w_s_dat_idx;

    logic [MW-1:0] r_s_scan;
    wire [AGE_WIDTH-1:0] w_s_scan_age = r_us - r_s_us[r_s_scan];
    wire w_s_scan_hit = cfg_timeout_enable && !w_never && r_s_valid[r_s_scan] && !r_s_tmo[r_s_scan] &&
                        (w_s_scan_age >= w_tmo);

    // ------------------------------------------------------------------
    // Episodes: links, credits, backpressure (the CXS lite's)
    // ------------------------------------------------------------------
    logic [1:0]           r_tx_link, r_rx_link;
    logic                 r_proto_q;
    logic [31:0]          r_starve_cycles, r_bp_cycles;
    logic [AGE_WIDTH-1:0] r_starve_stamp, r_tx_link_stamp, r_rx_link_stamp;
    logic                 r_tmo_credit_fired, r_tmo_tx_link_fired, r_tmo_rx_link_fired;
    logic                 r_starve_fired, r_bp_fired;

    wire w_tx_transient = (tx_link_state == 2'b10) || (tx_link_state == 2'b01);
    wire w_rx_transient = (rx_link_state == 2'b10) || (rx_link_state == 2'b01);
    wire [AGE_WIDTH-1:0] w_starve_age  = r_us - r_starve_stamp;
    wire [AGE_WIDTH-1:0] w_tx_link_age = r_us - r_tx_link_stamp;
    wire [AGE_WIDTH-1:0] w_rx_link_age = r_us - r_rx_link_stamp;

    // ------------------------------------------------------------------
    // Candidates, each gated by its class enable and the type mask
    // ------------------------------------------------------------------
    function automatic logic type_allowed(input logic [3:0] t);
        return !cfg_chi_pkt_mask[t];
    endfunction

    wire w_en_err    = cfg_error_enable   && type_allowed(PktTypeError);
    wire w_en_tmo    = cfg_timeout_enable && !w_never && type_allowed(PktTypeTimeout);
    wire w_en_compl  = cfg_compl_enable   && type_allowed(PktTypeCompletion);
    wire w_en_credit = cfg_credit_enable  && (cfg_stall_threshold != 32'd0) && type_allowed(PktTypeCredit);
    wire w_en_chan   = cfg_channel_enable && type_allowed(PktTypeChannel);
    wire w_en_stream = cfg_stream_enable  && type_allowed(PktTypeStream);

    wire w_err_proto    = w_en_err && protocol_error && !r_proto_q;
    wire w_err_resp     = w_en_err && ((w_crsp_txn && w_hit_crsp && w_crsp_rerr[1]) ||
                                       (w_cdat_read && w_hit_cdat && w_cdat_rerr[1]));
    wire w_err_orph_rsp = w_en_err && w_crsp_txn && !w_hit_crsp;
    wire w_err_orph_dat = w_en_err && w_cdat_read && !w_hit_cdat;
    wire w_err_orph_ack = w_en_err && ((w_qrsp_ack && !w_hit_qrsp) || (w_qdat_wr && !w_hit_qdat));
    wire w_err_orph_snp = w_en_err && ((w_qrsp_snp && !w_s_hit_rsp) || (w_qdat_snp && !w_s_hit_dat));
    wire w_err_full     = w_en_err && w_req_alloc && !w_free;
    wire w_err_s_full   = w_en_err && w_s_alloc && !w_s_free;

    wire w_tmo_txn    = w_en_tmo && w_scan_hit;
    wire w_tmo_snp    = w_en_tmo && w_s_scan_hit;
    wire w_tmo_credit = w_en_tmo && credit_starved && (r_starve_cycles != 32'd0) &&
                        (w_starve_age >= w_tmo) && !r_tmo_credit_fired;
    wire w_tmo_tx     = w_en_tmo && w_tx_transient && (tx_link_state == r_tx_link) &&
                        (w_tx_link_age >= w_tmo) && !r_tmo_tx_link_fired;
    wire w_tmo_rx     = w_en_tmo && w_rx_transient && (rx_link_state == r_rx_link) &&
                        (w_rx_link_age >= w_tmo) && !r_tmo_rx_link_fired && !w_tmo_tx;   // one a cycle; RX waits
    wire w_tmo_link   = w_tmo_tx || w_tmo_rx;

    wire w_compl_txn   = w_en_compl && w_retire_go;
    wire w_compl_retry = w_en_compl && w_retry_hit;
    wire w_compl_snp   = w_en_compl && w_s_done;

    wire w_starved   = w_en_credit && credit_starved && (r_starve_cycles >= cfg_stall_threshold) && !r_starve_fired;
    wire w_backpress = w_en_credit && w_bp && (r_bp_cycles >= cfg_stall_threshold) && !r_bp_fired;

    wire w_chan_pcrd    = w_en_chan && w_crsp_is_pcrd;
    wire w_chan_pcrdret = w_en_chan && w_req_pcrdret;
    wire w_chan_receipt = w_en_chan && w_crsp_receipt;

    wire w_tx_link_evt = w_en_stream && (tx_link_state != r_tx_link);
    wire w_rx_link_evt = w_en_stream && (rx_link_state != r_rx_link);

    // Two same-class events in one cycle share one candidate (RESP_ERR on both RSP and DAT, ORPHAN_ACK or
    // ORPHAN_SNP_RSP on both channels, two snoops retiring). The second is not delivered; it is counted as
    // lost so that delivered + reported dropped still equals issued.
    wire [2:0] w_merged = 3'(w_en_err && (w_crsp_txn && w_hit_crsp && w_crsp_rerr[1]) && (w_cdat_read && w_hit_cdat && w_cdat_rerr[1])) +
                          3'(w_en_err && (w_qrsp_ack && !w_hit_qrsp) && (w_qdat_wr && !w_hit_qdat)) +
                          3'(w_en_err && (w_qrsp_snp && !w_s_hit_rsp) && (w_qdat_snp && !w_s_hit_dat)) +
                          3'(w_en_compl && w_s_done_two);

    localparam int NC = 22;
    logic [NC-1:0] w_cand;      // MSB is the highest priority
    assign w_cand = {w_err_proto, w_err_resp, w_err_orph_rsp, w_err_orph_dat, w_err_orph_ack, w_err_orph_snp,
                     w_err_full, w_err_s_full, w_tmo_txn, w_tmo_snp, w_tmo_credit, w_tmo_link,
                     w_compl_txn, w_compl_retry, w_compl_snp, w_starved, w_backpress,
                     w_chan_pcrd, w_chan_pcrdret, w_chan_receipt, w_tx_link_evt, w_rx_link_evt};

    typedef struct packed {
        logic [3:0]  ptype;
        logic [7:0]  code;
        logic [8:0]  chan;
        logic [63:0] data;
    } chi_entry_t;

    function automatic logic [4:0] first_idx(input logic [NC-1:0] c);
        logic [4:0] r;
        r = '0;
        for (int i = 0; i < NC; i++) if (c[i]) r = 5'(i);
        return r;
    endfunction

    // ------------------------------------------------------------------
    // Event stage: candidates and their payload sources, registered
    // ------------------------------------------------------------------
    logic [NC-1:0]        r_e_cand;
    logic [TW-1:0]        r_e_txn_id, r_e_orph_rsp_id, r_e_orph_dat_id, r_e_orph_ack_id, r_e_orph_snp_id;
    logic [TW-1:0]        r_e_tmo_id, r_e_s_tmo_id, r_e_s_id, r_e_retry_id, r_e_req_id, r_e_snp_new_id;
    logic [6:0]           r_e_txn_opc, r_e_tmo_opc, r_e_req_opc;
    logic [7:0]           r_e_orph_rsp_opc, r_e_orph_dat_opc, r_e_orph_ack_opc, r_e_orph_snp_opc, r_e_resp_opc;
    logic [1:0]           r_e_rerr;
    logic [TW-1:0]        r_e_rerr_id;
    logic [3:0]           r_e_pcrd;
    logic [TS_WIDTH-1:0]  r_e_latency, r_e_s_latency;
    logic [AGE_WIDTH-1:0] r_e_tmo_age, r_e_s_tmo_age, r_e_starve_age, r_e_link_age;
    logic [CW-1:0]        r_e_occ;
    logic [31:0]          r_e_txns, r_e_starve, r_e_bp;
    logic [15:0]          r_e_snps;
    logic [1:0]           r_e_tx_link, r_e_rx_link, r_e_prev_tx_link, r_e_prev_rx_link;
    logic                 r_e_link_tx;
    logic [2:0]           r_e_merged;
    logic [15:0]          r_e_tmo_cfg;
    logic [31:0]          r_e_thresh;
    logic [31:0]          r_txns, r_snps;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_e_cand <= '0;
            r_e_txn_id <= '0; r_e_orph_rsp_id <= '0; r_e_orph_dat_id <= '0; r_e_orph_ack_id <= '0; r_e_orph_snp_id <= '0;
            r_e_tmo_id <= '0; r_e_s_tmo_id <= '0; r_e_s_id <= '0; r_e_retry_id <= '0; r_e_req_id <= '0; r_e_snp_new_id <= '0;
            r_e_txn_opc <= '0; r_e_tmo_opc <= '0; r_e_req_opc <= '0;
            r_e_orph_rsp_opc <= '0; r_e_orph_dat_opc <= '0; r_e_orph_ack_opc <= '0; r_e_orph_snp_opc <= '0; r_e_resp_opc <= '0;
            r_e_rerr <= '0; r_e_rerr_id <= '0; r_e_pcrd <= '0;
            r_e_latency <= '0; r_e_s_latency <= '0;
            r_e_tmo_age <= '0; r_e_s_tmo_age <= '0; r_e_starve_age <= '0; r_e_link_age <= '0;
            r_e_occ <= '0; r_e_txns <= '0; r_e_snps <= '0; r_e_starve <= '0; r_e_bp <= '0;
            r_e_tx_link <= '0; r_e_rx_link <= '0; r_e_prev_tx_link <= '0; r_e_prev_rx_link <= '0; r_e_link_tx <= 1'b0;
            r_e_merged <= '0; r_e_tmo_cfg <= '0; r_e_thresh <= '0;
        end else begin
            r_e_cand         <= clear ? '0 : w_cand;
            r_e_merged       <= clear ? '0 : w_merged;
            r_e_tmo_cfg      <= cfg_timeout_cnt;
            r_e_thresh       <= cfg_stall_threshold;
            r_e_txn_id       <= r_txnid[w_retire_idx];
            r_e_txn_opc      <= r_opcode[w_retire_idx];
            r_e_latency      <= r_cyc - r_cyc_stamp[w_retire_idx];
            r_e_retry_id     <= w_crsp_txnid;
            r_e_pcrd         <= w_crsp_pcrd;
            r_e_orph_rsp_id  <= w_crsp_txnid;
            r_e_orph_rsp_opc <= 8'(w_crsp_opc);
            r_e_orph_dat_id  <= w_cdat_txnid;
            r_e_orph_dat_opc <= 8'(w_cdat_opc);
            r_e_orph_ack_id  <= (w_qrsp_ack && !w_hit_qrsp) ? w_qrsp_txnid : w_qdat_txnid;
            r_e_orph_ack_opc <= (w_qrsp_ack && !w_hit_qrsp) ? 8'(w_qrsp_opc) : 8'(w_qdat_opc);
            r_e_orph_snp_id  <= (w_qrsp_snp && !w_s_hit_rsp) ? w_qrsp_txnid : w_qdat_txnid;
            r_e_orph_snp_opc <= (w_qrsp_snp && !w_s_hit_rsp) ? 8'(w_qrsp_opc) : 8'(w_qdat_opc);
            r_e_rerr         <= (w_crsp_txn && w_hit_crsp && w_crsp_rerr[1]) ? w_crsp_rerr : w_cdat_rerr;
            r_e_rerr_id      <= (w_crsp_txn && w_hit_crsp && w_crsp_rerr[1]) ? w_crsp_txnid : w_cdat_txnid;
            r_e_resp_opc     <= (w_crsp_txn && w_hit_crsp && w_crsp_rerr[1]) ? 8'(w_crsp_opc) : 8'(w_cdat_opc);
            r_e_req_id       <= w_req_txnid;
            r_e_req_opc      <= w_req_opc;
            r_e_snp_new_id   <= w_snp_txnid;
            r_e_tmo_id       <= r_txnid[r_scan];
            r_e_tmo_opc      <= r_opcode[r_scan];
            r_e_tmo_age      <= w_scan_age;
            r_e_s_tmo_id     <= r_s_txnid[r_s_scan];
            r_e_s_tmo_age    <= w_s_scan_age;
            r_e_s_id         <= r_s_txnid[w_s_done_idx];
            r_e_s_latency    <= r_cyc - r_s_cyc[w_s_done_idx];
            r_e_starve_age   <= w_starve_age;
            r_e_link_age     <= w_tmo_tx ? w_tx_link_age : w_rx_link_age;
            r_e_link_tx      <= w_tmo_tx;
            r_e_occ          <= w_occupancy;
            r_e_txns         <= r_txns + 32'(w_retire_go) + 32'(w_retry_hit);
            r_e_snps         <= 16'(r_snps + 32'(w_s_done) + 32'(w_s_done_two));
            r_e_starve       <= r_starve_cycles;
            r_e_bp           <= r_bp_cycles;
            r_e_tx_link      <= tx_link_state;
            r_e_rx_link      <= rx_link_state;
            r_e_prev_tx_link <= r_tx_link;
            r_e_prev_rx_link <= r_rx_link;
        end
    )

    function automatic logic [7:0] link_code(input logic [1:0] st, input logic tx);
        logic [7:0] c;
        case (st)
            2'b10:   c = 8'(CHI_STREAM_TX_ACTIVATE);
            2'b11:   c = 8'(CHI_STREAM_TX_UP);
            2'b01:   c = 8'(CHI_STREAM_TX_DEACTIVATE);
            default: c = 8'(CHI_STREAM_TX_DOWN);
        endcase
        return tx ? c : (c + 8'd4);
    endfunction

    function automatic chi_entry_t cand_entry(input logic [4:0] idx);
        chi_entry_t e;
        e = '{ptype: PktTypeError, code: 8'h00, chan: 9'h0, data: 64'h0};
        case (idx)
            5'd21: begin e.ptype = PktTypeError;      e.code = 8'(CHI_ERR_PROTOCOL);
                         e.data = {16'(r_e_occ), 6'h0, r_e_tx_link, 6'h0, r_e_rx_link, r_e_txns}; end
            5'd20: begin e.ptype = PktTypeError;      e.code = 8'(CHI_ERR_RESP_ERR); e.chan = 9'(r_e_rerr_id);
                         e.data = {r_e_resp_opc, 6'h0, r_e_rerr, 4'h0, r_e_rerr_id, 32'(r_e_txns)}; end
            5'd19: begin e.ptype = PktTypeError;      e.code = 8'(CHI_ERR_ORPHAN_RSP); e.chan = 9'(r_e_orph_rsp_id);
                         e.data = {r_e_orph_rsp_opc, 12'h0, r_e_orph_rsp_id, 16'(r_e_occ), 16'h0}; end
            5'd18: begin e.ptype = PktTypeError;      e.code = 8'(CHI_ERR_ORPHAN_DAT); e.chan = 9'(r_e_orph_dat_id);
                         e.data = {r_e_orph_dat_opc, 12'h0, r_e_orph_dat_id, 16'(r_e_occ), 16'h0}; end
            5'd17: begin e.ptype = PktTypeError;      e.code = 8'(CHI_ERR_ORPHAN_ACK); e.chan = 9'(r_e_orph_ack_id);
                         e.data = {r_e_orph_ack_opc, 12'h0, r_e_orph_ack_id, 16'(r_e_occ), 16'h0}; end
            5'd16: begin e.ptype = PktTypeError;      e.code = 8'(CHI_ERR_ORPHAN_SNP_RSP); e.chan = 9'(r_e_orph_snp_id);
                         e.data = {r_e_orph_snp_opc, 12'h0, r_e_orph_snp_id, 16'(r_e_occ), 16'h0}; end
            5'd15: begin e.ptype = PktTypeError;      e.code = 8'(CHI_ERR_TABLE_FULL); e.chan = 9'(r_e_req_id);
                         e.data = {8'(r_e_req_opc), 12'h0, r_e_req_id, 16'(r_e_occ), 16'h0}; end
            5'd14: begin e.ptype = PktTypeError;      e.code = 8'(CHI_ERR_SNP_TABLE_FULL); e.chan = 9'(r_e_snp_new_id);
                         e.data = {20'h0, r_e_snp_new_id, 16'(r_e_occ), 16'h0}; end
            5'd13: begin e.ptype = PktTypeTimeout;    e.code = 8'(CHI_TIMEOUT_TXN); e.chan = 9'(r_e_tmo_id);
                         e.data = {8'(r_e_tmo_opc), 4'h0, r_e_tmo_id, 8'h0, 16'(r_e_tmo_age), r_e_tmo_cfg}; end
            5'd12: begin e.ptype = PktTypeTimeout;    e.code = 8'(CHI_TIMEOUT_SNP); e.chan = 9'(r_e_s_tmo_id);
                         e.data = {12'h0, r_e_s_tmo_id, 8'h0, 16'(r_e_s_tmo_age), r_e_tmo_cfg}; end
            5'd11: begin e.ptype = PktTypeTimeout;    e.code = 8'(CHI_TIMEOUT_CREDIT);
                         e.data = {r_e_starve, 16'(r_e_starve_age), r_e_tmo_cfg}; end
            5'd10: begin e.ptype = PktTypeTimeout;    e.code = 8'(CHI_TIMEOUT_LINK);
                         e.data = {16'(r_e_occ), 5'h0, r_e_link_tx, r_e_tx_link, 6'h0, r_e_rx_link, 16'(r_e_link_age), r_e_tmo_cfg}; end
            5'd9:  begin e.ptype = PktTypeCompletion; e.code = 8'(CHI_COMPL_TXN); e.chan = 9'(r_e_txn_id);
                         e.data = {16'(r_e_latency), 8'(r_e_txn_opc), 4'h0, r_e_txn_id, 8'(r_e_occ), 16'(r_e_txns)}; end
            5'd8:  begin e.ptype = PktTypeCompletion; e.code = 8'(CHI_COMPL_RETRY); e.chan = 9'(r_e_retry_id);
                         e.data = {16'h0, 4'h0, r_e_pcrd, 4'h0, r_e_retry_id, 8'(r_e_occ), 16'(r_e_txns)}; end
            5'd7:  begin e.ptype = PktTypeCompletion; e.code = 8'(CHI_COMPL_SNP); e.chan = 9'(r_e_s_id);
                         e.data = {16'(r_e_s_latency), 8'h0, 4'h0, r_e_s_id, 8'h0, r_e_snps}; end
            5'd6:  begin e.ptype = PktTypeCredit;     e.code = 8'(CHI_CREDIT_STARVED);
                         e.data = {r_e_starve, r_e_thresh}; end
            5'd5:  begin e.ptype = PktTypeCredit;     e.code = 8'(CHI_CREDIT_BACKPRESSURE);
                         e.data = {r_e_bp, r_e_thresh}; end
            5'd4:  begin e.ptype = PktTypeChannel;    e.code = 8'(CHI_CHAN_PCRD_GRANT);
                         e.data = {28'h0, r_e_pcrd, 32'(r_e_txns)}; end
            5'd3:  begin e.ptype = PktTypeChannel;    e.code = 8'(CHI_CHAN_PCRD_RETURN); e.chan = 9'(r_e_req_id);
                         e.data = {20'h0, r_e_req_id, 32'(r_e_txns)}; end
            5'd2:  begin e.ptype = PktTypeChannel;    e.code = 8'(CHI_CHAN_READ_RECEIPT); e.chan = 9'(r_e_orph_rsp_id);
                         e.data = {20'h0, r_e_orph_rsp_id, 32'(r_e_txns)}; end
            5'd1:  begin e.ptype = PktTypeStream;     e.code = link_code(r_e_tx_link, 1'b1);
                         e.data = {16'(r_e_occ), 6'h0, r_e_prev_tx_link, 6'h0, r_e_prev_rx_link,
                                   6'h0, r_e_tx_link, 6'h0, r_e_rx_link, 16'(r_e_txns)}; end
            default: begin
                         e.ptype = PktTypeStream;
                         e.code  = link_code(r_e_rx_link, 1'b0);
                         e.data  = {16'(r_e_occ), 6'h0, r_e_prev_tx_link, 6'h0, r_e_prev_rx_link,
                                    6'h0, r_e_tx_link, 6'h0, r_e_rx_link, 16'(r_e_txns)};
                     end
        endcase
        return e;
    endfunction

    logic [NC-1:0] w_cand2;
    logic [4:0]    w_i1, w_i2;
    logic          w_fire1, w_fire2;
    logic [4:0]    w_ev_n;
    assign w_i1    = first_idx(r_e_cand);
    assign w_cand2 = r_e_cand & ~(NC'(1) << w_i1);
    assign w_i2    = first_idx(w_cand2);
    assign w_fire1 = (|r_e_cand) && !clear;
    assign w_fire2 = (|w_cand2)  && !clear;
    assign w_ev_n  = clear ? 5'd0 : (5'($countones(r_e_cand)) + 5'(r_e_merged));
    chi_entry_t w_e1, w_e2;
    assign w_e1 = cand_entry(w_i1);
    assign w_e2 = cand_entry(w_i2);

    // ------------------------------------------------------------------
    // Tracking state
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_valid <= '0; r_dbid_ok <= '0; r_need_comp <= '0; r_need_dbid <= '0; r_need_ack <= '0; r_tmo <= '0;
            for (int i = 0; i < N; i++) begin
                r_txnid[i] <= '0; r_dbid[i] <= '0; r_opcode[i] <= '0; r_pkts[i] <= '0; r_dat_rem[i] <= '0; r_wdat_rem[i] <= '0;
                r_us_stamp[i] <= '0; r_cyc_stamp[i] <= '0;
            end
            r_s_valid <= '0; r_s_tmo <= '0;
            for (int i = 0; i < M; i++) begin
                r_s_txnid[i] <= '0; r_s_rem[i] <= '0; r_s_us[i] <= '0; r_s_cyc[i] <= '0;
            end
            r_scan <= '0; r_s_scan <= '0; r_txns <= '0; r_snps <= '0;
            r_tx_link <= 2'b00; r_rx_link <= 2'b00; r_proto_q <= 1'b0;
            r_starve_cycles <= '0; r_bp_cycles <= '0;
            r_starve_stamp <= '0; r_tx_link_stamp <= '0; r_rx_link_stamp <= '0;
            r_tmo_credit_fired <= 1'b0; r_tmo_tx_link_fired <= 1'b0; r_tmo_rx_link_fired <= 1'b0;
            r_starve_fired <= 1'b0; r_bp_fired <= 1'b0;
        end else if (clear) begin
            r_valid <= '0; r_dbid_ok <= '0; r_need_comp <= '0; r_need_dbid <= '0; r_need_ack <= '0; r_tmo <= '0;
            r_s_valid <= '0; r_s_tmo <= '0;
            r_scan <= '0; r_s_scan <= '0; r_txns <= '0; r_snps <= '0;
            r_tx_link <= tx_link_state; r_rx_link <= rx_link_state; r_proto_q <= protocol_error;
            r_starve_cycles <= '0; r_bp_cycles <= '0;
            r_starve_stamp <= r_us; r_tx_link_stamp <= r_us; r_rx_link_stamp <= r_us;   // episodes restart at the clear
            r_tmo_credit_fired <= 1'b0; r_tmo_tx_link_fired <= 1'b0; r_tmo_rx_link_fired <= 1'b0;
            r_starve_fired <= 1'b0; r_bp_fired <= 1'b0;
        end else begin
            r_proto_q <= protocol_error;
            r_scan    <= (r_scan == SW'(N - 1)) ? '0 : r_scan + 1'b1;
            r_s_scan  <= (r_s_scan == MW'(M - 1)) ? '0 : r_s_scan + 1'b1;
            r_txns    <= r_txns + 32'(w_retire_go) + 32'(w_retry_hit);
            r_snps    <= r_snps + 32'(w_s_done) + 32'(w_s_done_two);

            // ---- request slots: allocate, update, retire ----
            if (w_req_alloc && w_free) begin
                r_valid[w_free_idx]     <= 1'b1;
                r_txnid[w_free_idx]     <= w_req_txnid;
                r_opcode[w_free_idx]    <= w_req_opc;
                r_dbid_ok[w_free_idx]   <= 1'b0;
                r_need_comp[w_free_idx] <= 1'b1;
                r_need_dbid[w_free_idx] <= owes_dbid(w_req_opc);
                r_need_ack[w_free_idx]  <= w_req_eca;
                r_pkts[w_free_idx]      <= owes_wdata(w_req_opc) ? w_req_pkts : 3'd0;   // write data the DBID will pull
                r_dat_rem[w_free_idx]   <= is_read_opcode(w_req_opc) ? w_req_pkts : 3'd0;
                r_wdat_rem[w_free_idx]  <= 3'd0;
                r_us_stamp[w_free_idx]  <= r_us;
                r_cyc_stamp[w_free_idx] <= r_cyc;
                r_tmo[w_free_idx]       <= 1'b0;
            end
            for (int i = 0; i < N; i++) begin
                // responses toward the requester
                if (w_m_crsp[i] && (w_crsp_comp || w_crsp_is_dbid)) begin
                    // every completion and DBID response carries the DBID the CompAck or write data will use
                    // (B2.4.3); the latest one wins, which is the DBID response when both are sent. The key is
                    // armed only when something will come back under it, so a read's unused DBID field
                    // (often 0) cannot alias a live write's DBID.
                    r_dbid[i]    <= w_crsp_dbid;
                    r_dbid_ok[i] <= w_crsp_is_dbid || r_need_ack[i] || (w_crsp_plain && is_copyback(r_opcode[i]));
                    if (w_crsp_comp) r_need_comp[i] <= 1'b0;
                    if (w_crsp_plain && (r_opcode[i] == CHI_REQ_MAKE_READ_UNIQUE))
                        r_dat_rem[i] <= 3'd0;                                  // MakeReadUnique may finish without data
                    if (w_crsp_plain && is_copyback(r_opcode[i])) begin
                        r_need_dbid[i] <= 1'b0;                                // B2.3.2.3 alt 1a: no data transfer,
                        r_need_ack[i]  <= 1'b1;                                // and a CompAck regardless of ExpCompAck
                    end
                    if (w_crsp_is_dbid) begin
                        r_need_dbid[i] <= 1'b0;
                        r_wdat_rem[i]  <= r_pkts[i];                           // the write data the Size named (0 for the Zero writes)
                    end
                end
                if (w_m_cdat[i] && w_cdat_read) begin
                    if (r_dat_rem[i] != 3'd0) r_dat_rem[i] <= r_dat_rem[i] - 3'd1;
                    if ((w_cdat_opc == CHI_DAT_COMP_DATA) && (r_dat_rem[i] <= 3'd1))
                        r_need_comp[i] <= 1'b0;                                // CompData is the completion too
                    r_dbid[i]    <= w_cdat_dbid;                               // CompData carries the DBID the CompAck uses
                    r_dbid_ok[i] <= r_need_ack[i];
                end
                // messages from the requester
                if (w_m_qrsp[i] && w_qrsp_ack) r_need_ack[i] <= 1'b0;
                if (w_m_qdat[i] && w_qdat_wr) begin
                    if (w_qdat_cancel)             r_wdat_rem[i] <= 3'd0;
                    else if (r_wdat_rem[i] != 3'd0) r_wdat_rem[i] <= r_wdat_rem[i] - 3'd1;
                    if (w_qdat_wr_ack)             r_need_ack[i] <= 1'b0;
                end
                if (w_tmo_txn && (r_scan == SW'(i))) r_tmo[i] <= 1'b1;
            end
            if (w_retire_go) r_valid[w_retire_idx] <= 1'b0;
            if (w_retry_hit) r_valid[w_retry_idx]  <= 1'b0;

            // ---- snoop slots ----
            if (w_s_alloc && w_s_free) begin
                r_s_valid[w_s_free_idx] <= 1'b1;
                r_s_txnid[w_s_free_idx] <= w_snp_txnid;
                r_s_rem[w_s_free_idx]   <= 3'(LINE_PKTS);
                r_s_us[w_s_free_idx]    <= r_us;
                r_s_cyc[w_s_free_idx]   <= r_cyc;
                r_s_tmo[w_s_free_idx]   <= 1'b0;
            end
            for (int i = 0; i < M; i++) begin
                if (w_sm_dat[i] && w_qdat_snp && (r_s_rem[i] != 3'd0)) r_s_rem[i] <= r_s_rem[i] - 3'd1;
                if (w_tmo_snp && (r_s_scan == MW'(i))) r_s_tmo[i] <= 1'b1;
            end
            if (w_s_done_rsp) r_s_valid[w_s_rsp_idx] <= 1'b0;
            if (w_s_done_dat) r_s_valid[w_s_dat_idx] <= 1'b0;

            // ---- link state episodes ----
            r_tx_link <= tx_link_state;
            r_rx_link <= rx_link_state;
            if (tx_link_state != r_tx_link) begin
                r_tx_link_stamp     <= r_us;
                r_tmo_tx_link_fired <= 1'b0;
            end else if (w_tmo_tx) begin
                r_tmo_tx_link_fired <= 1'b1;
            end
            if (rx_link_state != r_rx_link) begin
                r_rx_link_stamp     <= r_us;
                r_tmo_rx_link_fired <= 1'b0;
            end else if (w_tmo_rx) begin
                r_tmo_rx_link_fired <= 1'b1;
            end
            // ---- credit starvation episodes ----
            if (credit_starved) begin
                if (r_starve_cycles == '0) r_starve_stamp <= r_us;
                if (r_starve_cycles != 32'hFFFF_FFFF) r_starve_cycles <= r_starve_cycles + 32'd1;
                if (w_tmo_credit) r_tmo_credit_fired <= 1'b1;
                if (w_starved)    r_starve_fired     <= 1'b1;
            end else begin
                r_starve_cycles    <= '0;
                r_tmo_credit_fired <= 1'b0;
                r_starve_fired     <= 1'b0;
            end
            // ---- FUB backpressure episodes ----
            if (w_bp) begin
                if (r_bp_cycles != 32'hFFFF_FFFF) r_bp_cycles <= r_bp_cycles + 32'd1;
                if (w_backpress) r_bp_fired <= 1'b1;
            end else begin
                r_bp_cycles <= '0;
                r_bp_fired  <= 1'b0;
            end
        end
    )

    // ------------------------------------------------------------------
    // Output queue, drop accounting and the drop report: the CXS lite's
    // structure, unchanged (see cxs_monitor_lite for the reasoning).
    // ------------------------------------------------------------------
    localparam int OQW   = (OUT_DEPTH > 1) ? $clog2(OUT_DEPTH) : 1;
    localparam int OQ_BD = ((OUT_DEPTH + 1) / 2 < 2) ? 2 : (OUT_DEPTH + 1) / 2;
    logic [OQW:0] r_q_count;
    logic         r_q_wb, r_q_rb;
    wire  [OQW:0] w_q_count = r_q_count;
    wire          w_q_empty = (w_q_count == '0);
    wire          w_room1   = (w_q_count <= (OQW+1)'(OUT_DEPTH - 1));
    wire          w_room2   = (OUT_DEPTH >= 2) && (w_q_count <= (OQW+1)'(OUT_DEPTH - 2));

    wire         w_take1    = w_fire1 && w_room1;
    wire         w_take2    = w_fire2 && w_room2;
    wire  [4:0]  w_lost     = w_ev_n - 5'(w_take1) - 5'(w_take2);
    logic [4:0]  r_lost;
    logic [15:0] r_dropped, r_errors;
    wire         w_drop_rpt = (r_dropped != 16'd0) && (r_lost == 5'd0) && !w_fire1 && w_q_empty && w_en_err && !clear;
    wire  [1:0]  w_err_take = 2'(w_take1 && (w_e1.ptype == PktTypeError)) + 2'(w_take2 && (w_e2.ptype == PktTypeError));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_lost <= '0; r_dropped <= '0; r_errors <= '0;
        end else if (clear) begin
            r_lost <= '0; r_dropped <= '0; r_errors <= '0;
        end else begin
            r_lost <= w_lost;
            if (w_drop_rpt)            r_dropped <= '0;
            else if (&r_dropped[15:5]) r_dropped <= 16'hFFFF;
            else                       r_dropped <= r_dropped + 16'(r_lost);
            if ((w_err_take != 2'd0) && (r_errors < 16'hFFFE)) r_errors <= r_errors + 16'(w_err_take);
        end
    )

    chi_entry_t w_slot1, w_entry_out;
    assign w_slot1 = w_fire1 ? w_e1
                             : '{ptype: PktTypeError, code: 8'(CHI_ERR_EVENT_DROPPED), chan: 9'd0, data: 64'(r_dropped)};
    wire w_push1 = w_take1 || w_drop_rpt;
    wire w_push2 = w_take2;
    wire w_q_pop = monbus_valid && monbus_ready;

    logic [1:0]                       w_bank_wr, w_bank_rd_valid;
    logic [$bits(chi_entry_t)-1:0]    w_bank_wr_data [2];
    logic [$bits(chi_entry_t)-1:0]    w_bank_rd_data [2];
    assign w_entry_out = chi_entry_t'(w_bank_rd_data[r_q_rb]);
    for (genvar b = 0; b < 2; b++) begin : g_bank
        wire w_mine1 = (r_q_wb == 1'(b));
        assign w_bank_wr[b]      = w_mine1 ? w_push1 : w_push2;
        assign w_bank_wr_data[b] = w_mine1 ? w_slot1 : w_e2;
        gaxi_fifo_sync #(
            .REGISTERED (0),
            .DATA_WIDTH ($bits(chi_entry_t)),
            .DEPTH      (OQ_BD)
        ) u_out_q (
            .axi_aclk    (aclk),
            .axi_aresetn (aresetn),
            .wr_valid    (w_bank_wr[b]),
            /* verilator lint_off PINCONNECTEMPTY */
            .wr_ready    (),
            .count       (),
            /* verilator lint_on PINCONNECTEMPTY */
            .wr_data     (w_bank_wr_data[b]),
            .rd_ready    (w_q_pop && (r_q_rb == 1'(b))),
            .rd_valid    (w_bank_rd_valid[b]),
            .rd_data     (w_bank_rd_data[b])
        );
    end
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused_bank_rd_valid = ^w_bank_rd_valid;
    /* verilator lint_on UNUSEDSIGNAL */

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_q_count <= '0; r_q_wb <= 1'b0; r_q_rb <= 1'b0;
        end else begin
            r_q_count <= r_q_count + (OQW+1)'(w_push1) + (OQW+1)'(w_push2) - (OQW+1)'(w_q_pop);
            r_q_wb    <= r_q_wb ^ (w_push1 ^ w_push2);
            if (w_q_pop) r_q_rb <= !r_q_rb;
        end
    )

    assign monbus_valid     = !w_q_empty;
    assign monbus_packet    = create_monitor_packet(w_entry_out.ptype, PROTOCOL_CHI, w_entry_out.code,
                                                    w_entry_out.chan, UNIT_ID, AGENT_ID, w_entry_out.data);
    assign monbus_timestamp = i_mon_time;

    assign busy          = (|r_valid) || (|r_s_valid) || credit_starved || w_bp || w_tx_transient ||
                           w_rx_transient || (|r_e_cand) || (r_lost != 5'd0) || monbus_valid;
    assign active_count  = w_occupancy;
    assign txn_count     = r_txns;
    assign snoop_count   = r_snps;
    assign error_count   = r_errors;
    assign dropped_count = r_dropped;

    // The flit bits this block does not read (payload) and the field it keys but never reports
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused_fields = ^{req_flit, cpl_rsp_flit, cpl_dat_flit, rq_rsp_flit, rq_dat_flit, snp_flit, r_e_prev_rx_link};
    /* verilator lint_on UNUSEDSIGNAL */

endmodule : chi_monitor_lite

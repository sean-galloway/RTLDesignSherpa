#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generate rapids_signal_contracts.xlsx for the current RAPIDS-beats RTL.

Built on the shared machinery in bin/kmaps (TOOLING-KMAP step 5), the same
package the STREAM generator uses. What lives here is RAPIDS-specific: the RTL
path constants, the CITES registry, and the build_* sheet builders.

First target (rapids TASK-002 item 3) is the `drain_size_gt1` SOURCE beat drop
(known_issues/active/drain_size_gt1_source_beat_drop.md). Beat-drop bugs are
adjacency bugs, which is what a K-map is for -- and in this case the map makes
a MISSING TERM visible: the drain grant is qualified on an availability view
that counts beats the reservation accounting has already subtracted.

Rerun after source drain-path RTL changes:
    source env_python && python3 docs/gen_rapids_signal_contracts_kmaps.py
"""
import os

import openpyxl

from kmaps.citations import verify_citations
from kmaps.writer import CONTRACT_HDRS, contract_sheet, new_kmap_sheet

HERE = os.path.dirname(os.path.abspath(__file__))
XLSX = os.path.join(HERE, "rapids_signal_contracts.xlsx")
REPO = os.path.abspath(os.path.join(HERE, *([".."] * 5)))

# ---------------------------------------------------------------------------
# RTL under analysis
# ---------------------------------------------------------------------------
SRC_AXIS = "projects/components/dmas/rapids/rtl/macro_beats/src_data_path_axis_beats.sv"
SRC_UNIT = "projects/components/dmas/rapids/rtl/macro_beats/src_sram_controller_unit_beats.sv"
SNK_UNIT = "projects/components/dmas/rapids/rtl/macro_beats/snk_sram_controller_unit_beats.sv"
DRAIN_B = "projects/components/dmas/rapids/rtl/fub_beats/drain_ctrl_beats.sv"
ALLOC_B = "projects/components/dmas/rapids/rtl/fub_beats/alloc_ctrl_beats.sv"
SNK_AXIS = "projects/components/dmas/rapids/rtl/macro_beats/snk_data_path_axis_beats.sv"
SCHED_B = "projects/components/dmas/rapids/rtl/fub_beats/scheduler_beats.sv"
WR_ENG_B = "projects/components/dmas/rapids/rtl/fub_beats/axi_write_engine_beats.sv"
SNK_MACRO = "projects/components/dmas/rapids/rtl/macro_beats/rapids_snk_beats.sv"
SNK_DP = "projects/components/dmas/rapids/rtl/macro_beats/snk_data_path_beats.sv"
SRC_MACRO = "projects/components/dmas/rapids/rtl/macro_beats/rapids_src_beats.sv"
SNK_SRAM = "projects/components/dmas/rapids/rtl/macro_beats/snk_sram_controller_beats.sv"
SG = "projects/components/dmas/rapids/rtl/macro_beats/scheduler_group_beats.sv"
SG_ARR = "projects/components/dmas/rapids/rtl/macro_beats/scheduler_group_array_beats.sv"
CTRLRD = "projects/components/dmas/rapids/rtl/fub/ctrlrd_engine.sv"
LBRIDGE = "projects/components/dmas/rapids/rtl/fub_beats/latency_bridge_beats.sv"

# STREAM, cited as the CONTRAST: same fork, defect already fixed there.
STR_UNIT = "projects/components/dmas/stream/rtl/fub/sram_controller_unit.sv"
STR_MACRO = "projects/components/dmas/stream/rtl/fub/sram_controller.sv"
STR_WENG = "projects/components/dmas/stream/rtl/fub/axi_write_engine.sv"
STR_RENG = "projects/components/dmas/stream/rtl/fub/axi_read_engine.sv"
STR_SCHED = "projects/components/dmas/stream/rtl/fub/scheduler.sv"
STR_CORE = "projects/components/dmas/stream/rtl/macro/stream_core.sv"

KI_DRAIN = ("projects/components/dmas/rapids/known_issues/active/"
            "drain_size_gt1_source_beat_drop.md")
KI_STALL = ("projects/components/dmas/rapids/known_issues/resolved/"
            "snk_scheduler_write_commit_stall.md")
KI_SDP = ("projects/components/dmas/rapids/known_issues/active/"
          "sink_data_path.md")
KI_SSC = ("projects/components/dmas/rapids/known_issues/active/"
          "sink_sram_control.md")

# ---------------------------------------------------------------------------
# Citation registry: (path-relative-to-repo, line, snippet-on-that-line).
# Verified against the RTL before the workbook is written.
# ---------------------------------------------------------------------------
CITES = [
    (SRC_AXIS, 216, "w_ch_grantable[ch] = (w_effective_avail[ch] >= SCW'(cfg_drain_size))"),
    (SRC_AXIS, 292, "drain_req[r_arb_grant_id] = 1'b1;"),
    (SRC_AXIS, 293, "drain_size[r_arb_grant_id] = r_drain_remaining;"),
    (SRC_AXIS, 299, "assign drain_read = w_beat_accepted;"),
    (SRC_AXIS, 329, "assign m_axis_tvalid = r_arb_active"),

    (STR_UNIT, 141, ".rd_valid           (axi_wr_sram_valid && axi_wr_sram_ready),"),
    (STR_UNIT, 189, ".rd_valid           (axi_wr_drain_req),"),
    (STR_UNIT, 190, ".rd_size            (axi_wr_drain_size),"),
    (STR_UNIT, 191, ".rd_ready           ()"),
    (STR_UNIT, 194, ".data_available     (drain_data_available),"),
    (STR_UNIT, 307, "assign axi_wr_drain_data_avail = drain_data_available;"),
    (STR_UNIT, 307, "assign axi_wr_drain_data_avail = drain_data_available;"),

    (DRAIN_B, 78, "assign w_read  = rd_valid && rd_ready;"),
    (DRAIN_B, 101, "if (w_read && !r_rd_empty) begin"),
    (DRAIN_B, 102, "r_rd_ptr_bin <= r_rd_ptr_bin + (AW+1)'(rd_size);"),
    (DRAIN_B, 142, "assign rd_ready = !r_rd_empty;"),
    (DRAIN_B, 145, "assign data_available = w_count;"),
    (DRAIN_B, 156, "The read pointer advances by the FULL rd_size, gated only on !rd_empty."),
    (DRAIN_B, 176, "((AW+1)'(rd_size) > data_available)) begin"),

    (LBRIDGE, 185, "assign occupancy = skid_count;"),

    (STR_UNIT, 282, "Total data available = drain controller occupancy, and NOTHING else."),
    (STR_UNIT, 284, "Do NOT add bridge_occupancy here."),
    (STR_UNIT, 290, "Adding bridge_occupancy counted it a second time."),
    (STR_UNIT, 292, "The over-count was 0..SKID_DEPTH (4) beats"),
    (STR_UNIT, 307, "assign axi_wr_drain_data_avail = drain_data_available;"),
    (STR_WENG, 387, "w_effective_avail"),

    # --- item 5: sink AXIS ingress admission ---------------------------
    (SNK_AXIS, 188, "wire w_channel_needs_alloc = (r_pending_alloc[axis_channel_id] == '0);"),
    (SNK_AXIS, 189, "wire w_channel_has_space = (fill_space_free[axis_channel_id] >= cfg_alloc_size);"),
    (SNK_AXIS, 192, "assign fill_alloc_req = s_axis_tvalid && w_channel_needs_alloc && w_channel_has_space;"),
    (SNK_AXIS, 200, "assign fill_valid = s_axis_tvalid &&"),
    (SNK_AXIS, 201, "((r_pending_alloc[axis_channel_id] > 0) ||"),
    (SNK_AXIS, 202, "(w_channel_needs_alloc && w_channel_has_space));"),
    (SNK_AXIS, 207, "assign s_axis_tready = (fill_ready && (r_pending_alloc[axis_channel_id] > 0)) ||"),
    (SNK_AXIS, 208, "(fill_alloc_req);"),
    (SNK_AXIS, 222, "if (fill_alloc_req && (fill_alloc_id == ch[CIW-1:0])) begin"),
    (SNK_AXIS, 225, "r_pending_alloc[ch] <= r_pending_alloc[ch] + fill_alloc_size - 1'b1;"),
    (SNK_AXIS, 228, "r_pending_alloc[ch] <= r_pending_alloc[ch] + fill_alloc_size;"),
    (SNK_AXIS, 232, "r_pending_alloc[ch] <= r_pending_alloc[ch] - 1'b1;"),
    (SNK_AXIS, 237, "if (s_axis_tvalid && s_axis_tready) begin"),

    (STR_UNIT, 134, ".wr_valid           (axi_rd_alloc_req),"),
    (STR_UNIT, 136, ".wr_ready           ()"),
    (STR_UNIT, 184, ".wr_valid           (axi_rd_sram_valid && axi_rd_sram_ready),"),
    (STR_UNIT, 225, ".wr_valid       (axi_rd_sram_valid),"),
    (STR_UNIT, 226, ".wr_ready       (axi_rd_sram_ready),"),
    (STR_UNIT, 314, "axi_rd_alloc_space_free <= alloc_space_free;"),

    (ALLOC_B, 76, "assign w_write = wr_valid && wr_ready;"),
    (ALLOC_B, 86, "if (w_write && !r_wr_full) begin"),
    (ALLOC_B, 137, "assign wr_ready = !r_wr_full;"),
    (ALLOC_B, 141, "assign space_free = (AW+1)'(D) - w_count;"),

    (STR_RENG, 580, "axi_rd_alloc_req |-> $past(m_axi_arvalid && m_axi_arready));"),

    # --- item 4: scheduler issue/commit gating + timeout escalation -----
    (SCHED_B, 418, "if (w_exec_complete) begin"),
    (SCHED_B, 771, "assign w_read_complete = (r_read_beats_remaining == 32'h0);"),
    (SCHED_B, 775, "assign w_write_complete = (r_write_beats_to_commit == 32'h0);"),
    (SCHED_B, 776, "assign w_transfer_complete = w_read_complete && w_write_complete;"),
    (SCHED_B, 779, "assign w_is_data   = (r_desc_opcode == DESC_OP_DATA);"),
    (SCHED_B, 792, "assign w_exec_complete = w_is_data ? w_transfer_complete : w_ctrl_complete;"),
    (SCHED_B, 858, "assign sched_wr_valid = (r_current_state == rapids_pkg::CH_XFER_DATA) && w_is_data &&"),
    (SCHED_B, 859, "(r_write_beats_remaining != 32'h0) &&"),
    (SCHED_B, 860, "!w_write_complete &&"),
    (SCHED_B, 861, "!w_sched_wr_completing_this_cycle &&"),
    (SCHED_B, 862, "!w_wr_need_base;"),
    (SCHED_B, 920, "if (sched_wr_done_strobe || sched_wr_commit_strobe) begin"),
    (SCHED_B, 932, "if (r_channel_reset_active || (r_current_state == rapids_pkg::CH_IDLE)) begin"),
    (SCHED_B, 936, "end else if (w_timeout_expired && !(&r_timeout_strikes)) begin"),
    (SCHED_B, 965, "assign w_timeout_expired = cfg_sched_timeout_enable &&"),
    (SCHED_B, 966, "(r_timeout_counter >= cfg_sched_timeout_cycles);"),
    (SCHED_B, 970, "assign w_timeout_escalate = (cfg_sched_timeout_limit != 8'd0) &&"),
    (SCHED_B, 971, "(r_timeout_strikes >= cfg_sched_timeout_limit);"),
    (SCHED_B, 978, "assign w_hard_error = descriptor_error || sched_rd_error || sched_wr_error ||"),
    (SCHED_B, 1105, "assign scheduler_idle = (r_current_state == rapids_pkg::CH_IDLE) && !r_channel_reset_active;"),
    (SCHED_B, 1136, "(w_read_complete && w_write_complete);"),

    (STR_SCHED, 525, "end else if (w_transfer_complete && !r_rd_ahead) begin"),
    (STR_SCHED, 542, "end else if (w_write_complete) begin"),
    (STR_SCHED, 902, "assign w_write_issued   = (r_write_beats_remaining == 32'h0);"),
    (STR_SCHED, 909, "assign w_transfer_complete = w_read_complete && w_write_issued;"),
    (STR_SCHED, 1376, "(w_read_complete && w_write_issued);"),

    # --- items 1-2: sink error reporting + drain port --------------------
    (WR_ENG_B, 144, "sched_wr_error"),
    (WR_ENG_B, 951, "m_axi_bresp != 2'b00"),
    (WR_ENG_B, 955, "r_wr_error[ch_id] <= 1'b1;"),
    (WR_ENG_B, 964, "assign sched_wr_error = r_wr_error;"),

    (SNK_MACRO, 344, "scheduler_group_array_beats #("),
    (SNK_MACRO, 513, ".sched_rd_error         ('0),"),
    (SNK_MACRO, 514, ".sched_wr_error         (sched_wr_error),"),
    (SNK_MACRO, 596, "snk_data_path_axis_beats #("),
    (SNK_MACRO, 640, ".sched_wr_error     (sched_wr_error),"),
    (SNK_DP, 275, ".sched_wr_error     (sched_wr_error),"),

    (SRC_MACRO, 491, ".sched_rd_error         (sched_rd_error),"),
    (SRC_MACRO, 492, ".sched_wr_error         ('0),"),

    (SG_ARR, 540, ".sched_rd_error         (sched_rd_error[ch]),"),
    (SG_ARR, 541, ".sched_wr_error         (sched_wr_error[ch]),"),

    (SG, 264, "descriptor_engine_beats #("),
    (SG, 289, ".descriptor_error       (desceng_to_sched_error),"),
    (SG, 411, ".sched_wr_error         (sched_wr_error),"),
    (SG, 419, ".ctrlrd_error           (sched_ctrlrd_error),"),
    (CTRLRD, 437, "assign ctrlrd_error = r_ctrlrd_error;"),

    (SCHED_B, 162, "sched_rd_error"),
    (SCHED_B, 163, "sched_wr_error"),
    (SCHED_B, 943, "if (sched_rd_error) r_read_error_sticky <= 1'b1;"),
    (SCHED_B, 944, "if (sched_wr_error) r_write_error_sticky <= 1'b1;"),
    (SCHED_B, 979, "r_read_error_sticky || r_write_error_sticky ||"),
    (SCHED_B, 980, "(w_is_ctrlrd && ctrlrd_error) || (w_is_ctrlwr && ctrlwr_error);"),
    (SCHED_B, 1084, "r_write_error_sticky, r_read_error_sticky"),

    (STR_MACRO, 149, "axi_wr_sram_drain_decoded = '0;"),
    (STR_MACRO, 151, "if (axi_wr_sram_drain && axi_wr_sram_id < NC) begin"),
    (STR_MACRO, 152, "axi_wr_sram_drain_decoded[axi_wr_sram_id] = 1'b1;"),
    (STR_MACRO, 161, "axi_wr_sram_data = axi_wr_sram_data_per_channel[axi_wr_sram_id];"),

    (STR_CORE, 669, "sched_wr_error;"),
    (STR_CORE, 1047, ".sched_wr_error"),
    (STR_CORE, 2130, "obs_flags[11]"),
]


# ---------------------------------------------------------------------------
# Contract sheet: the SOURCE drain interface
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
# SUPERSEDED, pending re-derivation.
#
# build_src_drain_contract() and build_src_drain_kmaps() below describe the
# PRE-FIX source drain path. The defects they document are fixed:
#   * drain_data_avail no longer adds bridge_occupancy (RAPIDS now wraps
#     STREAM's sram_controller, whose unit exposes data_available only)
#   * the arbiter no longer re-consults availability mid-drain, reserves
#     min(cfg_drain_size, avail), pulses drain_req once, retires on the last
#     beat, and subtracts in-flight reservations (w_effective_avail)
# Measured after the fix: beat_conservation 0 beats lost at cfg_drain_size
# 1, 2, 4 and 8; 0 over-drain; 63/63 src and 54/54 snk datapath cells.
#
# These two sheets are NOT repairable by retargeting citations: one K-map axis
# is w_arb_should_advance (a signal that no longer exists), the exclusion
# lambda is justified by "avail = data_available + bridge_occupancy so
# avail >= fifo ALWAYS" (a premise that is now false), and rtl_sop is the
# Boolean form of the deleted FSM. They need re-deriving against the new
# arbiter (axes: w_effective_avail, w_ch_grantable, w_grant_size,
# r_grant_pulse, retire-on-last). Tracked as follow-up work.
#
# The snk ingress / snk error sheets are NOT superseded: that tready vs
# fill_ready defect candidate is still open and snk_data_path_axis_beats.sv
# is untouched.
# ---------------------------------------------------------------------------
def build_src_drain_contract(wb):
    rows = [
        ("Source drain / request", "drain_req[ch]", "1", "out",
         "src_data_path_axis_beats",
         "COMBINATIONAL, asserted for the granted channel while a drain is "
         "active. Consumed by drain_ctrl_beats as rd_valid -- it is a "
         "RESERVATION, not a data pop: it advances the drain controller's "
         "read pointer by the FULL drain_size in one cycle.",
         "A drain_req must only assert when the drain controller's own "
         "data_available >= drain_size. The module asserts this itself "
         f"({DRAIN_B}:176) but only as a simulation $error.",
         f"{SRC_AXIS}:222, wired at {SRC_UNIT}:157. DEFECT: the qualifying "
         f"comparison uses an INFLATED view -- see {KI_DRAIN}."),

        ("Source drain / request", "drain_size[ch]", "8", "out",
         "src_data_path_axis_beats",
         "Set to cfg_drain_size for the whole grant. The drain controller "
         "advances rd_ptr by this amount on the reservation, regardless of "
         "how many beats the arbiter subsequently manages to move.",
         "rd_ptr must never overshoot wr_ptr; an overshoot makes the "
         "wrap-corrected occupancy evaluate to ~DEPTH and is PERMANENT.",
         f"{SRC_AXIS}:223, consumed {DRAIN_B}:102."),

        ("Source drain / accounting", "drain_data_avail[ch]", "SCW", "in",
         "src_sram_controller_unit_beats",
         "The arbiter's view of how much data a channel holds. Computed as "
         "the drain controller's data_available PLUS the latency bridge's "
         "skid occupancy.",
         "Must count each beat exactly once. It does not: a beat that has "
         "moved from the FIFO into the bridge skid is still counted in "
         "data_available (whose rd_ptr only moves on a RESERVATION), so "
         "adding bridge_occupancy counts it a second time.",
         f"{SRC_UNIT}:229 -- THE DEFECT. Over-count is 0..4 "
         f"({LBRIDGE}:185). STREAM carried the identical line and removed "
         f"it; see {STR_UNIT}:282-307 for the prohibition and the deadlock "
         f"it caused. {SNK_UNIT}:229 is the same line, unfixed."),

        ("Source drain / data", "drain_valid[ch] / drain_ready", "1 / 1",
         "in / out", "latency_bridge_beats / src_data_path_axis_beats",
         "The actual per-beat handshake out of the latency bridge. "
         "drain_ready is driven by drain_read = tvalid && tready && "
         "r_arb_active. This path is INDEPENDENT of drain_req: beats leave "
         "one at a time here, while the pointer already jumped drain_size.",
         "Beats actually transferred under a grant must equal the "
         "drain_size reserved for it. Nothing in the RTL enforces this.",
         f"{SRC_AXIS}:229, {SRC_AXIS}:251."),

        ("Source drain / accounting", "rd_ready (drain_ctrl)", "1", "out",
         "drain_ctrl_beats",
         "The drain controller's own not-empty flag (!r_rd_empty). It is "
         "the only signal that could tell a caller the reservation is "
         "unbacked.",
         "Should gate the reservation. It is left UNCONNECTED at the "
         "instantiation, so the caller cannot see it.",
         f"{DRAIN_B}:142 driven, discarded at {SRC_UNIT}:159. STREAM also "
         f"leaves it unconnected -- stream fixes the problem upstream "
         f"instead, at {STR_UNIT}:307 and {STR_WENG}:387."),
    ]
    contract_sheet(
        wb, "Contracts src drain",
        "RAPIDS-beats SOURCE drain path -- signal contracts",
        "The drain path has TWO independent readers of one FIFO: a block "
        "RESERVATION (drain_req/drain_size -> drain_ctrl_beats, which jumps "
        "the read pointer by the full size) and a per-beat POP "
        "(drain_valid/drain_ready via the latency bridge). Nothing "
        "reconciles them. This sheet is the contract for that interface; the "
        "K-map sheet computes the decision surface that breaks it.",
        rows)


# ---------------------------------------------------------------------------
# K-map sheet: the drain-grant decision surface
# ---------------------------------------------------------------------------
def build_src_drain_kmaps(wb):
    km = new_kmap_sheet(wb, "K-maps src drain")
    km.sheet_intro(
        f"src_data_path_axis_beats / drain_ctrl_beats - drain grant ({SRC_AXIS})",
        ["Each grid is computed from a python mirror of the exact RTL "
         "expression (file:line cited, RTL quoted verbatim). Gray order "
         "00 01 11 10; 1-cells green, 0-cells grey, unreachable cells X.",
         "TARGET: rapids TASK-002 item 3, the DRAIN_SIZE>1 source beat drop "
         f"({KI_DRAIN}). The first map is the important one -- it is a map "
         "whose 1-cells include cells that should be impossible, and the "
         "axis that would have excluded them is not an input to the "
         "decision at all."])

    # -- Map 1: the grant qualification, with the missing term as an axis ----
    km.kmap(
        "drain grant fires  (reservation committed)", f"{SRC_AXIS}:197",
        "grant = w_arb_should_advance && r_arb_request[ch] && "
        "(drain_data_avail[check_ch] >= cfg_drain_size); on grant, "
        "r_drain_remaining <= cfg_drain_size and drain_req/drain_size "
        "are driven for the winning channel",
        [("avail_ge_size",
          "drain_data_avail[check_ch] >= cfg_drain_size -- the INFLATED "
          "view: drain controller data_available PLUS latency-bridge skid "
          "occupancy",
          f"{SRC_AXIS}:197 (view built at {SRC_UNIT}:229)"),
         ("fifo_ge_size",
          "drain_data_available >= cfg_drain_size -- the REAL reservation "
          "count inside drain_ctrl_beats, the quantity the read pointer is "
          "actually advanced against. NOT AN INPUT TO THIS DECISION",
          f"{SRC_UNIT}:162, consumed {DRAIN_B}:102"),
         ("should_advance",
          "w_arb_should_advance -- arbiter is free to re-grant this cycle",
          f"{SRC_AXIS}:180"),
         ("req_pending",
          "r_arb_request[ch] = (drain_data_avail[ch] > 0)",
          f"{SRC_AXIS}:169")],
        lambda avail, fifo, adv, req: bool(adv and req and avail),
        "HEALTHY: every green cell would sit at fifo_ge_size=1 -- a "
        "reservation only ever committed against beats that are really in "
        "the drain controller. ACTUAL: fifo_ge_size does not appear in the "
        "expression at all, so the map is INDEPENDENT of it: of the two green "
        "cells, one sits at fifo_ge_size=1 (correct) and one at "
        "fifo_ge_size=0 -- (avail_ge_size=1, fifo_ge_size=0, "
        "should_advance=1, req_pending=1) -- and THAT cell is the defect. "
        "In it the "
        "arbiter commits a cfg_drain_size reservation while the drain "
        "controller holds less than that, drain_ctrl_beats advances rd_ptr "
        f"by the full size anyway ({DRAIN_B}:102, gated only on "
        "!r_rd_empty), and rd_ptr overshoots wr_ptr. Per the module's own "
        f"comment ({DRAIN_B}:156) that corruption is PERMANENT. Those cells "
        "are reachable exactly when bridge_occupancy > 0, which is the "
        "steady state whenever the bridge holds its prefetch. At "
        "cfg_drain_size == 1 the !r_rd_empty gate absorbs the whole "
        "discrepancy, which is why DRAIN_SIZE=1 is clean and is the "
        "shipped workaround.",
        depends_only_on=(
            "these four. cfg_drain_size is a configuration constant held "
            "across the transfer; r_arb_grant_id/check_ch select WHICH "
            "channel is examined, not whether a grant fires; "
            "r_drain_remaining gates the decrement path, not this one. "
            "Critically, NOTHING in the cone reads the drain controller's "
            f"own not-empty flag -- it is driven ({DRAIN_B}:142) and then "
            f"discarded unconnected ({SRC_UNIT}:159)."),
        relations=[
            ("drain_data_avail = data_available + bridge_occupancy, and "
             "occupancy is unsigned, so avail >= fifo ALWAYS. Cells with "
             "fifo_ge_size=1 and avail_ge_size=0 are therefore unreachable "
             "and marked X. The converse is NOT excluded: avail_ge_size=1 "
             "with fifo_ge_size=0 is exactly the over-count window, and "
             "those cells are reachable.",
             lambda avail, fifo, adv, req: not (fifo and not avail),
             f"{SRC_UNIT}:229, {LBRIDGE}:185"),
            ("req_pending is (drain_data_avail > 0) computed from the same "
             "view as avail_ge_size, so for any cfg_drain_size >= 1, "
             "avail_ge_size implies req_pending. Cells with avail_ge_size=1 "
             "and req_pending=0 are unreachable and marked X.",
             lambda avail, fifo, adv, req: not (avail and not req),
             f"{SRC_AXIS}:169")],
        rtl_sop="should_advance & req_pending & avail_ge_size")

    # -- Map 2: the pointer advance, and the detector that does not gate it --
    km.kmap(
        "drain_ctrl read-pointer advance", f"{DRAIN_B}:101",
        "w_read = rd_valid && rd_ready; rd_ready = !r_rd_empty; "
        "advance = w_read && !r_rd_empty, and the advance is by the FULL "
        "rd_size",
        [("rd_valid",
          "the reservation request, driven by drain_req",
          f"{DRAIN_B}:78 (wired {SRC_UNIT}:157)"),
         ("not_empty",
          "!r_rd_empty -- the ONLY gate on the advance; a bare not-empty "
          "test, not a test that rd_size entries are present",
          f"{DRAIN_B}:142"),
         ("size_gt_avail",
          "(AW+1)'(rd_size) > data_available -- the over-drain condition "
          "the module detects and reports",
          f"{DRAIN_B}:176")],
        lambda v, ne, gt: bool(v and ne),
        "The map is INDEPENDENT of size_gt_avail: the pointer advances in "
        "both size_gt_avail cells of the v=1,ne=1 column. The $error at "
        f"{DRAIN_B}:176 fires in exactly one of those two cells and changes "
        "nothing -- it is a DETECTOR, not a guard, and it is wrapped in "
        "translate_off so it exists only in simulation. No DRAIN_SIZE>1 "
        "configuration is present in the checked-in RAPIDS collateral and "
        "no over-drain report exists anywhere in the tree, but the known "
        f"issue records a DRAIN_SIZE=8 A/B run in sim ({KI_DRAIN}), so "
        "whether this $error has ever actually fired is UNESTABLISHED. "
        "Re-running that A/B and grepping for it is the cheapest available "
        "confirmation of the whole mechanism. HEALTHY would be a map that "
        "is 0 wherever size_gt_avail=1.",
        depends_only_on=(
            "these three. rd_size sets the SIZE of the advance, not whether "
            "it happens; the write pointer and wrap bit affect data_available "
            "only through size_gt_avail."),
        rtl_sop="rd_valid & not_empty")

    # -- Map 3: mid-grant abandonment -------------------------------------
    km.kmap(
        "w_arb_should_advance  (grant abandon)", f"{SRC_AXIS}:180",
        "w_arb_should_advance = !r_arb_active || (r_drain_remaining == 0 && "
        "m_axis_tvalid && m_axis_tready) || (r_arb_active && "
        "drain_data_avail[r_arb_grant_id] == 0)",
        [("arb_active",
          "r_arb_active -- a grant is currently held",
          f"{SRC_AXIS}:180"),
         ("rem_zero",
          "r_drain_remaining == 0 -- the committed block is fully drained",
          f"{SRC_AXIS}:181"),
         ("beat",
          "m_axis_tvalid && m_axis_tready -- an egress beat completes this "
          "cycle (this is also drain_read)",
          f"{SRC_AXIS}:229"),
         ("avail_zero",
          "drain_data_avail[r_arb_grant_id] == 0 -- the granted channel's "
          "view has gone empty",
          f"{SRC_AXIS}:182")],
        lambda act, rz, beat, az: bool((not act) or (rz and beat) or (act and az)),
        "The cells at arb_active=1, avail_zero=1, rem_zero=0 are "
        "ABANDONMENT: the arbiter drops a grant while r_drain_remaining is "
        "still non-zero. The reservation for that grant already advanced "
        "the read pointer by the full cfg_drain_size, so the beats between "
        "what was reserved and what was actually moved are skipped -- they "
        "are never emitted and never recovered. This is the second half of "
        "the loss mechanism and it is why the shortfall is not a clean "
        "multiple of DRAIN_SIZE. Note also that the decrement of "
        f"r_drain_remaining sits in the ELSE of this condition "
        f"({SRC_AXIS}:204), so on any advancing cycle a beat can leave "
        "without being counted against the block.",
        depends_only_on=(
            "these four. r_arb_grant_id selects which channel's avail is "
            "examined; the round-robin scan order decides WHO wins the next "
            "grant, not whether the current one ends."),
        relations=[
            ("avail_zero and beat are NOT mutually exclusive: m_axis_tvalid "
             "is r_arb_active && drain_valid[grant], and drain_valid comes "
             "from the latency bridge, which can still be holding beats "
             "after the drain controller's count has reached zero. So a "
             "beat can complete in the same cycle the channel's view reads "
             "empty. Recorded as an INDEPENDENCE note -- no cell is "
             "excluded -- because this same bridge/controller split is the "
             "root of the over-count in map 1.",
             None,
             f"{SRC_AXIS}:251, {SRC_UNIT}:229")],
        rtl_sop="~arb_active | (rem_zero & beat) | (arb_active & avail_zero)")

    # -- The cross-project comparison table --------------------------------
    km.table(
        "STREAM vs RAPIDS: the same fork, one side fixed",
        f"{STR_UNIT}:282-307",
        ["Concern", "STREAM (fixed)", "RAPIDS-beats (as shipped)"],
        [["availability exposed to the requester",
          f"data_available ONLY ({STR_UNIT}:307)",
          f"data_available + bridge_occupancy ({SRC_UNIT}:229)"],
         ["is the double-count documented",
          f"yes, as a prohibition with the deadlock it caused "
          f"({STR_UNIT}:282-301)",
          "no"],
         ["caller-side correction",
          f"w_effective_avail = avail - in-flight drains ({STR_WENG}:387)",
          "none -- the raw view is compared directly to cfg_drain_size"],
         ["drain controller itself",
          "identical module, identical over-drain $error",
          f"identical module, identical over-drain $error ({DRAIN_B}:176)"],
         ["sink path", "n/a", f"same unfixed line at {SNK_UNIT}:229"]],
        note="STREAM carried this exact line too (it is present at "
             "2025-11-11 and 2025-11-24) and removed it later. RAPIDS-beats "
             "was forked from STREAM in 2026-01 and inherited the line, but "
             "not the subsequent fix. The correction is therefore already "
             "written and field-validated one directory over.")


# ---------------------------------------------------------------------------
# Item 5: the sink AXIS ingress admission surface
# ---------------------------------------------------------------------------
def build_snk_ingress_contract(wb):
    rows = [
        ("Sink ingress / AXIS", "s_axis_tready", "1", "out",
         "snk_data_path_axis_beats",
         "COMBINATIONAL: (fill_ready && pending>0) || fill_alloc_req. The "
         "second term carries NO fill_ready conjunct, so tready can assert "
         "while the channel FIFO is backpressuring.",
         "A beat accepted on AXIS must be stored. The only real store is "
         f"fill_valid && fill_ready ({STR_UNIT}:225-226, the FIFO's own "
         "wr_ready), so any accepted beat for which fill_ready was low is "
         "consumed off the network and lost.",
         f"{SNK_AXIS}:204-205 -- THE DEFECT CANDIDATE. See the K-map sheet "
         "for which cell and what is not yet established about reaching it."),

        ("Sink ingress / AXIS", "fill_alloc_req", "1", "out",
         "snk_data_path_axis_beats",
         "s_axis_tvalid && (r_pending_alloc[ch]==0) && "
         "(fill_space_free[ch] >= cfg_alloc_size). A request with NO "
         "handshake: alloc_ctrl_beats' wr_ready is discarded at the "
         "instantiation.",
         "A reservation the allocator refuses must not be counted as "
         "granted. alloc_ctrl advances its pointer only on "
         "w_write && !r_wr_full, so a request arriving while full is "
         "silently dropped -- but r_pending_alloc increments anyway.",
         f"{SNK_AXIS}:189; discarded ready at {STR_UNIT}:136; "
         f"allocator gating at {ALLOC_B}:76 and {ALLOC_B}:86."),

        ("Sink ingress / accounting", "r_pending_alloc[ch]", "16", "internal",
         "snk_data_path_axis_beats",
         "Per-channel count of beats allocated but not yet filled. "
         "Incremented by fill_alloc_size on the REQUEST, decremented by 1 "
         "per stored beat.",
         "Must track the allocator's actual grants. It cannot: the "
         "increment is gated on fill_alloc_req alone, never on acceptance, "
         "and acceptance is not observable in this module.",
         f"{SNK_AXIS}:219-229. STREAM has no equivalent counter at all "
         "(zero occurrences in stream/rtl); it registers its alloc request "
         f"and proves the contract instead -- {STR_RENG}:580, inside an "
         "`ifdef FORMAL` block."),

        ("Sink ingress / accounting", "fill_space_free[ch]", "SCW", "in",
         "snk_sram_controller_unit_beats",
         "The allocator's free-space view, REGISTERED one cycle to break a "
         "combinational path.",
         "The space test is therefore one cycle stale. At cfg_alloc_size==1 "
         "line :222 leaves r_pending_alloc at 0, re-arming fill_alloc_req "
         "every cycle against that stale value.",
         f"{STR_UNIT}:314. ALLOC_SIZE is an 8-bit rw CSR field defaulting "
         "to 0x10, so 1 is a writable value."),

        ("Sink ingress / stats", "dbg_axis_beats_received", "32", "out",
         "snk_data_path_axis_beats",
         "Counts s_axis_tvalid && s_axis_tready.",
         "Counts ACCEPTANCE, not storage -- so a beat lost by the tready "
         "term above is still counted as received.",
         f"{SNK_AXIS}:234."),
    ]
    contract_sheet(
        wb, "Contracts snk ingress",
        "RAPIDS-beats SINK AXIS ingress -- signal contracts",
        "The sink admits network beats through a per-channel reservation "
        "counter (r_pending_alloc) that is incremented on a REQUEST to an "
        "allocator whose grant signal is discarded. This sheet is the "
        "contract for that interface. NOTE: rapids TASK-002 item 5 names this "
        "target 'credit/RDA accounting'; neither exists in the RTL -- there "
        "are zero word-boundary RDA references and no credit machinery "
        "(scheduler_beats.sv says 'No credit management'). The real "
        "decision surface is ingress admission, mapped here.",
        rows)


def build_snk_ingress_kmaps(wb):
    km = new_kmap_sheet(wb, "K-maps snk ingress")
    km.sheet_intro(
        f"snk_data_path_axis_beats - AXIS ingress admission ({SNK_AXIS})",
        ["Computed from a python mirror of the exact RTL expression "
         "(file:line cited, RTL quoted). Gray order 00 01 11 10; 1-cells "
         "green, 0-cells grey, unreachable cells X.",
         "TARGET: rapids TASK-002 item 5, re-scoped. The first map is the one that "
         "matters: it shows an AXIS beat being accepted on a term that does "
         "not include the only signal that decides whether the beat can be "
         "stored."])

    km.kmap(
        "s_axis_tready  (AXIS beat accepted)", f"{SNK_AXIS}:204",
        "s_axis_tready = (fill_ready && (r_pending_alloc[ch] > 0)) || "
        "fill_alloc_req",
        [("fill_ready",
          "the channel FIFO's own wr_ready, muxed per channel -- the ONLY "
          "signal that says the beat can actually be stored",
          f"{STR_UNIT}:226"),
         ("pending_gt0",
          "r_pending_alloc[axis_channel_id] > 0 -- this channel already "
          "holds a reservation",
          f"{SNK_AXIS}:204"),
         ("alloc_req",
          "fill_alloc_req -- a fresh allocation is being requested this "
          "cycle",
          f"{SNK_AXIS}:189")],
        lambda fr, p, ar: bool((fr and p) or ar),
        "HEALTHY: every green cell would sit at fill_ready=1, because the "
        "only actual store is fill_valid && fill_ready "
        f"({STR_UNIT}:225-226). ACTUAL: the single green cell at "
        "fill_ready=0 (alloc_req=1, pending_gt0=0) accepts an AXIS beat "
        "while the FIFO is backpressuring. The handshake completes, the "
        "beat is consumed off the network, and nothing stores it -- and "
        f"{SNK_AXIS}:234 then counts it as received. NOT YET ESTABLISHED: "
        "whether that cell is reachable in practice. It needs fill_ready=0 "
        "simultaneously with fill_space_free >= cfg_alloc_size, and those "
        "are two DIFFERENT counters -- the FIFO's own occupancy versus "
        f"alloc_ctrl's allocation accounting ({ALLOC_B}:141), which is "
        "released only when data leaves the latency bridge. Proving or "
        "excluding that co-occurrence is the open question this map "
        "poses; a directed test driving AXIS into a backpressured channel "
        "would settle it.",
        depends_only_on=(
            "these three. cfg_alloc_size and the stale fill_space_free "
            "enter only through alloc_req; axis_channel_id selects WHICH "
            "channel's counters are read, not whether the beat is taken; "
            "tlast/tstrb/tdest ride the beat but cannot gate it."),
        relations=[
            ("fill_alloc_req requires w_channel_needs_alloc, which is "
             "(r_pending_alloc[ch] == 0). So alloc_req and pending_gt0 "
             "cannot both be true: those cells are unreachable and marked "
             "X. This is why the defect cell necessarily sits at "
             "pending_gt0=0 -- it is the first beat of a packet, the exact "
             "case the RTL comment at :195-196 says the alloc term was "
             "added to protect.",
             lambda fr, p, ar: not (ar and p),
             f"{SNK_AXIS}:185, {SNK_AXIS}:189")],
        rtl_sop="(fill_ready & pending_gt0) | alloc_req")

    km.kmap(
        "fill_valid  (beat offered to the FIFO)", f"{SNK_AXIS}:197",
        "fill_valid = s_axis_tvalid && ((r_pending_alloc[ch] > 0) || "
        "(w_channel_needs_alloc && w_channel_has_space))",
        [("tvalid",
          "s_axis_tvalid -- the network is offering a beat",
          f"{SNK_AXIS}:197"),
         ("pending_gt0",
          "r_pending_alloc[axis_channel_id] > 0",
          f"{SNK_AXIS}:198"),
         ("needs_and_space",
          "w_channel_needs_alloc && w_channel_has_space -- allocating this "
          "cycle instead",
          f"{SNK_AXIS}:199")],
        lambda tv, p, ns: bool(tv and (p or ns)),
        "This map is CORRECT and is included as the contrast. fill_valid "
        "omits fill_ready, which is right for a valid/ready producer -- the "
        "FIFO's wr_ready decides the transfer. The hazard is not here; it "
        "is that s_axis_tready (map 1) does NOT follow the same discipline, "
        "so the AXIS side and the FIFO side can disagree about whether the "
        "beat moved.",
        depends_only_on=(
            "these three. The same channel-select and config terms as map 1 "
            "enter only through needs_and_space."),
        relations=[
            ("needs_and_space contains w_channel_needs_alloc = "
             "(r_pending_alloc[ch] == 0), so it cannot be true while "
             "pending_gt0 is. Those cells are unreachable and marked X.",
             lambda tv, p, ns: not (ns and p),
             f"{SNK_AXIS}:185")],
        rtl_sop="tvalid & (pending_gt0 | needs_and_space)")

    km.kmap(
        "r_pending_alloc credited", f"{SNK_AXIS}:219",
        "the += fill_alloc_size branch is taken on "
        "(fill_alloc_req && fill_alloc_id == ch)",
        [("alloc_req_ch",
          "fill_alloc_req targeting this channel",
          f"{SNK_AXIS}:219"),
         ("consume",
          "fill_valid && fill_ready && fill_id == ch -- a beat is stored "
          "this cycle (selects the -1 variant, not whether we credit)",
          f"{SNK_AXIS}:222"),
         ("alloc_granted",
          "alloc_ctrl's wr_ready = !r_wr_full -- whether the allocator "
          "ACTUALLY took the reservation. NOT AN INPUT: this wire is "
          "discarded at the instantiation",
          f"{ALLOC_B}:137, discarded at {STR_UNIT}:136")],
        lambda areq, cons, granted: bool(areq),
        "The map is INDEPENDENT of alloc_granted, which is the finding. "
        f"alloc_ctrl advances its pointer only on w_write && !r_wr_full "
        f"({ALLOC_B}:76, {ALLOC_B}:86), so a request arriving while the "
        "allocator is full is silently dropped -- yet r_pending_alloc is "
        "credited the full fill_alloc_size regardless. The two green cells "
        "at alloc_granted=0 are where the datapath believes it holds space "
        "the allocator never gave it. HEALTHY would be a map that is 0 "
        "wherever alloc_granted=0, which requires routing wr_ready back -- "
        "it is driven and available, just not connected.",
        depends_only_on=(
            "these three. fill_alloc_size sets the SIZE of the credit, not "
            "whether it is taken; the per-channel loop index only selects "
            "which counter is updated."),
        relations=[
            ("alloc_granted is not observable from this module at all -- "
             "the port is left unconnected, so no cell can be excluded on "
             "its value. Recorded as an INDEPENDENCE note precisely because "
             "the independence IS the defect: an input that should "
             "constrain the decision has been made unable to.",
             None,
             f"{STR_UNIT}:136")],
        rtl_sop="alloc_req_ch")

    km.table(
        "STREAM vs RAPIDS: how each qualifies an allocation",
        f"{STR_RENG}:580",
        ["Concern", "STREAM", "RAPIDS-beats sink"],
        [["local reservation counter",
          "none (zero r_pending_alloc in stream/rtl)",
          f"r_pending_alloc, credited on request ({SNK_AXIS}:225)"],
         ["allocation tied to an accepted handshake",
          f"yes, and PROVEN: alloc_req |-> $past(arvalid && arready) "
          f"({STR_RENG}:580, inside `ifdef FORMAL`)",
          "no property, and the allocator's wr_ready is discarded"],
         ["ingress ready includes the store-enable",
          "n/a -- stream's fill side is an AXI read engine, not an AXIS port",
          f"NO: s_axis_tready ORs in fill_alloc_req ({SNK_AXIS}:204)"],
         ["allocator module",
          "stream_alloc_ctrl",
          "alloc_ctrl_beats -- byte-identical to stream's apart from the "
          "module name and subsystem comment"]],
        note="RAPIDS' sink network side has no STREAM counterpart, so none "
             "of STREAM's proofs transfer here. That is exactly why "
             "rapids TASK-002 ranks this the most exposed area, and it is the "
             "first sheet in this workbook with no fixed STREAM original "
             "to compare against.")


# ---------------------------------------------------------------------------
# Item 4: scheduler issue/commit gating and timeout escalation
# ---------------------------------------------------------------------------
def build_sched_commit_kmaps(wb):
    km = new_kmap_sheet(wb, "K-maps sched commit")
    km.sheet_intro(
        f"scheduler_beats - completion gating and timeout escalation ({SCHED_B})",
        ["Computed from a python mirror of the exact RTL expression "
         "(file:line cited, RTL quoted). Gray order 00 01 11 10; 1-cells "
         "green, 0-cells grey, unreachable cells X.",
         "TARGET: rapids TASK-002 item 4. Unlike the alloc/drain FUBs (byte-"
         "identical to STREAM's), this module DIVERGED: 1150 lines against "
         f"STREAM's 1390. Map 1 is where the divergence lives, and it is "
         f"the cone of the resolved wedge in {KI_STALL}."])

    km.kmap(
        "CH_XFER_DATA exit  (DATA descriptor)", f"{SCHED_B}:418",
        "w_exec_complete = w_is_data ? w_transfer_complete : w_ctrl_complete, "
        "with w_transfer_complete = w_read_complete && w_write_complete and "
        "w_write_complete = (r_write_beats_to_commit == 0)",
        [("read_complete",
          "r_read_beats_remaining == 0 -- all source beats read",
          f"{SCHED_B}:771"),
         ("write_issued",
          "r_write_beats_remaining == 0 -- all destination beats ISSUED. "
          "This is STREAM's completion term; in RAPIDS it is NOT an input "
          "to this decision",
          f"{STR_SCHED}:902"),
         ("write_committed",
          "r_write_beats_to_commit == 0 -- all destination beats COMMITTED "
          "(B responses accounted)",
          f"{SCHED_B}:775"),
         ("is_data",
          "w_is_data -- DATA descriptor (control opcodes exit on "
          "w_ctrl_complete instead, outside this map)",
          f"{SCHED_B}:779")],
        lambda rc, wi, wc, isd: bool(isd and rc and wc),
        "The map is INDEPENDENT of write_issued, which is the divergence. "
        f"STREAM exits this state on ISSUE ({STR_SCHED}:909, "
        f"w_transfer_complete = w_read_complete && w_write_issued) and "
        f"defers the commit-wait to CH_COMPLETE, and only for the LAST "
        f"descriptor ({STR_SCHED}:542). RAPIDS waits for COMMITS here, on "
        f"EVERY descriptor ({SCHED_B}:776), and its CH_COMPLETE carries no "
        "commit gate at all. Two consequences. (1) Chain throughput: RAPIDS "
        "cannot advance to the next descriptor until the current one's B "
        "responses land; STREAM streams through. (2) A lost commit surfaces "
        "on ANY descriptor in RAPIDS rather than only the last. NOT a "
        "tolerance difference: under a lost commit NEITHER design recovers "
        "-- write_committed never reaches 1, no green cell is ever entered, "
        f"the channel never reaches CH_IDLE and scheduler_idle "
        f"({SCHED_B}:1105) never asserts. That is the wedge recorded in "
        f"{KI_STALL} (ILA: r_write_beats_to_commit=1, "
        "r_write_beats_remaining=0).",
        depends_only_on=(
            "these four for a DATA descriptor. The timeout path reaches the "
            "FSM through a separate w_hard_error/w_timeout_escalate branch "
            f"evaluated BEFORE this case ({SCHED_B}:978); channel reset "
            "overrides both."),
        relations=[
            ("A beat can only commit after it has been issued, so "
             "committed <= issued, hence r_write_beats_to_commit >= "
             "r_write_beats_remaining. write_committed therefore IMPLIES "
             "write_issued, and cells with write_committed=1 and "
             "write_issued=0 are unreachable and marked X. This is exactly "
             "why waiting on commits is strictly later than waiting on "
             "issues, never earlier.",
             lambda rc, wi, wc, isd: not (wc and not wi),
             f"{SCHED_B}:775, {STR_SCHED}:902")],
        rtl_sop="is_data & read_complete & write_committed")

    km.kmap(
        "sched_wr_valid  (request more writes)", f"{SCHED_B}:858",
        "sched_wr_valid = (state == CH_XFER_DATA) && w_is_data && "
        "(r_write_beats_remaining != 0) && !w_write_complete && "
        "!w_sched_wr_completing_this_cycle && !w_wr_need_base",
        [("xfer_and_data",
          "r_current_state == CH_XFER_DATA && w_is_data",
          f"{SCHED_B}:858"),
         ("beats_to_issue",
          "r_write_beats_remaining != 0 -- the explicit issue-count gate",
          f"{SCHED_B}:859"),
         ("write_committed",
          "w_write_complete -- all beats committed",
          f"{SCHED_B}:860"),
         ("completing_now",
          "w_sched_wr_completing_this_cycle -- look-ahead de-assert",
          f"{SCHED_B}:861"),
         ("need_base",
          "w_wr_need_base -- stream TASK-101 run-boundary stall",
          f"{SCHED_B}:862")],
        lambda xd, bti, wc, cn, nb: bool(xd and bti and not wc and not cn and not nb),
        "The issue-count gate is what stops a spurious garbage AW during "
        f"the commit-wait ({SCHED_B}:853-857). Note the !w_write_complete "
        "term is LOGICALLY REDUNDANT here: beats_to_issue=1 already forces "
        "write_committed=0 (see the relation), so it can never be the "
        "deciding term -- every cell where it would matter is marked X. It "
        "is belt-and-braces, not live logic, and a future reader should not "
        "assume removing it changes behaviour. STREAM carries the same "
        f"5-term conjunction with a near-identical comment "
        f"({STR_SCHED}:1004-1008), so this gate did NOT diverge.",
        depends_only_on=(
            "these five. sched_wr_addr/beats are payload, not qualifiers; "
            "sched_wr_ready is the engine's backpressure and deliberately "
            "does not gate the request."),
        relations=[
            ("r_write_beats_to_commit >= r_write_beats_remaining always "
             "(commits trail issues), so beats_to_issue (remaining != 0) "
             "implies to_commit != 0, i.e. write_committed = 0. Cells with "
             "both beats_to_issue=1 and write_committed=1 are unreachable "
             "and marked X.",
             lambda xd, bti, wc, cn, nb: not (bti and wc),
             f"{SCHED_B}:775, {SCHED_B}:859")],
        rtl_sop="xfer_and_data & beats_to_issue & ~write_committed "
                "& ~completing_now & ~need_base")

    km.kmap(
        "w_timeout_escalate  (soft -> fatal)", f"{SCHED_B}:970",
        "w_timeout_escalate = (cfg_sched_timeout_limit != 0) && "
        "(r_timeout_strikes >= cfg_sched_timeout_limit)",
        [("timeout_enable",
          "cfg_sched_timeout_enable -- the feature's enable bit; gates "
          "w_timeout_expired, which is the ONLY thing that increments "
          "strikes",
          f"{SCHED_B}:965"),
         ("counter_expired",
          "r_timeout_counter >= cfg_sched_timeout_cycles -- this window "
          "elapsed",
          f"{SCHED_B}:966"),
         ("limit_nonzero",
          "cfg_sched_timeout_limit != 0 -- escalation armed (0 = never "
          "escalate, pure soft timeout)",
          f"{SCHED_B}:970"),
         ("strikes_at_limit",
          "r_timeout_strikes >= cfg_sched_timeout_limit -- enough "
          "consecutive windows with no write progress",
          f"{SCHED_B}:971")],
        lambda en, cnt, lim, strk: bool(lim and strk),
        "Escalation drives the channel into sticky CH_ERROR "
        f"({SCHED_B}:380), so the green cells are fatal transitions. The "
        "map is INDEPENDENT of timeout_enable, and that is worth a look: "
        "strikes are cleared only by channel reset, by reaching CH_IDLE, or "
        f"by real write progress ({SCHED_B}:932-936) -- never by the enable "
        "bit going low. So a channel that has already accumulated strikes "
        "and then has cfg_sched_timeout_enable cleared by software still "
        "has w_timeout_escalate asserted and still wedges into CH_ERROR. "
        "NOT YET ESTABLISHED whether any host sequence actually clears "
        "enable mid-transfer; the map states the exposure rather than "
        "asserting the bug. A directed test that raises strikes, clears "
        "enable, and checks the channel does not enter CH_ERROR would "
        "settle it.",
        depends_only_on=(
            "these four. cfg_sched_timeout_cycles enters only through "
            "counter_expired; the counter's own 4-way arming priority "
            f"({SCHED_B}:920-928) decides WHEN a window elapses, not "
            "whether escalation fires once strikes are banked."),
        relations=[
            ("(r_timeout_strikes >= cfg_sched_timeout_limit) is "
             "unconditionally TRUE when cfg_sched_timeout_limit is 0, "
             "because the counter is unsigned. So limit_nonzero=0 forces "
             "strikes_at_limit=1, and cells with both 0 are unreachable "
             "and marked X. This is precisely why the explicit != 0 guard "
             "exists: without it, disabling escalation would enable it.",
             lambda en, cnt, lim, strk: not ((not lim) and (not strk)),
             f"{SCHED_B}:970, {SCHED_B}:971")],
        rtl_sop="limit_nonzero & strikes_at_limit")

    km.table(
        "STREAM vs RAPIDS scheduler: where the commit-wait sits",
        f"{SCHED_B}:418",
        ["Concern", "STREAM scheduler.sv (1390 lines)",
         "RAPIDS scheduler_beats.sv (1150 lines)"],
        [["CH_XFER_DATA exit term",
          f"w_write_issued -- issue-based ({STR_SCHED}:909)",
          f"w_write_complete -- commit-based ({SCHED_B}:776)"],
         ["formal property asserts",
          f"(w_read_complete && w_write_issued) ({STR_SCHED}:1376)",
          f"(w_read_complete && w_write_complete) ({SCHED_B}:1136)"],
         ["CH_COMPLETE commit gate",
          f"yes, last descriptor only ({STR_SCHED}:542); chained advances "
          "immediately",
          f"none ({SCHED_B}:424-432)"],
         ["chain streams without waiting for B",
          "yes", "no -- every descriptor waits for commits"],
         ["recovers from a lost commit",
          "no -- hangs in CH_COMPLETE",
          "no -- hangs in CH_XFER_DATA"],
         ["sched_wr_valid issue-count gate",
          f"same 5 terms ({STR_SCHED}:1004-1008)",
          f"same 5 terms ({SCHED_B}:858-862)"]],
        note="The alloc/drain FUBs are byte-identical between the two "
             "projects; this scheduler is not. The divergence is narrow -- "
             "one term in the completion wire and the placement of the "
             "commit-wait -- but it changes chain behaviour and which "
             "descriptor exposes a lost commit. Neither side has a recovery "
             f"path; see {KI_STALL}, whose section 6a found the write "
             "engine byte-identical and therefore the under-count risk "
             "shared.")


# ---------------------------------------------------------------------------
# Items 1-2: sink error reporting, and the shared drain port
# ---------------------------------------------------------------------------
def build_snk_error_contract(wb):
    rows = [
        ("Sink errors / engine", "sched_wr_error (engine output)", "NC", "out",
         "axi_write_engine_beats",
         "Sticky per-channel flag, set on any B beat whose response is not "
         "OKAY: m_axi_bvalid && m_axi_bready && (m_axi_bresp != 2'b00), "
         "channel taken from BID.",
         "A SLVERR or DECERR on a write response must reach the channel FSM "
         "and fault the channel. Since 2026-09-25 it does.",
         f"{WR_ENG_B}:951 sets it, :955 latches per channel, :964 drives "
         f"the port declared at :144. The detection is REAL and complete."),

        ("Sink errors / plumbing", "sched_wr_error (macro net)", "NC",
         "internal", "rapids_snk_beats",
         "Driven from the sink data path, which now exports the engine's "
         "sticky flag. FIXED 2026-09-25: this net was previously "
         "`assign sched_wr_error = '0;` under a TODO claiming the write "
         "engine did not support error reporting -- which was false.",
         "Must carry the engine's per-channel flag, not a constant. It now "
         "does, so w_hard_error's sched_wr_error term and "
         "r_write_error_sticky are live on the sink.",
         f"{SNK_MACRO}:640 connects it, :514 feeds the "
         f"scheduler_group_array_beats instantiated at :344. The data path "
         f"exports it at {SNK_DP}:275."),

        ("Sink errors / plumbing", "sched_rd_error (macro net)", "NC",
         "internal", "rapids_snk_beats",
         "Tied to '0 at the instantiation.",
         "LEGITIMATE: the sink has no AXI read engine, and its read "
         "done-strobes are tied off in the same block. Listed so a reader "
         "does not mistake it for the same defect as the row above.",
         f"{SNK_MACRO}:513. Contrast {SRC_MACRO}:491, where the SOURCE wires "
         f"a real sched_rd_error, and :492 where the source ties its unused "
         f"write error off for the mirror-image legitimate reason."),

        ("Sink errors / scheduler", "r_write_error_sticky", "1", "internal",
         "scheduler_beats",
         "Latched high on any cycle sched_wr_error is high; cleared on reset "
         "and channel reset.",
         "Was constant 0 on the sink while its only source was tied off; "
         "live since 2026-09-25. Feeds w_hard_error AND the MonBus error "
         "packet, so the sink's error telemetry works now too.",
         f"{SCHED_B}:944 latches it, :979 uses it in w_hard_error, :1084 "
         f"packs it into a monitor packet."),

        ("Sink errors / scheduler", "w_hard_error", "1", "internal",
         "scheduler_beats",
         "7-term OR: descriptor_error, sched_rd_error, sched_wr_error, both "
         "stickies, and the two control-engine error terms. Drives the "
         "sticky CH_ERROR transition.",
         "2 of the 7 terms are still constant 0 on the sink "
         "(sched_rd_error and r_read_error_sticky -- legitimately, there is "
         "no AXI read engine here). Before 2026-09-25 it was 4, and a DATA "
         "descriptor reduced to descriptor_error alone.",
         f"{SCHED_B}:978-980, consumed at :380. Live terms come from "
         f"{SG}:264 (descriptor_engine_beats) and {CTRLRD}:437."),

        ("Sink SRAM / drain port", "drain_read / drain_id", "1 / CIW", "in",
         "snk_sram_controller_beats",
         "A single read strobe and a single channel index, decoded one-hot "
         "to select which channel is drained, with one data mux on the same "
         "index.",
         "At most one channel can be drained per cycle, by construction. "
         "This is the interface, not an omission inside the module.",
         f"{SNK_SRAM}:147-148 decode, :157 mux. See {KI_SSC} -- the "
         f"limitation is structural, which is why a keyword search for "
         f"\"single read\" finds nothing."),
    ]
    contract_sheet(
        wb, "Contracts snk errors",
        "RAPIDS-beats SINK error reporting and drain port -- signal contracts",
        "rapids TASK-002 items 1 and 2. Item 1: the write engine detects bad B "
        "responses per channel, and the sink used to throw that detection "
        "away, leaving two fatal-error terms provably dead. FIXED 2026-09-25 "
        "-- the maps below show the repaired cone, with the defect kept as a "
        "recorded relation so the history is not lost. Item 2: the sink SRAM "
        "drain port serves one channel per cycle by construction. Both were "
        "filed against retired pre-beats files, so only their anchors were "
        f"stale; see {KI_SDP} and {KI_SSC}.",
        rows)


def build_snk_error_kmaps(wb):
    km = new_kmap_sheet(wb, "K-maps snk errors")
    km.sheet_intro(
        f"rapids_snk_beats / scheduler_beats - fatal-error entry ({SCHED_B}:978)",
        ["Computed from a python mirror of the exact RTL expression "
         "(file:line cited, RTL quoted). Gray order 00 01 11 10; 1-cells "
         "green, 0-cells grey, unreachable cells X.",
         "TARGET: rapids TASK-002 items 1 and 2. READ THE X CELLS FIRST. "
         "Normally a don't-care marks a state that cannot physically occur. "
         "In map 1 they mark states the INSTANTIATION forbids by tying an "
         "input to a constant. That used to be four axes; two of those "
         "tie-offs were a defect, fixed 2026-09-25, so the map now shows 16 "
         "X cells rather than 28. The surviving exclusion is legitimate: "
         "the sink has no AXI read engine."])

    km.kmap(
        "w_hard_error  (on the SINK instance)", f"{SCHED_B}:978",
        "w_hard_error = descriptor_error || sched_rd_error || sched_wr_error "
        "|| r_read_error_sticky || r_write_error_sticky || "
        "(w_is_ctrlrd && ctrlrd_error) || (w_is_ctrlwr && ctrlwr_error)",
        [("descriptor_error",
          "descriptor fetch/validity fault, from descriptor_engine_beats "
          "inside the scheduler group -- LIVE on the sink",
          f"{SG}:264, wired :289"),
         ("wr_error",
          "sched_wr_error as the scheduler sees it",
          f"{SCHED_B}:163"),
         ("wr_sticky",
          "r_write_error_sticky -- latched from wr_error and nothing else",
          f"{SCHED_B}:944"),
         ("rd_path",
          "sched_rd_error || r_read_error_sticky, folded: both derive from "
          "the same input",
          f"{SCHED_B}:162, :943"),
         ("ctrl_err",
          "(w_is_ctrlrd && ctrlrd_error) || (w_is_ctrlwr && ctrlwr_error) -- "
          "LIVE, but only for CTRL descriptors",
          f"{SCHED_B}:980, driven {CTRLRD}:437")],
        lambda de, wr, ws, rd, ce: bool(de or wr or ws or rd or ce),
        "16 of 32 cells are unreachable, and NOT for the usual reason: they "
        "are states the INSTANTIATION forbids by tying an input to a "
        "constant, not states that cannot physically occur. The one "
        "surviving exclusion is legitimate -- the sink has no AXI read "
        "engine, so rd_path is identically 0. Of the 16 reachable cells 15 "
        "are green: any single error term faults the channel. COMPARE THE "
        "PREVIOUS VERSION: until 2026-09-25 wr_error and wr_sticky were ALSO "
        "tied to 0, only 4 cells were reachable, and a SLVERR or DECERR on "
        "every beat of a transfer produced no fatal error, no CH_ERROR "
        f"({SCHED_B}:380) and no error bit in the MonBus packet "
        f"({SCHED_B}:1084) -- the channel reported success. The detection was "
        f"always real ({WR_ENG_B}:951/:955/:964); only the wiring was "
        "missing, and it is now in place.",
        depends_only_on=(
            "these five. The timeout path is a SEPARATE disjunct at the "
            f"FSM ({SCHED_B}:380) and is mapped below; channel reset "
            "overrides both."),
        relations=[
            ("LEGITIMATE tie-off: the sink has no AXI read engine, so "
             "sched_rd_error is tied to '0 at the instantiation and "
             "r_read_error_sticky can never latch. rd_path is therefore "
             "identically 0 on this instance and every cell with rd_path=1 "
             "is unreachable. The sink's read done-strobes are tied off in "
             "the same block, which is what makes this legitimate rather "
             "than a second defect.",
             lambda de, wr, ws, rd, ce: not rd,
             f"{SNK_MACRO}:513"),
            ("HISTORY, no longer an exclusion: until 2026-09-25 "
             "sched_wr_error was assigned a constant '0 in rapids_snk_beats "
             "under a TODO claiming the write engine did not support error "
             "reporting -- which was false. wr_error and wr_sticky were "
             "therefore identically 0 and 28 of these 32 cells were "
             "unreachable, leaving a surface spanned by descriptor_error and "
             "ctrl_err alone. The sink data path now exports the engine's "
             "flag and the tie-off is gone, so those cells are REACHABLE and "
             "no predicate excludes them. Recorded as an independence note "
             "so the repair is visible in the map, not only in git.",
             None,
             f"{SNK_MACRO}:640, path :514 -> {SG_ARR}:541 -> {SG}:411 -> "
             f"{SCHED_B}:163; exported at {SNK_DP}:275")],
        rtl_sop="descriptor_error | wr_error | wr_sticky | rd_path | ctrl_err")

    km.kmap(
        "CH_ERROR entry  (on the SINK instance)", f"{SCHED_B}:380",
        "if (w_hard_error || w_timeout_escalate) w_next_state = CH_ERROR",
        [("descriptor_error",
          "the one always-live hard-error term on the sink",
          f"{SG}:289"),
         ("wr_error",
          "sched_wr_error -- a bad write response reaching the scheduler",
          f"{SCHED_B}:163"),
         ("ctrl_err",
          "control-engine error; live only for CTRL opcodes",
          f"{SCHED_B}:980"),
         ("timeout_escalate",
          "w_timeout_escalate -- soft timeout promoted after "
          "cfg_sched_timeout_limit consecutive windows",
          f"{SCHED_B}:970")],
        lambda de, wr, ce, esc: bool(de or wr or ce or esc),
        "No cell is excluded here any more: all four routes into sticky "
        "CH_ERROR are live on the sink since the wr_error wiring was "
        "restored on 2026-09-25. 15 of 16 cells are green -- any one fault "
        "takes the channel to CH_ERROR. The wr_error column is the part that "
        "was dead: previously every cell with it set was unreachable, so a "
        "bad write response could not fault the channel at all. One "
        "consequence is worth keeping in view even now: a SLVERR arrives "
        "WITH a B response, and the commit strobe is gated on bvalid/bready "
        f"and BID with no bresp test ({WR_ENG_B}:898), so it still counts as "
        f"write progress and resets the timeout counter ({SCHED_B}:920). The "
        "error path catches it now. A burst that returns no B at all is a "
        "different mechanism and is NOT this cone's job: AXI transaction "
        "timeouts are detected by the monitor layer by design "
        "(rtl/amba/monitor/axi_monitor_timer.sv plus "
        "axi_monitor_reporter_timeout.sv, gated by cfg_timeout_enable), not by "
        "a counter in the engine. NOT YET ESTABLISHED: no test drives a sink "
        "SLVERR today; a directed test returning SLVERR on one burst and "
        "checking the channel faults would close the loop.",
        depends_only_on=(
            "these four, plus channel reset which takes priority over the "
            f"whole branch ({SCHED_B}:369-370)."),
        relations=[
            ("wr_error USED to be identically 0 on this instance (see map 1), "
             "which made every cell carrying it unreachable. The tie-off is "
             "gone, so nothing is excluded here now. Kept as an independence "
             "note because the axis is only interesting once you know it was "
             "dead.",
             None,
             f"{SNK_MACRO}:640")],
        rtl_sop="descriptor_error | wr_error | ctrl_err | timeout_escalate")

    km.kmap(
        "drain_read_decoded[ch]  (which channel drains)", f"{SNK_SRAM}:147",
        "drain_read_decoded = '0; if (drain_read && drain_id < NC) "
        "drain_read_decoded[drain_id] = 1'b1;",
        [("drain_read",
          "the consumer asserts a drain this cycle",
          f"{SNK_SRAM}:147"),
         ("id_match",
          "drain_id selects THIS channel",
          f"{SNK_SRAM}:148"),
         ("id_in_range",
          "drain_id < NC",
          f"{SNK_SRAM}:147"),
         ("ch_has_data",
          "this channel actually holds drainable data -- NOT an input to "
          "the decode",
          f"{SNK_SRAM}:157")],
        lambda dr, im, ir, hd: bool(dr and im and ir),
        "rapids TASK-002 item 2, and the map states the limitation exactly. Two "
        "things are visible. (1) The decode is INDEPENDENT of ch_has_data: "
        "a drain is decoded to whichever channel drain_id names, whether or "
        "not it holds data -- safety is entirely the consumer's "
        "responsibility. (2) More importantly, drain_id is a SINGLE index "
        "and drain_read a SINGLE bit, so at most one channel's decode can "
        "assert in any cycle. Concurrent drains are excluded by the port "
        "shape, not by anything in this expression, which is why searching "
        "the module for a 'single read' guard finds nothing -- there is no "
        "logic to find. Supporting concurrency would mean widening "
        "drain_read/drain_id/drain_data to per-channel vectors. The fill "
        f"side has the identical shape. This is an architectural "
        f"simplification, not a bug ({KI_SSC} keeps it Low priority).",
        depends_only_on=(
            "these four. NC is a parameter; the other channels' state "
            "cannot influence this channel's decode, which is the whole "
            "point."),
        relations=[
            ("id_match means drain_id equals this channel's index, and a "
             "channel index is by definition < NC, so id_match implies "
             "id_in_range. Cells with id_match=1 and id_in_range=0 are "
             "unreachable and marked X.",
             lambda dr, im, ir, hd: not (im and not ir),
             f"{SNK_SRAM}:147")],
        rtl_sop="drain_read & id_match & id_in_range")

    km.table(
        "How the sink's write error reaches the scheduler (FIXED 2026-09-25)",
        f"{SNK_MACRO}:640",
        ["Stage", "What happens to the error", "Citation"],
        [["axi_write_engine_beats",
          "DETECTED: bad B response latched sticky per channel, port driven",
          f"{WR_ENG_B}:951 / :955 / :964"],
         ["snk_data_path_beats",
          "EXPORTED: was connected to an empty port under \"Error and Debug "
          "(unconnected at this level)\"; now declares a sched_wr_error "
          "output and drives it",
          f"{SNK_DP}:275"],
         ["snk_data_path_axis_beats",
          "PASSED THROUGH: gained a matching sched_wr_error output. Before "
          "the fix neither wrapper declared one, so the flag could not "
          "propagate even in principle",
          "snk_data_path_axis_beats.sv port list"],
         ["rapids_snk_beats",
          "CONNECTED: the assign sched_wr_error = '0 tie-off and its false "
          "TODO are deleted; the net is driven by the data path",
          f"{SNK_MACRO}:640 -> :514"],
         ["scheduler_beats",
          "LIVE TERMS: sched_wr_error and r_write_error_sticky now carry the "
          "engine's flag, in both w_hard_error and the MonBus error packet",
          f"{SCHED_B}:944 / :979 / :1084"],
         ["STREAM, for comparison",
          "WIRED: declared, connected, no tie-off, and surfaced for "
          "observability as obs_flags[11]",
          f"{STR_CORE}:669 / :1047 / :2130"]],
        note="Applied 2026-09-25, mirroring what the RAPIDS source path "
             f"({SRC_MACRO}:491) and STREAM already did. Verilator lint is "
             "warning-for-warning identical to the pre-change baseline. Gap 1 "
             "of the known issue is NOT fixed: there is still no AXI "
             "transaction timeout in axi_write_engine_beats, and that file is "
             f"byte-identical with STREAM's. See {KI_SDP}.")


def main():
    verify_citations(CITES, REPO)
    wb = openpyxl.Workbook()
    del wb[wb.sheetnames[0]]           # drop the default sheet

    build_src_drain_contract(wb)
    build_src_drain_kmaps(wb)
    build_snk_ingress_contract(wb)
    build_snk_ingress_kmaps(wb)
    build_sched_commit_kmaps(wb)
    build_snk_error_contract(wb)
    build_snk_error_kmaps(wb)

    wb.save(XLSX)
    print(f"wrote {XLSX}")
    for name in wb.sheetnames:
        print(" ", name)


if __name__ == "__main__":
    main()

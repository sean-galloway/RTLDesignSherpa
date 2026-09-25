#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generate rapids_signal_contracts.xlsx for the current RAPIDS-beats RTL.

Built on the shared machinery in bin/kmaps (TOOLING-KMAP step 5), the same
package the STREAM generator uses. What lives here is RAPIDS-specific: the RTL
path constants, the CITES registry, and the build_* sheet builders.

First target (TASK-002 item 3) is the `drain_size_gt1` SOURCE beat drop
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
LBRIDGE = "projects/components/dmas/rapids/rtl/fub_beats/latency_bridge_beats.sv"

# STREAM, cited as the CONTRAST: same fork, defect already fixed there.
STR_UNIT = "projects/components/dmas/stream/rtl/fub/sram_controller_unit.sv"
STR_WENG = "projects/components/dmas/stream/rtl/fub/axi_write_engine.sv"

KI_DRAIN = ("projects/components/dmas/rapids/known_issues/active/"
            "drain_size_gt1_source_beat_drop.md")

# ---------------------------------------------------------------------------
# Citation registry: (path-relative-to-repo, line, snippet-on-that-line).
# Verified against the RTL before the workbook is written.
# ---------------------------------------------------------------------------
CITES = [
    (SRC_AXIS, 169, "r_arb_request[ch] = (drain_data_avail[ch] > 0)"),
    (SRC_AXIS, 180, "assign w_arb_should_advance = !r_arb_active ||"),
    (SRC_AXIS, 181, "(r_drain_remaining == 0 && m_axis_tvalid && m_axis_tready) ||"),
    (SRC_AXIS, 182, "(r_arb_active && drain_data_avail[r_arb_grant_id] == 0);"),
    (SRC_AXIS, 197, "if (drain_data_avail[check_ch] >= cfg_drain_size) begin"),
    (SRC_AXIS, 200, "r_drain_remaining <= cfg_drain_size;"),
    (SRC_AXIS, 204, "end else if (drain_read && drain_valid[r_arb_grant_id]) begin"),
    (SRC_AXIS, 222, "drain_req[r_arb_grant_id] = 1'b1;"),
    (SRC_AXIS, 223, "drain_size[r_arb_grant_id] = cfg_drain_size;"),
    (SRC_AXIS, 229, "assign drain_read = m_axis_tvalid && m_axis_tready && r_arb_active;"),
    (SRC_AXIS, 251, "assign m_axis_tvalid = r_arb_active && drain_valid[r_arb_grant_id];"),

    (SRC_UNIT, 129, ".rd_valid           (drain_valid && drain_ready),"),
    (SRC_UNIT, 157, ".rd_valid           (drain_req),"),
    (SRC_UNIT, 158, ".rd_size            (drain_size),"),
    (SRC_UNIT, 159, ".rd_ready           ()"),
    (SRC_UNIT, 162, ".data_available     (drain_data_available),"),
    (SRC_UNIT, 229, "assign drain_data_avail = drain_data_available + SCW'(bridge_occupancy);"),
    (SNK_UNIT, 229, "assign drain_data_avail = drain_data_available + SCW'(bridge_occupancy);"),

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
]


# ---------------------------------------------------------------------------
# Contract sheet: the SOURCE drain interface
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
         "TARGET: TASK-002 item 3, the DRAIN_SIZE>1 source beat drop "
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


def main():
    verify_citations(CITES, REPO)
    wb = openpyxl.Workbook()
    del wb[wb.sheetnames[0]]           # drop the default sheet

    build_src_drain_contract(wb)
    build_src_drain_kmaps(wb)

    wb.save(XLSX)
    print(f"wrote {XLSX}")
    for name in wb.sheetnames:
        print(" ", name)


if __name__ == "__main__":
    main()

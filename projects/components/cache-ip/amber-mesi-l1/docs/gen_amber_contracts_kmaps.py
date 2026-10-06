#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generate amber_signal_contracts.xlsx for the amber cache IP.

This is a PRE-RTL workbook. amber has no RTL yet, so the derived minimal SOP
is the contract the future RTL must match. When RTL lands, rtl_sop= strings
will be supplied and the generator will emit the three-outcome verdict
(identical / RTL-redundant / RTL-differs) from bin/kmaps/minimize.py.

Builds, from scratch (rerunnable / idempotent):
  * CONTRACT sheets -- per interface group, a table of Signal / Width / Dir /
    Driver / "Legal / Correct behavior" / invariant / notes.
  * K-MAP sheets -- for each important combinational decision signal, a K-map
    computed from the DECIDED tables in the amber HAS. Gray order 00 01 11 10;
    >4 vars page into multiple grids. 1-cells green, 0-cells grey, X-cells
    (don't-care) for unreachable input combos. The minimal cover is derived
    mechanically by Quine-McCluskey.

Every sheet intro states the pre-RTL status. Axis citations point to the amber
HAS chapters. The CITES registry is empty until RTL exists.

Rerun after RTL changes:
    python3 docs/gen_amber_contracts_kmaps.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
XLSX = os.path.join(HERE, "amber_signal_contracts.xlsx")
REPO = os.path.abspath(os.path.join(HERE, *([".."] * 5)))
sys.path.insert(0, os.path.join(REPO, "bin"))

import openpyxl

from kmaps.citations import verify_citations
from kmaps.writer import (CONTRACT_HDRS, KmapWriter, contract_sheet,
                          new_kmap_sheet)

# ---------------------------------------------------------------------------
# Citation registry: empty until RTL lands. When RTL exists, add
# (path-relative-to-repo, line-number, snippet) tuples here so the generator
# fails loudly if a cited expression moves.
# ---------------------------------------------------------------------------
CITES = []

HAS = "projects/components/cache-ip/amber-mesi-l1/docs/amber_has"
MAS = "projects/components/cache-ip/amber-mesi-l1/docs/amber_mas"

HAS_COHERENCE = f"{HAS}/ch03_architecture/04_coherence_fsm.md"
HAS_PARAMS = f"{HAS}/ch05_parameters/01_parameters.md"
HAS_INTERFACES = f"{HAS}/ch04_interfaces"
MAS_CONTROL = f"{MAS}/ch02_blocks/01_amber_control.md"


# ---------------------------------------------------------------------------
# CRRESP / next-state authority: HAS Table 3.0 (MESI snoop matrix)
# State encoding 2-bit: I=0, S=1, E=2, M=3.
# Snoop encoding 3-bit: ReadShared=0, ReadOnce=1, ReadUnique=2,
#                       CleanShared=3, CleanInvalid=4, MakeInvalid=5.
# ---------------------------------------------------------------------------
CRRESP_TABLE = {
    # (state, snoop): (DT, PD, IS, WU, next_state)
    (3, 0): (1, 1, 1, 0, 1),  # M + ReadShared    -> S
    (3, 1): (1, 1, 0, 0, 0),  # M + ReadOnce      -> I
    (3, 2): (1, 1, 0, 0, 0),  # M + ReadUnique    -> I
    (3, 3): (1, 1, 1, 0, 1),  # M + CleanShared   -> S
    (3, 4): (1, 1, 1, 0, 0),  # M + CleanInvalid  -> I
    (3, 5): (0, 0, 0, 0, 0),  # M + MakeInvalid   -> I
    (2, 0): (1, 0, 1, 1, 1),  # E + ReadShared    -> S
    (2, 1): (1, 0, 1, 1, 1),  # E + ReadOnce      -> S
    (2, 2): (1, 0, 0, 1, 0),  # E + ReadUnique    -> I
    (2, 3): (0, 0, 1, 1, 2),  # E + CleanShared   -> E
    (2, 4): (0, 0, 0, 0, 0),  # E + CleanInvalid  -> I
    (2, 5): (0, 0, 0, 0, 0),  # E + MakeInvalid   -> I
    (1, 0): (0, 0, 1, 0, 1),  # S + ReadShared    -> S
    (1, 1): (0, 0, 1, 0, 1),  # S + ReadOnce      -> S
    (1, 2): (0, 0, 0, 0, 0),  # S + ReadUnique    -> I
    (1, 3): (0, 0, 0, 0, 1),  # S + CleanShared   -> S
    (1, 4): (0, 0, 0, 0, 0),  # S + CleanInvalid  -> I
    (1, 5): (0, 0, 0, 0, 0),  # S + MakeInvalid   -> I
    (0, 0): (0, 0, 0, 0, 0),  # I + any           -> I
    (0, 1): (0, 0, 0, 0, 0),
    (0, 2): (0, 0, 0, 0, 0),
    (0, 3): (0, 0, 0, 0, 0),
    (0, 4): (0, 0, 0, 0, 0),
    (0, 5): (0, 0, 0, 0, 0),
}


def _bits_to_int(bits):
    v = 0
    for b in bits:
        v = (v << 1) | int(bool(b))
    return v


def _crresp_bit(bit_idx):
    def fn(st1, st0, sn2, sn1, sn0):
        state = _bits_to_int((st1, st0))
        snoop = _bits_to_int((sn2, sn1, sn0))
        if snoop > 5:
            return None  # don't-care: reserved / unused snoop encoding
        return CRRESP_TABLE[(state, snoop)][bit_idx]
    return fn


def _next_state_bit(bit_idx):
    def fn(st1, st0, sn2, sn1, sn0):
        state = _bits_to_int((st1, st0))
        snoop = _bits_to_int((sn2, sn1, sn0))
        if snoop > 5:
            return None
        return (CRRESP_TABLE[(state, snoop)][4] >> bit_idx) & 1
    return fn


# ---------------------------------------------------------------------------
# Contract sheets
# ---------------------------------------------------------------------------
def build_cpu_gaxi_contract(wb):
    rows = [
        ("Request", "cpu_req_wr_valid", "1", "in", "CPU",
         "Pulsed high when the CPU has a request. Held stable until the handshake.",
         "cpu_req_wr_valid |-> cpu_req_wr_data stable until cpu_req_wr_ready",
         f"{HAS_INTERFACES}/01_cpu_gaxi.md"),
        ("Request", "cpu_req_wr_ready", "1", "out", "amber_cpu_frontend",
         "Asserted only when amber_control is in CTRL_IDLE and no snoop priority "
         "stall is active. Because the cache is blocking, ready stays low from "
         "request acceptance until the response handshake completes.",
         "ready |-> CTRL_IDLE && !snoop_stall",
         f"{MAS_CONTROL}"),
        ("Request", "cpu_req_wr_data", "CPU_REQ_W", "in", "CPU",
         "Packed {addr, we, be, wdata}. Captured on the handshake cycle and held "
         "in the frontend latch until the response returns.",
         "stable from valid to ready; fields match CPU_REQ_W packing",
         f"{HAS_INTERFACES}/01_cpu_gaxi.md"),
        ("Response", "cpu_rsp_rd_valid", "1", "out", "amber_cpu_frontend",
         "Pulsed high when the response data is available. Held until accepted.",
         "cpu_rsp_rd_valid |-> cpu_rsp_rd_data stable until ready",
         f"{HAS_INTERFACES}/01_cpu_gaxi.md"),
        ("Response", "cpu_rsp_rd_ready", "1", "in", "CPU",
         "CPU backpressure. The frontend response skid/FIFO absorbs this; the "
         "cache pipeline is not stalled by response backpressure.",
         "no response torn / partial packet",
         f"{HAS_INTERFACES}/01_cpu_gaxi.md"),
        ("Response", "cpu_rsp_rd_data", "CPU_RSP_W", "out", "amber_cpu_frontend",
         "Packed {rdata}. For write requests the data field is zero/undefined; "
         "the handshake still marks completion.",
         "stable while cpu_rsp_rd_valid is high",
         f"{HAS_INTERFACES}/01_cpu_gaxi.md"),
    ]
    contract_sheet(
        wb, "CPU GAXI",
        "amber CPU-side GAXI slave signal contract",
        "Two house-GAXI streams: request (wr) and response (rd). Blocking: only "
        "one request is accepted at a time. Sources: "
        f"{HAS_INTERFACES}/01_cpu_gaxi.md, {MAS_CONTROL}.",
        rows)


def build_fabric_axi4_contract(wb):
    rows = [
        ("AR", "m_axi_arvalid", "1", "out", "amber_fill",
         "Asserted for one AR transaction per fill. ARLEN = FILL_BEATS-1, "
         "ARSIZE = log2(BUS_WIDTH/8), ARBURST=INCR, ARADDR line-aligned.",
         "one AR per fill; araddr aligned to LINE_BYTES",
         f"{HAS_INTERFACES}/02_fabric_axi4.md"),
        ("AR", "m_axi_araddr / arlen / arsize / arburst", "AW/8/3/2", "out",
         "amber_fill", "Line-aligned address; burst covers whole cache line.",
         "arlen+1 == FILL_BEATS; arsize matches BUS_WIDTH",
         f"{HAS_INTERFACES}/02_fabric_axi4.md"),
        ("R", "m_axi_rvalid / rready / rdata", "in/out/in", "fabric / amber_fill",
         "R beats accepted one per cycle and written to amber_data_array port A "
         "and the pending-fill bypass register.",
         "accepted beat == data_array write == bypass mask update",
         f"{HAS_INTERFACES}/02_fabric_axi4.md"),
        ("R", "m_axi_rlast", "1", "in", "fabric",
         "Marks the last beat of the fill burst. fill_done pulses one cycle after "
         "RLAST is accepted.",
         "exactly one rlast per fill",
         f"{HAS_INTERFACES}/02_fabric_axi4.md"),
        ("AW", "m_axi_awvalid", "1", "out", "amber_drain",
         "Asserted for one AW transaction per dirty victim drain. AWLEN = "
         "FILL_BEATS-1, AWSIZE = log2(BUS_WIDTH/8), AWBURST=INCR.",
         "one AW per dirty victim; awaddr == victim line address",
         f"{HAS_INTERFACES}/02_fabric_axi4.md"),
        ("W", "m_axi_wvalid / wdata / wstrb / wlast", "out", "amber_drain",
         "Whole-line write beats. WSTRB all-1s for every beat. WLAST on final beat.",
         "wlast exactly once per awlen+1 beats; wstrb all-1s",
         f"{HAS_INTERFACES}/02_fabric_axi4.md"),
        ("B", "m_axi_bvalid / bready / bresp", "in/out/in", "fabric / amber_drain",
         "Write response. bready is constant 1. drain_done pulses one cycle after "
         "the B handshake.",
         "one B per AW; bresp!=OKAY is a fatal error",
         f"{HAS_INTERFACES}/02_fabric_axi4.md"),
    ]
    contract_sheet(
        wb, "Fabric AXI4",
        "amber pair-rig AXI4 master signal contract",
        "Plain AXI4 read/write masters for fills and dirty-victim drains. Single "
        "outstanding. Sources: "
        f"{HAS_INTERFACES}/02_fabric_axi4.md.",
        rows)


def build_fabric_ace_contract(wb):
    rows = [
        ("AR", "fub_axi_arsnoop[3:0]", "4", "out", "amber_ace_issue",
         "ReadShared (shared fill) or ReadUnique (exclusive fill).",
         "arsnoop is one of the two onyx-D2 read encodings",
         f"{HAS_INTERFACES}/03_fabric_ace.md"),
        ("AR", "fub_axi_arvalid / arready / araddr / arlen", "-", "out/in",
         "amber_fill / axi4ace_master_rd", "Same timing as AXI4 case; ARSNOOP "
         "selects coherent transaction type.",
         "one AR per fill; address aligned",
         f"{HAS_INTERFACES}/03_fabric_ace.md"),
        ("R", "m_axi_rack", "1", "out", "axi4ace_master_rd",
         "ACE read acknowledge, auto-pulsed one cycle after RLAST handshake.",
         "exactly one rack per read transaction",
         f"{HAS_INTERFACES}/03_fabric_ace.md"),
        ("AW", "fub_axi_awsnoop[2:0]", "3", "out", "amber_ace_issue",
         "CleanUnique, MakeUnique, WriteBack, or Evict per cache event.",
         "awsnoop is one of the four onyx-D2 write encodings",
         f"{HAS_INTERFACES}/03_fabric_ace.md"),
        ("AW/W", "fub_axi_awvalid / wvalid / wlast", "-", "out",
         "amber_drain / axi4ace_master_wr", "WriteBack carries W data; "
         "CleanUnique/MakeUnique/Evict are AW-only.",
         "wlast exactly once per WriteBack; no W data for CU/MU/Evict",
         f"{HAS_INTERFACES}/03_fabric_ace.md"),
        ("B", "m_axi_wack", "1", "out", "axi4ace_master_wr",
         "ACE write acknowledge, auto-pulsed one cycle after B handshake.",
         "exactly one wack per write transaction",
         f"{HAS_INTERFACES}/03_fabric_ace.md"),
    ]
    contract_sheet(
        wb, "Fabric ACE",
        "amber_ace onyx-rig ACE master signal contract",
        "Full ACE read/write masters with ARSNOOP/AWSNOOP and auto-pulsed "
        "RACK/WACK. Sources: "
        f"{HAS_INTERFACES}/03_fabric_ace.md.",
        rows)


def build_snoop_contract(wb):
    rows = [
        ("AC", "m_axi_acvalid / acready", "1/1", "in/out",
         "peer cache / amber_snoop_resp",
         "AC handshake accepts a snoop address and type. acready is the skid "
         "buffer wr_ready; the adapter can absorb SKID_DEPTH_AC snoops.",
         "no snoop address dropped while adapter FIFO has space",
         f"{HAS_INTERFACES}/04_snoop_accdcr.md"),
        ("AC", "m_axi_acaddr / acsnoop[3:0] / acprot", "AW/4/3", "in",
         "peer cache", "Snoop address and type; one of six IHI0022 snoop encodings.",
         "acsnoop in {ReadShared,ReadOnce,ReadUnique,CleanShared,CleanInvalid,MakeInvalid}",
         f"{HAS_INTERFACES}/04_snoop_accdcr.md"),
        ("CD", "m_axi_cdvalid / cdready / cddata / cdlast", "out/in", "out",
         "amber_snoop_resp / peer cache",
         "CD beats driven when CRRESP.DataTransfer is 1. cdlast marks final beat.",
         "cdlast high on final beat only; data valid when cdvalid high",
         f"{HAS_INTERFACES}/04_snoop_accdcr.md"),
        ("CR", "m_axi_crvalid / crready / crresp[4:0]", "out/in/out",
         "amber_snoop_resp / peer cache",
         "CR is asserted only after the final CD beat has been accepted. CRRESP "
         "bits are the authority of HAS Table 3.0.",
         "crvalid low until cdlast handshake; CRRESP matches Table 3.0",
         f"{HAS_INTERFACES}/04_snoop_accdcr.md, {HAS_COHERENCE}"),
        ("Internal", "fub_acaddr / fub_acsnoop / fub_acvalid", "out", "out",
         "amber_snoop_resp / amber_control",
         "Bus-agnostic snoop request presented to amber_control.",
         "fub_acvalid pulses after AC handshake; stable until ctrl_snoop_ready",
         f"{HAS_INTERFACES}/04_snoop_accdcr.md"),
        ("Internal", "fub_crresp / fub_crvalid", "in", "in",
         "amber_control / amber_snoop_resp",
         "5-bit response from amber_control, captured and returned on CR after CD.",
         "fub_crvalid marks response ready; crvalid held until crready",
         f"{HAS_INTERFACES}/04_snoop_accdcr.md"),
    ]
    contract_sheet(
        wb, "Snoop ACDCR",
        "amber ACE snoop responder signal contract",
        "ACE-shaped snoop adapter with CR-after-CDLAST ordering. Sources: "
        f"{HAS_INTERFACES}/04_snoop_accdcr.md, {HAS_COHERENCE}.",
        rows)


def build_monbus_contract(wb):
    rows = [
        ("MonBus", "mon_valid", "1", "out", "amber_monlite",
         "One-cycle pulse per emitted packet. Never held for backpressure.",
         "downstream MUST provide FIFO or be always-ready",
         f"{HAS_INTERFACES}/05_observation_monbus.md"),
        ("MonBus", "mon_ready", "1", "in", "consumer",
         "Consumer flow control. Sustained backpressure drops packets at the "
         "source register.",
         "no partial/torn packets under backpressure",
         f"{HAS_INTERFACES}/05_observation_monbus.md"),
        ("MonBus", "mon_packet", "128", "out", "amber_monlite",
         "Standard monitor_common_pkg packet with AMBER agent/unit ids and "
         "event-specific payload.",
         "event classes match Chapter 4 of the MAS",
         f"{HAS_INTERFACES}/05_observation_monbus.md"),
        ("MonBus", "mon_timestamp", "64", "out", "amber_monlite",
         "Free-running time sampled at packet emission and held stable beside "
         "the packet.",
         "timestamp corresponds to the emit cycle",
         f"{HAS_INTERFACES}/05_observation_monbus.md"),
        ("MonBus", "drop-and-count", "-", "-", "amber_monlite",
         "Packets dropped under backpressure are counted and reported as "
         "AMBER_EV_DROPPED when the bus next has room.",
         "observer never stalls the measured path",
         f"{HAS_INTERFACES}/05_observation_monbus.md"),
    ]
    contract_sheet(
        wb, "MonBus out",
        "amber MonBus observation contract",
        "128-bit packet + 64-bit side-band timestamp. Drop-and-count policy. "
        f"Sources: {HAS_INTERFACES}/05_observation_monbus.md.",
        rows)


# ---------------------------------------------------------------------------
# K-map sheets
# ---------------------------------------------------------------------------
def build_snoop_crresp_kmaps(wb):
    km = new_kmap_sheet(wb, "K-maps snoop CRRESP")
    km.sheet_intro(
        f"amber_snoop_resp CRRESP derivation ({HAS_COHERENCE} Table 3.0)",
        ["These maps are the flagship pre-RTL contract. Each grid is computed "
         "row-for-row from the amber HAS MESI snoop matrix, which is the amber "
         "interpretation of the cocotb-framework 1.2.0 ACE BFM default handler.",
         "State is encoded 2-bit {I,S,E,M} = {0,1,2,3}; snoop type is encoded "
         "3-bit {ReadShared,ReadOnce,ReadUnique,CleanShared,CleanInvalid,MakeInvalid} "
         "= {0..5}. Snoop codes 6 and 7 are unreachable (reserved / unused).",
         "rtl_sop is intentionally absent: RTL does not exist yet. The derived "
         "minimal SOP is the contract the RTL must match."])

    km.table(
        "Snoop type encoding",
        f"{HAS_COHERENCE}",
        ["snoop[2:0]", "Type"],
        [("3'b000", "ReadShared"),
         ("3'b001", "ReadOnce"),
         ("3'b010", "ReadUnique"),
         ("3'b011", "CleanShared"),
         ("3'b100", "CleanInvalid"),
         ("3'b101", "MakeInvalid"),
         ("3'b110", "reserved / unused"),
         ("3'b111", "reserved / unused")],
        note="Only the six IHI0022 snoop encodings used by amber are reachable; "
             "110 and 111 are don't-care in the maps below.")

    axes = [
        ("state[1]", "current state MSB: {I,S,E,M} = {0,1,2,3}",
         f"{HAS_COHERENCE}"),
        ("state[0]", "current state LSB", f"{HAS_COHERENCE}"),
        ("snoop[2]", "snoop type MSB: {0..5} for the six IHI0022 snoops",
         f"{HAS_COHERENCE}"),
        ("snoop[1]", "snoop type middle bit", f"{HAS_COHERENCE}"),
        ("snoop[0]", "snoop type LSB", f"{HAS_COHERENCE}"),
    ]

    relation_text = (
        "Only snoop encodings 0..5 are used by amber; encodings 6 and 7 are "
        "reserved / unused and are unreachable. The relation marks those cells "
        "as don't-care so the QM cover can use them to widen implicants.")

    def snoop_unreachable(st1, st0, sn2, sn1, sn0):
        snoop = _bits_to_int((sn2, sn1, sn0))
        return snoop <= 5

    depends_text = (
        "these five bits and nothing else. The address/tag only selects WHICH "
        "line is looked up; the response bits depend only on the line's current "
        "MESI state and the snoop type. The pending-fill bypass is a separate "
        "path handled before these maps are consulted.")

    crresp_names = ["DT (DataTransfer)", "PD (PassDirty)",
                    "IS (IsShared)", "WU (WasUnique)"]
    for idx, name in enumerate(crresp_names):
        km.kmap(
            name, f"{HAS_COHERENCE}: Table 3.0",
            f"{name} = f(state[1:0], snoop[2:0]) from HAS Table 3.0",
            axes,
            _crresp_bit(idx),
            f"Single 1-cells exactly where HAS Table 3.0 says {name}=1; "
            f"0 elsewhere for reachable snoop codes; X for codes 6/7.",
            depends_only_on=depends_text,
            relations=[(relation_text, snoop_unreachable, f"{HAS_COHERENCE}")],
            rtl_sop=None)


def build_snoop_nextstate_kmaps(wb):
    km = new_kmap_sheet(wb, "K-maps snoop next-state")
    km.sheet_intro(
        f"amber_snoop_resp next-state derivation ({HAS_COHERENCE} Table 3.0)",
        ["Two boolean maps for next_state[1] and next_state[0], derived from the "
         "Next-state column of HAS Table 3.0. State encoding is {I,S,E,M} = "
         "{0,1,2,3}.",
         "rtl_sop is intentionally absent until RTL lands."])

    axes = [
        ("state[1]", "current state MSB: {I,S,E,M} = {0,1,2,3}",
         f"{HAS_COHERENCE}"),
        ("state[0]", "current state LSB", f"{HAS_COHERENCE}"),
        ("snoop[2]", "snoop type MSB: {0..5}", f"{HAS_COHERENCE}"),
        ("snoop[1]", "snoop type middle bit", f"{HAS_COHERENCE}"),
        ("snoop[0]", "snoop type LSB", f"{HAS_COHERENCE}"),
    ]

    relation_text = (
        "Snoop encodings 6 and 7 are reserved / unused; marked as don't-care.")

    def snoop_unreachable(st1, st0, sn2, sn1, sn0):
        return _bits_to_int((sn2, sn1, sn0)) <= 5

    depends_text = (
        "these five bits. The next MESI state of the probed line is a function "
        "only of its current state and the snoop type, per HAS Table 3.0.")

    for bit in (1, 0):
        km.kmap(
            f"next_state[{bit}]", f"{HAS_COHERENCE}: Table 3.0",
            f"next_state[{bit}] = f(state[1:0], snoop[2:0])",
            axes,
            _next_state_bit(bit),
            f"1-cells match the next-state column of HAS Table 3.0; 0 elsewhere "
            f"for reachable snoops; X for codes 6/7.",
            depends_only_on=depends_text,
            relations=[(relation_text, snoop_unreachable, f"{HAS_COHERENCE}")],
            rtl_sop=None)


def build_control_kmaps(wb):
    km = new_kmap_sheet(wb, "K-maps amber control")
    km.sheet_intro(
        f"amber_control miss-path decision ({MAS_CONTROL})",
        ["PROPOSED micro-architecture decision owned by the MAS. The axes are "
         "honest one-term signals; the derived minimal SOP is the contract the "
         "RTL must match when it lands.",
         "hit: the current request hit in the tag array. victim_dirty: the "
         "replacement victim is in Modified state. pending_bypass_match: the "
         "request/snoop address matches the pending-fill bypass register."])

    axes = [
        ("hit", "tag lookup hit for the current request",
         f"{MAS_CONTROL}"),
        ("victim_dirty", "replacement victim state == Modified",
         f"{MAS_CONTROL}"),
        ("pending_bypass_match", "address matches the pending-fill bypass register",
         f"{MAS_CONTROL}"),
    ]

    def start_drain(hit, dirty, bypass):
        return (not hit) and dirty and (not bypass)

    def start_fill(hit, dirty, bypass):
        return (not hit) and (not dirty) and (not bypass)

    def replay_now(hit, dirty, bypass):
        return (not hit) and bypass

    km.kmap(
        "start_drain", f"{MAS_CONTROL}: miss-path proposal",
        "start_drain = !hit & victim_dirty & !pending_bypass_match",
        axes, start_drain,
        "Single 1-cell at (hit=0, victim_dirty=1, pending_bypass_match=0). "
        "The dirty victim must be written back before the fill can proceed.",
        depends_only_on=(
            "these three one-term signals. The victim way and address are payload, "
            "not gates. All eight combinations are reachable in principle, though "
            "pending_bypass_match is normally 0 for CPU requests in the blocking "
            "pipeline."),
        rtl_sop=None)

    km.kmap(
        "start_fill", f"{MAS_CONTROL}: miss-path proposal",
        "start_fill = !hit & !victim_dirty & !pending_bypass_match",
        axes, start_fill,
        "Single 1-cell at (hit=0, victim_dirty=0, pending_bypass_match=0). "
        "No dirty victim: launch the line fill immediately.",
        depends_only_on=(
            "these three one-term signals. The fill address is payload; the "
            "decision is whether to launch, not what to fetch."),
        rtl_sop=None)

    km.kmap(
        "replay_now", f"{MAS_CONTROL}: miss-path proposal",
        "replay_now = !hit & pending_bypass_match",
        axes, replay_now,
        "1-cells whenever the address matches a pending fill and no new fill is "
        "needed. The original request is replayed from the frontend latch after "
        "the pending fill completes.",
        depends_only_on=(
            "these three one-term signals. In the blocking pipeline this signal "
            "is most relevant for snoops, but the control cone exposes it as a "
            "general input."),
        rtl_sop=None)


def main():
    verify_citations(CITES, REPO)
    wb = openpyxl.Workbook()
    del wb[wb.sheetnames[0]]  # drop default sheet

    build_cpu_gaxi_contract(wb)
    build_fabric_axi4_contract(wb)
    build_fabric_ace_contract(wb)
    build_snoop_contract(wb)
    build_monbus_contract(wb)

    build_snoop_crresp_kmaps(wb)
    build_snoop_nextstate_kmaps(wb)
    build_control_kmaps(wb)

    wb.save(XLSX)
    print(f"wrote {XLSX}")
    for name in wb.sheetnames:
        print(" ", name)


if __name__ == "__main__":
    main()

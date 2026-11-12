"""DDR2 device standard for Ramulator 2.1 (memory-controllers MC-012).

Upstream ships no DDR2. This class is derived from ddr3.py: the same command
set (ACT / PREpb / PREab / RD / WR / RDA / WRA / REFab), the same
Channel > Rank > Bank > Row > Column hierarchy, no bank groups. What differs,
each with its JESD79-2F source:

  * 4n prefetch (clause 2): internal_prefetch_size = 4, nBL = BL/2 CK, so BL4
    is 2 CK and one prefetch. BL8 is a second class (DDR2_BL8) because the
    prefetch size is a class attribute that fixes the transaction size
    (prefetch * channel_width / 8 bytes) and the column granularity.
  * Write latency WL = RL - 1 = AL + CL - 1 (clause 3.9, AL = 0 here). There
    is no CWL speed-bin field; nCWL is resolved as nCL - 1 so the DDR3
    turnaround expressions (RD->WR nCL + nBL + 2 - nCWL, WR->RD nCWL + nBL
    + nWTR, WR->PRE nCWL + nBL + nWR) carry over unchanged.
  * Read to precharge (clause 3.9.1, Table 42 note 3): RD -> PRE is
    AL + BL/2 + max(tRTP, 2 tCK) - 2 tCK, so the RD->PRE and RDA->ACT terms
    are "nBL + nRTP - 2" where DDR3 uses "nRTP". nRTP is at least 2.
  * tRPall (Table 41 note 1): on an 8-bank device PREab -> ACT is tRP + 1 tCK,
    so the rank-level PREab terms carry "nRP + 1". Single-bank PREpb is nRP.
  * tRRD and tFAW are by PAGE SIZE (Tables 42/43): 1 KB page 7.5 ns / 37.5 ns
    (35 ns at DDR2-800), 2 KB page 10 ns / 50 ns (45 ns at DDR2-800), with a
    2 tCK floor on tRRD. A x16 part with 1K columns is a 2 KB page.
  * tWTR is 10 ns at DDR2-400 and 7.5 ns from DDR2-533 up (Table 42 note 24).
  * tRFC by density (Table 40): 256 Mb 75, 512 Mb 105, 1 Gb 127.5, 2 Gb 195,
    4 Gb 327.5 ns. tREFI 7.8 us (85 C). tCCD = 2 tCK.

Presets come in two kinds. The JEDEC speed bins (DDR2_400B ... DDR2_800E,
Table 41) carry the bin's tRCD / tRP / tRAS / tRC and resolve tRRD / tFAW from
the organization's page size and the bin's rate. The PART presets
(DDR2_MT47H64M16_*) are the Nexys A7 device, Micron MT47H64M16 -25E (rated
DDR2-800, 2 KB page), run at the board clocks: a part keeps its own ns limits
when run slow, so those presets carry the part's tRRD 10 ns / tFAW 45 ns /
tWTR 7.5 ns explicitly instead of the bin table for that rate. The ns values
are the repo's pumice_device.py::DDR2_MT47H64M16_NS with tRRD corrected to
the 2 KB-page value (the table's 7.5 ns is the 1 KB figure; at CK 150 / 200
MHz both round to 2 CK, so the correction moves nothing on the board).

Rounding: Ramulator is CK-granular, nX = ceil(tX / tCK) with the JEDEC CK
floors. The RTL derivation adds a phase margin because its counters are
MC-cycle (2 CK) granular, so the model is the ideal CK-granular controller and
a 1 CK gap per constraint against granite is expected, not a modelling error.
"""
import math

from ramulator.dram.spec import DRAMStandard, TimingConstraint


def _ck(ns, tCK_ps, floor=1):
    return max(floor, math.ceil(ns * 1000 / tCK_ps))


class DDR2(DRAMStandard):
    name = "DDR2"
    internal_prefetch_size = 4          # 4n prefetch: BL4 is one prefetch
    read_latency = "nCL + nBL"

    levels = {
        "Channel": "N_A",
        "Rank":    "N_A",
        "Bank":    "Closed",
        "Row":     "Closed",
        "Column":  "N_A",
    }

    commands = ["ACT", "PREpb", "PREab", "RD", "WR", "RDA", "WRA", "REFab"]
    states = ["Opened", "Closed", "N_A"]

    timing_params = [
        "rate", "nBL",
        "nCL", "nRCD", "nRP", "nRAS", "nRC",
        "nWR", "nRTP", "nCWL",
        "nCCD", "nRRD", "nWTR",
        "nFAW", "nRFC", "nREFI",
        "nCS", "tCK_ps",
    ]

    supported_requests = {"Read": "RD", "Write": "WR"}

    timing_constraints = [
        # Channel: data bus occupancy
        TimingConstraint(level="Channel", preceding=["RD", "RDA"], following=["RD", "RDA"], latency="nBL"),
        TimingConstraint(level="Channel", preceding=["WR", "WRA"], following=["WR", "WRA"], latency="nBL"),
        # Rank: CAS to CAS
        TimingConstraint(level="Rank", preceding=["RD", "RDA"], following=["RD", "RDA"], latency="nCCD"),
        TimingConstraint(level="Rank", preceding=["WR", "WRA"], following=["WR", "WRA"], latency="nCCD"),
        # Rank: turnarounds. RD->WR = RL + BL/2 + 2 - WL ; WR->RD = WL + BL/2 + tWTR
        TimingConstraint(level="Rank", preceding=["RD", "RDA"], following=["WR", "WRA"], latency="nCL + nBL + 2 - nCWL"),
        TimingConstraint(level="Rank", preceding=["WR", "WRA"], following=["RD", "RDA"], latency="nCWL + nBL + nWTR"),
        # Rank switching (inert at one rank, kept for the multi-rank shape)
        TimingConstraint(level="Rank", preceding=["RD", "RDA"], following=["RD", "RDA", "WR", "WRA"], latency="nBL + nCS", window=1, sibling=True),
        TimingConstraint(level="Rank", preceding=["WR", "WRA"], following=["RD", "RDA"], latency="nCWL + nBL + nCS - nCL", window=1, sibling=True),
        # Rank: CAS to PREab
        TimingConstraint(level="Rank", preceding=["RD", "RDA"], following=["PREab"], latency="nBL + nRTP - 2"),
        TimingConstraint(level="Rank", preceding=["WR", "WRA"], following=["PREab"], latency="nCWL + nBL + nWR"),
        # Rank: RAS
        TimingConstraint(level="Rank", preceding=["ACT"], following=["ACT"], latency="nRRD"),
        TimingConstraint(level="Rank", preceding=["ACT"], following=["ACT"], latency="nFAW", window=4),
        TimingConstraint(level="Rank", preceding=["ACT"], following=["PREab"], latency="nRAS"),
        TimingConstraint(level="Rank", preceding=["PREab"], following=["ACT"], latency="nRP + 1"),     # tRPall, 8 banks
        # Rank: RAS to REF
        TimingConstraint(level="Rank", preceding=["ACT"], following=["REFab"], latency="nRC"),
        TimingConstraint(level="Rank", preceding=["PREpb"], following=["REFab"], latency="nRP"),
        TimingConstraint(level="Rank", preceding=["PREab"], following=["REFab"], latency="nRP + 1"),   # tRPall
        TimingConstraint(level="Rank", preceding=["RDA"], following=["REFab"], latency="nRP + nBL + nRTP - 2"),
        TimingConstraint(level="Rank", preceding=["WRA"], following=["REFab"], latency="nCWL + nBL + nWR + nRP"),
        TimingConstraint(level="Rank", preceding=["REFab"], following=["ACT"], latency="nRFC"),
        # Bank
        TimingConstraint(level="Bank", preceding=["ACT"], following=["ACT"], latency="nRC"),
        TimingConstraint(level="Bank", preceding=["ACT"], following=["RD", "RDA", "WR", "WRA"], latency="nRCD"),
        TimingConstraint(level="Bank", preceding=["ACT"], following=["PREpb"], latency="nRAS"),
        TimingConstraint(level="Bank", preceding=["PREpb"], following=["ACT"], latency="nRP"),
        TimingConstraint(level="Bank", preceding=["RD"], following=["PREpb"], latency="nBL + nRTP - 2"),
        TimingConstraint(level="Bank", preceding=["WR"], following=["PREpb"], latency="nCWL + nBL + nWR"),
        TimingConstraint(level="Bank", preceding=["RDA"], following=["ACT"], latency="nBL + nRTP - 2 + nRP"),
        TimingConstraint(level="Bank", preceding=["WRA"], following=["ACT"], latency="nCWL + nBL + nWR + nRP"),
    ]

    # ---- Secondary timing resolution (JESD79-2F Tables 40-43) ----
    @classmethod
    def resolve_secondary_timings(cls, timing_dict, org_dict):
        tCK_ps = timing_dict["tCK_ps"]
        rate = timing_dict["rate"]
        page_size_bytes = cls._page_size_bytes(org_dict)
        # A preset that already carries nRRD / nFAW (a part's own ns limits) keeps
        # them; a JEDEC bin preset marks them -1 and takes the page-size table.
        if timing_dict.get("nRRD", -1) == -1:
            timing_dict["nRRD"] = cls._resolve_nRRD(page_size_bytes, tCK_ps)
        if timing_dict.get("nFAW", -1) == -1:
            timing_dict["nFAW"] = cls._resolve_nFAW(page_size_bytes, rate, tCK_ps)
        timing_dict["nRFC"] = cls._resolve_nRFC(org_dict["density"], tCK_ps)
        timing_dict["nREFI"] = 7_800_000 // tCK_ps
        if timing_dict.get("nCWL", -1) == -1:
            timing_dict["nCWL"] = timing_dict["nCL"] - 1          # WL = CL - 1 (AL = 0)

    @staticmethod
    def _page_size_bytes(org_dict):
        dq = org_dict["dq"]
        if dq not in (4, 8, 16):
            return -1
        bits = org_dict["column"] * dq
        return bits // 8 if bits % 8 == 0 else -1

    @staticmethod
    def _resolve_nRRD(page_size_bytes, tCK_ps):
        tRRD_ns = {1024: 7.5, 2048: 10.0}.get(page_size_bytes)
        if tRRD_ns is None:
            return -1
        return _ck(tRRD_ns, tCK_ps, floor=2)

    @staticmethod
    def _resolve_nFAW(page_size_bytes, rate, tCK_ps):
        if page_size_bytes == 1024:
            tFAW_ns = 35.0 if rate >= 800 else 37.5
        elif page_size_bytes == 2048:
            tFAW_ns = 45.0 if rate >= 800 else 50.0
        else:
            return -1
        return _ck(tFAW_ns, tCK_ps)

    @staticmethod
    def _resolve_nRFC(density, tCK_ps):
        tRFC_ns = {256: 75.0, 512: 105.0, 1024: 127.5, 2048: 195.0, 4096: 327.5}.get(density)
        if tRFC_ns is None:
            return -1
        return _ck(tRFC_ns, tCK_ps)


# channel_width = dq: one device IS the channel (the Nexys A7 has a single x16
# part; tx = 4 * 16 / 8 = 8 bytes at BL4). x8 / x4 presets model a 64-bit DIMM rank.
DDR2.org_presets = {
    "DDR2_1Gb_x16": {"density": 1024, "dq": 16, "channel_width": 16, "rank": 1, "bank": 8, "row": 1 << 13, "column": 1 << 10},
    "DDR2_1Gb_x8":  {"density": 1024, "dq": 8,  "channel_width": 64, "rank": 1, "bank": 8, "row": 1 << 14, "column": 1 << 10},
    "DDR2_1Gb_x4":  {"density": 1024, "dq": 4,  "channel_width": 64, "rank": 1, "bank": 8, "row": 1 << 14, "column": 1 << 11},
    "DDR2_512Mb_x16": {"density": 512, "dq": 16, "channel_width": 16, "rank": 1, "bank": 4, "row": 1 << 13, "column": 1 << 10},
    "DDR2_2Gb_x16": {"density": 2048, "dq": 16, "channel_width": 16, "rank": 1, "bank": 8, "row": 1 << 14, "column": 1 << 10},
}

# nCWL -1 -> nCL - 1. nRRD / nFAW -1 -> JEDEC page-size table for the bin's rate.
# CK counts are ceil(ns / tCK) with the JESD79-2F floors (tCCD 2, tRTP 2, tRRD 2).
_JEDEC_BINS = {
    # Table 41 DDR2-400B 3-3-3 @ 5.0 ns: tRCD 15, tRP 15, tRAS 40, tRC 55; Table 42 tWTR 10, tRTP 7.5, tWR 15
    "DDR2_400B": {"rate": 400, "nBL": 2, "tCK_ps": 5000,
                  "nCL": 3, "nRCD": 3, "nRP": 3, "nRAS": 8, "nRC": 11,
                  "nWR": 3, "nRTP": 2, "nCWL": -1, "nCCD": 2, "nWTR": 2,
                  "nRRD": -1, "nFAW": -1, "nCS": 2},
    # DDR2-533B 3-3-3 @ 3.75 ns: tRCD 11.25, tRP 11.25, tRAS 45, tRC 56.25; tWTR 7.5
    "DDR2_533B": {"rate": 533, "nBL": 2, "tCK_ps": 3750,
                  "nCL": 3, "nRCD": 3, "nRP": 3, "nRAS": 12, "nRC": 15,
                  "nWR": 4, "nRTP": 2, "nCWL": -1, "nCCD": 2, "nWTR": 2,
                  "nRRD": -1, "nFAW": -1, "nCS": 2},
    # DDR2-667D 5-5-5 @ 3.0 ns: tRCD 15, tRP 15, tRAS 45, tRC 60; tWTR 7.5
    "DDR2_667D": {"rate": 667, "nBL": 2, "tCK_ps": 3000,
                  "nCL": 5, "nRCD": 5, "nRP": 5, "nRAS": 15, "nRC": 20,
                  "nWR": 5, "nRTP": 3, "nCWL": -1, "nCCD": 2, "nWTR": 3,
                  "nRRD": -1, "nFAW": -1, "nCS": 2},
    # DDR2-800E 6-6-6 @ 2.5 ns: tRCD 15, tRP 15, tRAS 45, tRC 60; tWTR 7.5 (Table 43)
    "DDR2_800E": {"rate": 800, "nBL": 2, "tCK_ps": 2500,
                  "nCL": 6, "nRCD": 6, "nRP": 6, "nRAS": 18, "nRC": 24,
                  "nWR": 6, "nRTP": 3, "nCWL": -1, "nCCD": 2, "nWTR": 3,
                  "nRRD": -1, "nFAW": -1, "nCS": 2},
}

# Micron MT47H64M16 -25E (Nexys A7), 1 Gb x16, 2 KB page, rated DDR2-800. Part ns
# limits: tRCD 15, tRP 15, tRAS 45, tRC 60, tWR 15, tWTR 7.5, tRTP 7.5, tRRD 10,
# tFAW 45, tRFC 127.5 (pumice_device.py::DDR2_MT47H64M16_NS with tRRD at the 2 KB
# value). The board runs it below every JEDEC bin, so its ns limits are kept
# explicitly here rather than taken from the bin table at that rate.
_PART_NS = dict(tRCD=15.0, tRP=15.0, tRAS=45.0, tRC=60.0, tWR=15.0, tWTR=7.5,
                tRTP=7.5, tRRD=10.0, tFAW=45.0)


def _part_preset(rate, tCK_ps, nCL):
    p = _PART_NS
    return {"rate": rate, "nBL": 2, "tCK_ps": tCK_ps,
            "nCL": nCL, "nRCD": _ck(p["tRCD"], tCK_ps), "nRP": _ck(p["tRP"], tCK_ps),
            "nRAS": _ck(p["tRAS"], tCK_ps), "nRC": _ck(p["tRC"], tCK_ps),
            "nWR": _ck(p["tWR"], tCK_ps), "nRTP": _ck(p["tRTP"], tCK_ps, floor=2), "nCWL": -1,
            "nCCD": 2, "nWTR": _ck(p["tWTR"], tCK_ps, floor=2), "nRRD": _ck(p["tRRD"], tCK_ps, floor=2),
            "nFAW": _ck(p["tFAW"], tCK_ps), "nCS": 2}


DDR2.timing_presets = {
    **_JEDEC_BINS,
    # the board point: CK 150 MHz (sys 75 MHz, DFI 1:2), CL3 -- pumice_dram_configs "board_ddr2_300"
    "DDR2_MT47H64M16_300_CL3": _part_preset(300, 6667, 3),
    # CK 200 MHz (sys 100 MHz), CL3 -- "ddr2_400_cl3_bl4"
    "DDR2_MT47H64M16_400_CL3": _part_preset(400, 5000, 3),
    # the part at its rating (DDR2-800 CL6 per MT47H64M16_BINS)
    "DDR2_MT47H64M16_800_CL6": _part_preset(800, 2500, 6),
}


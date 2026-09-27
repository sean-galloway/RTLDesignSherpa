"""The 12 named DRAM operating points, and the timing derivation for each.

WHY THIS FILE EXISTS. An operating point is a PART plus a CLOCK plus MODE
REGISTERS. Changing one field of one point in place does not produce another
point -- it produces a mix of two parts that no device implements, and a suite
running such a mix reports timing violations nobody can act on while hiding the
ones that matter. Sean, repeatedly and finally 2026-09-27: *"A config should
match the boards. Multiple legal and strictly defined configs should be run.
Using handwavy and bullshit mixes of configs that make no logical sense is
unacceptable."* So every point below is a complete, self-consistent tuple and a
test selects one BY NAME. Adding a point is welcome; editing one is not.

WHY IT IS ONE FILE AND NOT TWELVE. It was twelve files for about ten minutes,
then Sean: *"A single file with a dict is better than my idea."* He is right --
the whole value is being able to read the points against each other, and twelve
files with one dict each turns that comparison into a directory listing. The
keys were briefly numbered (`config1_board`, `config2_perf1`, ...) and are now
named for what they are, which is the same argument one level down: a key that
does not say CL and BL sends you back to the table to find out.

BOTH LAYERS IMPORT THIS. The macro scheduler TB and the top-level TB read the
same table; before this existed the macro TB carried invented numbers
(`t_rcd=3 t_rp=3 t_ras=5 t_rc=8` at 100 MHz -- a set matching no part at no
clock) and the top TB carried its own constants, which is how this suite ran the
wrong clock for months.

EVERY POINT IS LEGAL FOR THE PART. The MT47H64M16HR-25 is DDR2-800 rated.
Running it AT or BELOW a bin is legal (the board runs it at DDR2-300); running
it above its rating is not, and nothing here does. A CL at or ABOVE the bin
minimum is always legal, and config 5 uses that deliberately.

DDR3 / LPDDR3 NOTE. The derivation is per-family: `ddr2_timings_mc_cycles`
encodes DDR2's WL = CL-1 and its CK minimums. A successor family adds its own
derivation and its own points in this same table keyed by `family`; the
consumers -- the TBs and the command-stream checker -- read the derived cycle
counts and never ask which family produced them. Keep it that way and the whole
config axis ports for free.
"""

import os
import sys

_HOST_DIR = ("/mnt/data/github/RTLDesignSherpa/projects/fpga-systems/NexysA7/"
             "pumice/build-perf/host")
if _HOST_DIR not in sys.path:
    sys.path.insert(0, _HOST_DIR)

# IMPORTED, never re-typed. `ddr2_timings_mc_cycles` encodes the bank_timer port
# contracts (`t_wr_i` is "WR cmd -> earliest PRE, incl WL + BL/2") and was fixed
# for exactly that in 65968b9b4 -- a fix the top TB never received because it
# carried its own copy. A second copy of a part table is how that happens.
from pumice_device import (                                   # noqa: E402
    DDR2_MT47H64M16_NS as PART_MT47H64M16,
    ddr2_timings_mc_cycles as _ctrl_timings,
)
from CocoTBFramework.components.dfi.jedec_timings import (     # noqa: E402
    timings_from_params as _model_timings_from,
)

DEFAULT_CONFIG = "board_ddr2_300"

# JEDEC speed bins for the MT47H64M16HR-25 and the minimum CL in each, so a new
# point can be checked against them rather than against somebody's memory.
MT47H64M16_BINS = {800: 6, 667: 5, 533: 4, 400: 3}
MT47H64M16_RATED_MTPS = 800

# The keys are the configuration: family, data rate, CL, BL. The board carries
# its role in its name because "which one is the board" is the single fact a
# reader most needs, and DEFAULT_CONFIG points at it.
#
# key                        what it ISOLATES from the point before it
# board_ddr2_300             the shipping point; smallest cycle counts in the table
# board_ddr2_300_bl8         BL only -- same silicon, same clock as the board
# ddr2_400_cl3_bl4           lowest JEDEC bin; tRAS/tRC/tRFC move, tRCD/tRP do not
# ddr2_400_cl3_bl8           BL crossed with a second frequency
# ddr2_400_cl4_bl4           CL WITHOUT frequency (CL above the bin minimum)
# ddr2_533_cl4_bl4           mid bin; first point where tRCD/tRP reach 3; quantised clock
# ddr2_533_cl4_bl8           BL at the mid bin
# ddr2_650_cl5_bl4_xcheck    the DERIVATION CROSS-CHECK against the RDS-DV model
# ddr2_667_cl5_bl4           a real bin adjacent to the xcheck; the pair is a rounding control
# ddr2_667_cl5_bl8           worst case for the write-to-precharge contract
# ddr2_800_cl6_bl4           the part at its RATED speed; largest counts, opposite end of board
# ddr2_800_cl6_bl8           rated speed at BL8; largest counters in the table
DRAM_CONFIGS = {
    # CONFIG 1 -- THE BOARD, and the default everywhere. The part run well below
    # its rating, which is why its MC-cycle counts are the smallest here
    # (tRCD=2 tRP=2 tCCD=1). Small counts are NOT the easy case: they are where
    # a fixed-depth pipeline guard has the least slack behind it, and pumice
    # BUG-003 lived exactly there. Any result that does not hold here is not a
    # shipping result.
    "board_ddr2_300": dict(family="DDR2", part=PART_MT47H64M16, mc_clk_hz=75e6,
                          ck_per_mc=2, CL=3, BL=4, data_rate_mtps=300,
                          label="board DDR2-300 CL3 BL4"),

    # CONFIG 2 -- config 1 with only MR0's burst length changed, so BL is
    # isolated from everything else. BL is not cosmetic in the derivation: the
    # bank_timer contract folds WL + BL/2 into t_wr and t_wtr, so BL8 moves both
    # 4 -> 5 with nothing else moving. That derivation was wrong once
    # (65968b9b4). It is also the geometry where one DRAM burst is FOUR AXI beats
    # instead of one, which is how PUMICE-025's 2x read throttle shipped green.
    "board_ddr2_300_bl8": dict(family="DDR2", part=PART_MT47H64M16, mc_clk_hz=75e6,
                          ck_per_mc=2, CL=3, BL=8, data_rate_mtps=300,
                          label="DDR2-300 CL3 BL8"),

    # CONFIG 3 -- the lowest bin the part is graded for, at that bin's minimum
    # CL. tRCD and tRP stay at 2 while tRAS/tRC/tRFC grow (5/7/14 vs 4/5/11):
    # the row-cycle constraints move and the command-to-column ones do not. A
    # guard indexed to the wrong one of those two groups passes config 1 and
    # fails here.
    "ddr2_400_cl3_bl4": dict(family="DDR2", part=PART_MT47H64M16, mc_clk_hz=100e6,
                          ck_per_mc=2, CL=3, BL=4, data_rate_mtps=400,
                          label="DDR2-400 CL3 BL4"),

    # CONFIG 4 -- config 3 at BL8, so the BL axis is crossed with more than one
    # frequency. A BL-dependent defect that only appears when t_wr lands on a
    # particular value is invisible in a single-frequency BL sweep.
    "ddr2_400_cl3_bl8": dict(family="DDR2", part=PART_MT47H64M16, mc_clk_hz=100e6,
                          ck_per_mc=2, CL=3, BL=8, data_rate_mtps=400,
                          label="DDR2-400 CL3 BL8"),

    # CONFIG 5 -- a HIGHER CL than the bin requires. Always legal, and the ONLY
    # way to move CL without moving frequency. That separation is the point: CL
    # sets WL (= CL-1 on DDR2), and WL appears in t_wr, t_wtr and t_rtw but NOT
    # in tRCD, tRP, tRAS or tRC. Every other point moves CL and the clock
    # together, so a defect that tracks WL cannot be told from one that tracks
    # the clock. Here it can.
    "ddr2_400_cl4_bl4": dict(family="DDR2", part=PART_MT47H64M16, mc_clk_hz=100e6,
                          ck_per_mc=2, CL=4, BL=4, data_rate_mtps=400,
                          label="DDR2-400 CL4 BL4 (CL above bin minimum)"),

    # CONFIG 6 -- the mid bin, and the first point where tRCD and tRP reach 3.
    # Its MC period is also not a whole number of picoseconds (7.5 ns quantises
    # to 7.504 ns on the 8 ps grain), so it exercises the quantised-clock path
    # cocotb forces on us. Report the ACTUAL frequency from dram_clocks(),
    # never the nominal.
    "ddr2_533_cl4_bl4": dict(family="DDR2", part=PART_MT47H64M16,
                          mc_clk_hz=133.333333e6, ck_per_mc=2, CL=4, BL=4,
                          data_rate_mtps=533, label="DDR2-533 CL4 BL4"),

    # CONFIG 7 -- config 6 at BL8, completing the BL cross at the mid bin.
    "ddr2_533_cl4_bl8": dict(family="DDR2", part=PART_MT47H64M16,
                          mc_clk_hz=133.333333e6, ck_per_mc=2, CL=4, BL=8,
                          data_rate_mtps=533, label="DDR2-533 CL4 BL8"),

    # CONFIG 8 -- kept for ONE reason: deriving this point reproduces the RDS-DV
    # model's builtin_timings("ddr2-650-mt47h64m16hr") EXACTLY (tRCD=5 tRP=5
    # tRAS=15 tRC=20 tWR=5 in CK). Agreement between two independently written
    # derivations is the evidence that this table's numbers are right at all. It
    # stays even though 650 MT/s is not a JEDEC bin -- it is a cross-check, not
    # a product configuration, and it is labelled as such.
    "ddr2_650_cl5_bl4_xcheck": dict(family="DDR2", part=PART_MT47H64M16, mc_clk_hz=162.5e6,
                          ck_per_mc=2, CL=5, BL=4, data_rate_mtps=650,
                          label="650 CL5 BL4 (model cross-check, not a bin)"),

    # CONFIG 9 -- a real JEDEC bin next door to config 8, which makes the pair a
    # control: nearly the same clock must give nearly the same cycle counts. A
    # derivation that disagrees sharply between two adjacent clocks has a
    # rounding bug, and this pair is where that shows.
    "ddr2_667_cl5_bl4": dict(family="DDR2", part=PART_MT47H64M16,
                          mc_clk_hz=166.666667e6, ck_per_mc=2, CL=5, BL=4,
                          data_rate_mtps=667, label="DDR2-667 CL5 BL4"),

    # CONFIG 10 -- config 9 at BL8: the largest t_wr in the table at this BL
    # (WL + BL/2 + tWR all growing together), so the worst case for the
    # write-to-precharge contract.
    "ddr2_667_cl5_bl8": dict(family="DDR2", part=PART_MT47H64M16,
                           mc_clk_hz=166.666667e6, ck_per_mc=2, CL=5, BL=8,
                           data_rate_mtps=667, label="DDR2-667 CL5 BL8"),

    # CONFIG 11 -- the part at its RATED speed, and the opposite end of the
    # cycle-count range from config 1: tRCD=4 tRP=4 tRAS=10 tRC=13 tRFC=26
    # against the board's 2/2/4/5/11. Large counts hide the hazards small counts
    # expose and expose ones small counts hide -- a timer wide enough at tRFC=11
    # can overflow at 26, and a background close that cannot race the pick
    # pipeline at tRP=4 can at tRP=2. Both ends must run.
    "ddr2_800_cl6_bl4": dict(family="DDR2", part=PART_MT47H64M16, mc_clk_hz=200e6,
                            ck_per_mc=2, CL=6, BL=4, data_rate_mtps=800,
                            label="DDR2-800 CL6 BL4 (rated)"),

    # CONFIG 12 -- rated speed at BL8: the largest timing numbers in the table
    # (t_wr=8, t_wtr=7). If any counter in the scheduler is too narrow, this is
    # the config that finds it.
    "ddr2_800_cl6_bl8": dict(family="DDR2", part=PART_MT47H64M16, mc_clk_hz=200e6,
                            ck_per_mc=2, CL=6, BL=8, data_rate_mtps=800,
                            label="DDR2-800 CL6 BL8 (rated)"),
}

ALL_CONFIGS = tuple(DRAM_CONFIGS)

# The board plus the two ends and the middle of the cycle-count range: the
# smallest subset that still spans the axis. A sweep that cannot afford all 12
# uses this rather than inventing a subset.
SPAN_CONFIGS = ("board_ddr2_300", "ddr2_533_cl4_bl4", "ddr2_800_cl6_bl4")


def _resolve(name=None):
    name = name or os.environ.get("DRAM_CONFIG", DEFAULT_CONFIG)
    if name not in DRAM_CONFIGS:
        raise ValueError(
            f"unknown DRAM_CONFIG {name!r}. Legal operating points: "
            f"{sorted(DRAM_CONFIGS)}. Add a NEW named point rather than editing "
            f"one -- a point is a part plus a clock plus mode registers, and "
            f"changing a field in place makes it a mix of two parts.")
    return name, DRAM_CONFIGS[name]


def dram_clocks(name=None):
    """(aclk_ns, dfi_ns, ACTUAL aclk_hz) derived from the operating point.

    QUANTISED TO WHOLE PICOSECONDS, and to a MULTIPLE OF 8. 1e9/75e6 is
    13.3333...ns, which cocotb refuses outright ("Unable to accurately represent
    13.333333333333334(ns) with the simulator precision of 1e-12"), and the DFI
    clock divides it -- 13333/2 = 6666.5 ps is not whole either. A multiple of
    8 ps keeps /2, /4 and /8 all whole. Residual frequency error is ~2e-4.

    The third element is the frequency AFTER quantisation. Report that, never the
    nominal: a bandwidth computed from the nominal against a quantised clock is
    wrong by that same factor, and a test printing the nominal cannot be checked
    against the clock it actually ran.
    """
    _name, c = _resolve(name)
    grain = 8
    aclk_ps = grain * round(1e12 / c["mc_clk_hz"] / grain)
    dfi_ps = aclk_ps // c["ck_per_mc"]
    return aclk_ps / 1000.0, dfi_ps / 1000.0, round(1e12 / aclk_ps)


def board_clock_periods(name=None):
    """(aclk_ns, dfi_ns) -- the ONE source of truth for tests that start clocks.

    Twenty sites hardcoded `Clock(dut.aclk, 10)` / `Clock(dut.dfi_clk, 4)` --
    100 MHz and a 2.5:1 ratio matching neither DFI_RATE=2 nor the 75 MHz board.
    Fixing a TB class does not help the tests that bypass it, which is how
    BUG-003 was first measured on the wrong clock.
    """
    a, d, _hz = dram_clocks(name)
    return a, d


def dram_config(name=None):
    """Resolve one point into (model_timings, controller_mc_cycles, meta).

    Both halves come from the same part and clock, so a coherence assertion
    between the DV model and the programmed controller is possible -- and is made
    in PumiceTopCsrTB.program_timings().
    """
    name, c = _resolve(name)
    tck_ns = 1e9 / (c["mc_clk_hz"] * c["ck_per_mc"])
    cl, bl = c["CL"], c["BL"]
    cwl = cl - 1                                   # DDR2: WL = CL-1
    model = _model_timings_from(
        tCK_ns=tck_ns, CL=cl, CWL=cwl, BL=bl,
        **{(f"{k}_ns" if k != "tRAS" else "tRAS_min_ns"): v
           for k, v in c["part"].items()})
    ctrl = _ctrl_timings(c["mc_clk_hz"], ck_per_mc=c["ck_per_mc"], cl=cl,
                         part=c["part"], dram_bl=bl)
    aclk_ns, dfi_ns, aclk_hz = dram_clocks(name)
    meta = dict(name=name, family=c["family"], label=c["label"], tck_ns=tck_ns,
                CL=cl, CWL=cwl, BL=bl, ck_per_mc=c["ck_per_mc"],
                mc_clk_hz=c["mc_clk_hz"], data_rate_mtps=c["data_rate_mtps"],
                aclk_ns=aclk_ns, dfi_ns=dfi_ns, aclk_hz=aclk_hz)
    return model, ctrl, meta


def describe(name=None):
    """One line naming the point and every number derived from it.

    A passing run must be able to prove which config it ran
    (feedback_sim_config_must_be_provable), so print this beside the result.
    """
    _model, ctrl, meta = dram_config(name)
    t = " ".join(f"{k}={ctrl[k]}" for k in sorted(ctrl))
    return (f"{meta['name']:16s} {meta['label']:42s} "
            f"aclk={meta['aclk_hz']/1e6:8.3f}MHz ({meta['aclk_ns']}ns) "
            f"CL={meta['CL']} BL={meta['BL']} | {t}")

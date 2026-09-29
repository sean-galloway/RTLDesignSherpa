"""The scheduler layer across every legal operating point and paging mode.

WHY THIS TEST EXISTS. pumice BUG-003 -- a pick the arbiter's own final safety
gate had rejected being pushed to the DRAM anyway -- was found at this layer in
under a minute, after weeks of chasing it through the DFI model and the board.
The layer is cheap (no AXI front end, no CAMs, no DFI, no PHY), fully
observable, and it is where the command stream is DECIDED. Sean's question, and
the reason for this file: *"are there another 50 bugs laying dormant in the rtl
right now??? How do I tell????"* -- you tell by running the configurations that
make them reachable, and by checking the stream against JEDEC rather than
against a bandwidth number.

THE THREE AXES, and why each one can hide a defect the others cannot:

  OPERATING POINT (12 named legal points, pumice_dram_configs.py). The scheduler
  is single-domain, so a frequency reaches it ONLY as the timing set in MC
  cycles. Those counts span 2..4 for tRCD/tRP and 11..26 for tRFC across the
  table. Small counts leave a fixed-depth pipeline guard the least slack -- which
  is where BUG-003 lived -- while large counts are where a too-narrow counter
  overflows. Neither end substitutes for the other. It also decides whether a
  rule can arm at all: on the board tFAW=4 against tRRD=2, so tFAW is
  UNREACHABLE there no matter the stimulus, and only another point can test it.

  PAGING MODE (0..5). The modes differ in WHO closes a row and WHEN: nobody
  (static open), the column itself (auto-precharge), or a background timer with
  no column driving it (fixed_open). Only the third kind can close
  a row while a column for that row is already in the pick pipeline, which is
  the entire BUG-003 race. A suite that only runs open page cannot see it.

  TRAFFIC PATTERN. A rule that never arms proves nothing, and the stimulus is
  what arms it: a column stream never precharges, so it says nothing about tRP;
  a single-bank pattern cannot reach tRRD or tFAW; a read-only pattern cannot
  reach tWTR, tRTW or tWR. Each pattern below names the rules it exists to arm,
  and the checker REFUSES a verdict if they did not.

THE ORACLE IS JEDEC, NOT PERFORMANCE. Every arm replays the issued stream
through tbclasses/pumice_cmd_stream_checker.py -- per-bank open/closed AND open
ROW, plus every command-to-command minimum derived from that config -- and
separately asserts the arbiter invariant that a pick rejected by `w_out_safe`
is never pushed. A bandwidth regression is a different question and has its own
tests; this file asks only whether the controller ever tells the DRAM to do
something the DRAM forbids.

PORTING TO DDR3 / LPDDR3. Nothing here knows it is DDR2. The configs carry a
`family`, the checker consumes derived cycle counts, and the patterns are
expressed in banks, rows and columns. A successor family adds its timing
derivation and its points to the same table and this file runs unchanged.
"""

import os
import random
import sys
import time

import cocotb
from cocotb.utils import get_sim_time
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

_TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
_DV_DIR = os.path.abspath(os.path.join(_TESTS_DIR, "..", ".."))
for _p in (_TESTS_DIR, _DV_DIR):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from pumice_coverage import get_coverage_compile_args, get_coverage_env  # noqa: E402
from tbclasses.pumice_mem_cmd_scheduler_tb import (                      # noqa: E402
    PumiceMemCmdSchedulerTB, OP_ACT, OP_RD, OP_WR, OP_PRE, OP_REF,
)
from tbclasses.pumice_dram_configs import (                              # noqa: E402
    ALL_CONFIGS, SPAN_CONFIGS, DEFAULT_CONFIG, dram_config, describe,
)
from tbclasses.pumice_cmd_stream_checker import assert_clean             # noqa: E402

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/macro/pumice_mem_cmd_scheduler.f")

# Paging modes, by the name the RTL and the CSR use for each.
#   0 build_default  1 static_open  2 static_close(AP)  3 fixed_open
# (4 adapt_time and 5 adapt_access were RETIRED 2026-09-27 -- mode 4 measured
#  as fixed_open(tr_min) and mode 5 drove auto-precharge, which costs 4.9x the
#  activations. A write of 4..7 now falls through to the build default.)
# The (mode, tr_init) pairs: tr_init only means anything for the background-close
# modes, and TR=2 is the aggressive setting TASK-013 measured as the best default
# and BUG-003 blocked.
# Rules that a given arm CANNOT observe from the command stream, and must
# therefore not be required of it. Under auto-precharge there is no PRE command
# at all, and tRAS/tRTP/tWR gate the DEVICE's internal precharge rather than any
# command pumice issues (JESD79-2F 3.8.1) -- so requiring them of an AP arm asks
# the stimulus to prove something the interface cannot show.
_AP_UNOBSERVABLE = ("tRAS", "tRTP", "tWR")

PAGE_ARMS = (
    ("build_default", 0, 0),
    ("static_open",   1, 0),
    ("static_close",  2, 0),
    ("fixed_open_tr2", 3, 2),
    ("fixed_open_tr8", 3, 8),
    # A write to a RETIRED mode must behave as the build default, not as
    # something undefined -- so the retired encodings stay in the sweep as a
    # REGRESSION on the fallthrough, not as modes.
    ("retired_mode4_falls_through", 4, 2),
    ("retired_mode5_falls_through", 5, 0),
)


# --------------------------------------------------------------------------
# Traffic patterns. Each returns a list of (kind, bank, row, col) and names the
# checker rules it exists to arm -- a pattern that cannot arm its own rules is a
# pattern that proves nothing, and assert_clean turns that into a failure.
# --------------------------------------------------------------------------
def _pat_col_stream(n):
    """One row, walking columns: the row-hit path. Arms tRCD and tCCD."""
    return [("rd", 2, 0x123, 0x40 + 4 * (i % 128)) for i in range(n)], ("tRCD", "tCCD")


def _pat_row_thrash(n):
    """One bank, alternating rows: forces PRE/ACT every access.

    This is the pattern that reaches the background-close race, because every
    access leaves the bank briefly idle with a column already classified.
    """
    return ([("rd", 2, 0x100 + (i % 2) * 0x40, 0x40 + 4 * (i % 128))
             for i in range(n)], ("tRP", "tRAS", "tRC", "tRCD"))


def _pat_bank_rotate(n):
    """Rotate all 8 banks, one row each: the ACT-pressure path. Arms tRRD/tFAW."""
    return ([("rd", i % 8, 0x200 + (i % 8), 0x40 + 4 * ((i // 8) % 128))
             for i in range(n)], ("tRRD", "tRCD"))


def _pat_bank_rotate_thrash(n):
    """Rotate banks AND rows: maximum ACT/PRE pressure across the array."""
    return ([("rd", i % 8, 0x300 + (i % 8) + (i // 8) * 0x10,
              0x40 + 4 * (i % 128)) for i in range(n)],
            ("tRRD", "tRP", "tRC"))


def _pat_rw_mix(n):
    """Alternating reads and writes on one row: the turnaround path.

    Arms tWTR and tRTW, and -- because a write must complete before its bank can
    be precharged -- tWR, which no read-only pattern can reach.
    """
    return ([("wr" if i % 2 else "rd", 3, 0x321, 0x80 + 4 * (i % 128))
             for i in range(n)], ("tWTR", "tRTW"))


def _pat_rw_thrash(n):
    """Reads and writes across two rows of one bank: turnarounds AND closes."""
    return ([("wr" if i % 2 else "rd", 3, 0x400 + (i % 2) * 0x40,
              0x80 + 4 * (i % 128)) for i in range(n)], ("tWR", "tRP"))


def _pat_random(n):
    """SEEDED RANDOM traffic across banks, rows, columns and direction.

    THIS IS THE PATTERN THAT LOOKS FOR DORMANT BUGS. The directed patterns above
    each walk one axis, so they reach the states a human thought of; a defect
    that needs a particular INTERLEAVING -- a write turnaround landing in the
    same cycle as another bank's background close, a refresh arriving between a
    pick and its fire -- is not on any of those paths. 2000 directed requests
    that all have the same shape explore barely more state than 32 of them,
    which is the honest criticism of the first version of this file.

    The seed comes from the suite's SEED/RDS_SEED_BASE plumbing, so a failure
    replays exactly (project_seed_rerun_masks_failures).
    """
    rng = random.Random(int(os.environ.get("SEED", "0")) ^ 0x5CED)
    seq = []
    for _ in range(n):
        kind = "wr" if rng.random() < 0.4 else "rd"
        bank = rng.randrange(8)
        # A small row set per bank keeps hits and misses both common: an all-random
        # row is a miss almost every time, which tests the ACT path and nothing
        # else. Four rows per bank gives a realistic hit/miss mix.
        row = 0x500 + bank * 0x40 + rng.randrange(4)
        seq.append((kind, bank, row, 0x40 + 4 * rng.randrange(128)))
    return seq, ("tRCD", "tRP", "tRRD", "tCCD")


def _pat_random_single_bank(n):
    """Seeded random, confined to ONE bank: maximum row-conflict density.

    Restricting the bank removes the parallelism that hides same-bank ordering
    defects -- every request contends for the same row buffer, so close/open
    races per unit time are an order of magnitude denser than in the spread
    pattern. This is the shape BUG-003 needed.
    """
    rng = random.Random(int(os.environ.get("SEED", "0")) ^ 0xB10C)
    seq = []
    for _ in range(n):
        kind = "wr" if rng.random() < 0.4 else "rd"
        seq.append((kind, 5, 0x600 + rng.randrange(3),
                    0x40 + 4 * rng.randrange(128)))
    return seq, ("tRP", "tRC", "tRCD")


PATTERNS = (
    ("col_stream", _pat_col_stream),
    ("row_thrash", _pat_row_thrash),
    ("bank_rotate", _pat_bank_rotate),
    ("bank_rotate_thrash", _pat_bank_rotate_thrash),
    ("rw_mix", _pat_rw_mix),
    ("rw_thrash", _pat_rw_thrash),
    ("random", _pat_random),
    ("random_single_bank", _pat_random_single_bank),
)

# REG_LEVEL scales the cross-product, not the rigour: every level runs the same
# oracle, and a smaller level runs fewer arms. The DEPTH of a cell is the
# TEST_LEVEL its wrapper exports through level_env() (tooling BUG-004: the
# conftest stamp is gone, so the per-cell export is what the simulator sees);
# REG_LEVEL is read second only so a bare `pytest` still picks a sane table.
# REG_LEVEL scales the cross-product AND THE DEPTH. The first version of this
# file drove 16-32 requests per pattern at every level, so "12 configs, 504 arms"
# finished in 37 seconds -- which is the correct amount of time to find nothing.
# `reqs` is requests per pattern per arm, and it is the number that decides
# whether this sweep can find a dormant bug or merely confirm the ones already
# known. At FULL a single config drives ~100k requests and takes minutes, which
# is the point.
_LEVELS = {
    "gate": dict(patterns=("row_thrash", "rw_mix", "random_single_bank"),
                 arms=("static_open", "static_close", "fixed_open_tr2"),
                 reqs=48),
    "func": dict(patterns=("col_stream", "row_thrash", "bank_rotate", "rw_mix",
                           "random", "random_single_bank"),
                 arms=("build_default", "static_open", "static_close",
                       "fixed_open_tr2", "retired_mode4_falls_through"),
                 reqs=384),
    "full": dict(patterns=tuple(n for n, _ in PATTERNS),
                 arms=tuple(n for n, _, _ in PAGE_ARMS),
                 reqs=2048),
}


def _level():
    lv = (os.environ.get("TEST_LEVEL") or os.environ.get("REG_LEVEL")
          or "func").lower()
    return _LEVELS.get(lv, _LEVELS["func"]), lv


async def _drive(tb, seq, settle):
    """Push one pattern through the TB's single-entry CAM model."""
    for kind, bank, row, col in seq:
        ent = dict(bank=bank, row=row, col=col, id=0xA, age=10, slot=3)
        if kind == "rd":
            tb.rd_entry = ent
            for _ in range(400):
                if tb.rd_entry is None:
                    break
                await tb.wait_clocks('aclk', 1)
        else:
            tb.wr_entry = ent
            for _ in range(400):
                if tb.wr_entry is None:
                    break
                await tb.wait_clocks('aclk', 1)
    await tb.wait_clocks('aclk', settle)


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_sched_config_matrix(dut):
    cfg = os.environ.get("DRAM_CONFIG", DEFAULT_CONFIG)
    _model, ctrl, meta = dram_config(cfg)
    tb = PumiceMemCmdSchedulerTB(dut, config=cfg)
    await tb.setup_clocks_and_reset()
    assert await tb.complete_init(), "init_done never asserted"

    # THE INIT SEQUENCE IS EXCLUDED, DELIBERATELY AND EXPLICITLY. This TB zeroes
    # t_init_wait / t_dll_wait / t_mrd_wait / t_rp_wait / t_rfc_wait, because the
    # real ones are hundreds of microseconds of power-up delay that no simulation
    # can afford to wait out. That makes the init-phase command spacing
    # deliberately NOT JEDEC-legal -- at DDR2-800 the first mission ACT lands 21
    # cycles after init's last REF against tRFC=26 -- so replaying it through a
    # JEDEC checker reports the shortening, not a defect.
    #
    # Excluding it is sound because DDR2 init ENDS with every bank precharged
    # (PREA, refreshes, MRS writes), which is exactly the blank state the model
    # starts from. What it does mean is that NOTHING in this suite currently
    # checks the init sequence's own timing legality; that is a real gap, filed
    # rather than papered over here.
    init_end = len(tb.cmds)
    tb.log.info("init issued %d commands; the JEDEC replay starts after them "
                "(init waits are shortened for sim and are not representative)",
                init_end)

    level, level_name = _level()
    tb.log.info("=" * 78)
    tb.log.info("SCHEDULER MATRIX  level=%s", level_name)
    tb.log.info("  %s", describe(cfg))
    tb.log.info("  arms=%s", ",".join(level['arms']))
    tb.log.info("  patterns=%s", ",".join(level['patterns']))
    tb.log.info("=" * 78)

    pats = [(n, f) for n, f in PATTERNS if n in level['patterns']]
    arms = [(n, m, tr) for n, m, tr in PAGE_ARMS if n in level['arms']]
    # tRP is a settle allowance, not a guess: long enough for the last command to
    # clear CMD_DELAY and the cmd FIFO at any config in the table.
    settle = 24 + ctrl['tRC'] + ctrl['tRFC']

    total_cmds = total_pushes = total_reqs = 0
    ran = []
    t_wall0 = time.time()
    for arm_name, mode, tr in arms:
        dut.page_mode_i.value = mode
        dut.page_tr_init_i.value = tr
        await tb.wait_clocks('aclk', 8)
        for pat_name, pat_fn in pats:
            seq, must_arm = pat_fn(level['reqs'])
            if mode == 2:                     # static close == auto-precharge
                must_arm = tuple(r for r in must_arm
                                 if r not in _AP_UNOBSERVABLE)
            base_cmd, base_push = len(tb.cmds), len(tb.pushes)
            await _drive(tb, seq, settle)
            # THE WHOLE STREAM, reported FROM base_cmd. Bank state carries across
            # patterns and arms -- the ACT that opened a bank is routinely in the
            # previous phase -- so handing the checker only this phase's tail
            # would start it with every bank idle and report the first column as
            # a column to a closed bank. That false positive is what this run
            # produced before `since` existed.
            stream = list(tb.cmds)[init_end:]
            pushed = len(tb.pushes) - base_push
            label = f"{cfg}/{arm_name}/{pat_name}"

            # ORACLE 1 -- JEDEC legality of the issued stream, with the rules
            # this pattern exists to arm REQUIRED to have evaluated.
            assert_clean(stream, ctrl, num_banks=tb.NUM_BANKS, label=label,
                         require=must_arm, min_cmds=4, log=tb.log,
                         since=base_cmd - init_end,
                         bl=meta['BL'], ck_per_mc=meta['ck_per_mc'])

            # ORACLE 2 -- the arbiter invariant (pumice BUG-003). A pick its own
            # final gate rejected must never reach the cmd FIFO. Checked on every
            # arm because the defect was structural, not mode-specific.
            assert not tb.unsafe_pushes, (
                f"[{label}] BUG-003 CLASS: {len(tb.unsafe_pushes)} commands "
                f"pushed to the cmd FIFO with w_out_safe==0 -- rejected by the "
                f"arbiter's own final gate, no evt_* strobed for them, and "
                f"issued to the DRAM regardless. First: {tb.unsafe_pushes[0]}")

            total_cmds += len(stream) - (base_cmd - init_end)
            total_reqs += len(seq)
            total_pushes += pushed
            ran.append((arm_name, pat_name, len(stream)))

    # THE RUN MUST PROVE ITS DEPTH, not just that it ran. Sean, on reading that
    # 12 configs and 504 arms had completed in 37 seconds: *"I would expect 12
    # configurations at the scheduler_layer to run for 36 minutes or more. 37
    # seconds sounds way too fast."* He was right -- the patterns were 16-32
    # requests each, so the sweep was a smoke test with a sweep's arm count. A
    # wall-clock and cycle count printed beside the verdict is what makes that
    # visible without having to reason about it from the pattern definitions.
    wall = time.time() - t_wall0
    sim_cyc = get_sim_time('ns') / meta['aclk_ns']
    tb.log.info("-" * 78)
    for a, p, n in ran:
        tb.log.info("  %-18s %-20s %4d commands", a, p, n)
    tb.log.info("MATRIX OK  %s  level=%s", cfg, level_name)
    tb.log.info("  %d arms, %d requests driven, %d commands issued, %d pushes",
                len(ran), total_reqs, total_cmds, total_pushes)
    tb.log.info("  %.0f aclk cycles simulated (%.3f ms sim time) in %.1f s wall "
                "= %.0f cycles/s", sim_cyc, get_sim_time('ns') / 1e6, wall,
                sim_cyc / max(wall, 1e-6))
    tb.log.info("  0 JEDEC violations, 0 unsafe pushes")
    assert len(ran) == len(arms) * len(pats), (
        f"expected {len(arms) * len(pats)} arms, ran {len(ran)}")
    # EVERY REQUEST MUST HAVE PRODUCED AT LEAST ITS COLUMN. That is the floor
    # the stimulus itself defines, so it scales with the patterns instead of
    # being a magic number that has to be retuned whenever a level changes --
    # the first version of this check was `> 40 * arms` and failed a run in
    # which nothing was wrong.
    assert total_cmds >= total_reqs, (
        f"{total_reqs} requests were driven but only {total_cmds} commands "
        f"issued over {len(ran)} arms -- requests were dropped, so the clean "
        f"verdict is not evidence of anything.")


# --------------------------------------------------------------------------
# One pytest cell per operating point. The cells differ in elaboration
# PARAMETERS (the in-RTL command-history scoreboard's turnaround windows are
# compile-time and must match the config being programmed), so each gets its own
# sim_build -- sharing one would silently audit against another config's numbers.
# --------------------------------------------------------------------------
def _matrix_configs():
    """Which points this level runs. FULL runs all 12; below that, the span.

    SPAN is the board plus the two ends of the cycle-count range -- the smallest
    subset that still crosses the axis. It is a named subset in the config module
    rather than a slice invented here, so it cannot drift from the table.
    """
    lv = (os.environ.get("TEST_LEVEL") or os.environ.get("REG_LEVEL")
          or "func").lower()
    return ALL_CONFIGS if lv == "full" else SPAN_CONFIGS


@pytest.mark.parametrize("config", _matrix_configs())
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_pumice_sched_matrix(request, config, test_level):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_mem_cmd_scheduler"
    test_name = f"sched_matrix_{config}_{test_level}"

    _model, ctrl, meta = dram_config(config)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")
    os.makedirs(log_dir, exist_ok=True)

    params = {
        "NUM_RANKS": "1", "NUM_BANKS": "8", "ROW_WIDTH": "14", "COL_WIDTH": "10",
        "AXI_ID_WIDTH": "8", "NUM_ENTRIES": "8",
        # The in-scheduler command-history scoreboard (audit-only, generate-gated)
        # is a SECOND, independent oracle -- and its turnaround windows are
        # elaboration parameters, so they must be DERIVED from the config being
        # programmed. They were pinned at 2/2 to match the TB's old invented
        # timings; against the board's tWTR=4 / tRTW=20 that scoreboard would
        # have been auditing windows no config in the table uses.
        "CMD_HISTORY_EN": "1",
        "HIST_T_WTR": str(ctrl['tWTR']),
        "HIST_T_RTW": str(ctrl['tRTW']),
        # tRRD/tFAW: the two windows NO per-bank history can see, because they
        # constrain ACTs to DIFFERENT banks. Armed for pumice ISSUE-019 -- the
        # arbiter checks both two registers before the command fires and nothing
        # rechecked them at the issuing cycle.
        "HIST_T_RRD": str(ctrl['tRRD']),
        "HIST_T_FAW": str(ctrl['tFAW']),
    }
    extra_env = {
        "DUT": dut_name, "LOG_PATH": log_path, "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        "DRAM_CONFIG": config,
        **level_env(test_level),
    }
    extra_env.update(params)
    compile_args = ["+define+USE_ASYNC_RESET", "--assert"] + get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(
        python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_sched_config_matrix",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env,
        parameters=params, compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))), keep_files=True,
        timescale="1ns/1ps",
    )

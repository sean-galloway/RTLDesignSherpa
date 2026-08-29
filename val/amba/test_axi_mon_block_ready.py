# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_axi_mon_block_ready
# Purpose: block_ready validation for EVERY axi*_{master,slave}_{rd,wr}_mon.
#
# EVERY ACCEPTED COMMAND MUST GET A TABLE SLOT.
#
# All twelve wrappers share axi_monitor_base and therefore share the gate that
# admits commands. None of them validated it. This file gives each one its own
# test of the same three layers (see TBClasses.axi_monitor.block_ready_check):
#
#   1. saturation coverage   debug_block_ready actually went low
#   2. gating contract       blocked + enabled -> no command admitted
#   3. admission invariant   every admitted command got a table entry
#
# Layer 1 exists because a test can drive large response delays, look like it is
# exercising backpressure, and never fill the table -- a green run that proves
# nothing. It caught exactly that here: the first version awaited each
# transaction, so occupancy never exceeded 1 of 12 and block_ready never went
# low, while every other check passed.
#
# Layer 3 measures the documented lossy degrade. block_ready is computed against
# a one-cycle-stale active_count, so a command can be ADMITTED with no free
# slot; its data beats then arrive unmatched, and unmatched data allocation is
# deliberately ungated (a monitor must never stall returning data), so those
# beats are discarded. axi_monitor_base.sv accepts that as lossy-but-honest
# degrade in preference to the permanent stall a wider margin causes. This test
# turns the loss into a number (admitted_while_full) per wrapper instead of
# leaving it invisible.
#
# Measured so far: 0 on every wrapper that saturates, at every depth -- so the
# single-wrapper level does not reproduce the observer-level 4096-vs-3073 gap.
#
# See [[AMBA-BLOCKMARGIN]].

import contextlib
import os

import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.axi_monitor.block_ready_check import BlockReadyCheck
from TBClasses.axi4.monitor.axi4_master_monitor_tb import AXI4MasterMonitorTB


# Wrappers under test. Every one instantiates axi_monitor_base, so every one
# inherits the gate -- axi4_intf_master_observer is a thin wrapper over these, which is
# why the observer-level drop reproduces here.
WRAPPERS = [
    "axi4_master_rd_mon",  "axi4_master_wr_mon",
    "axi4_slave_rd_mon",   "axi4_slave_wr_mon",
    "axi5_master_rd_mon",  "axi5_master_wr_mon",
    "axi5_slave_rd_mon",   "axi5_slave_wr_mon",
    "axil4_master_rd_mon", "axil4_master_wr_mon",
    "axil4_slave_rd_mon",  "axil4_slave_wr_mon",
]

FILELIST_DIR = {"axi4": "rtl/amba/filelists", "axi5": "rtl/amba/filelists",
                "axil": "rtl/amba/filelists"}


# Seed control -- same model as test_axi_monitor_trans_mgr.py, for the same
# reason: a run that cannot be replayed cannot be diagnosed.
#
# Pinned DELIBERATELY, and read from BLOCKREADY_SEED rather than SEED, so an
# exported SEED aimed at another suite cannot perturb this one. Saturation
# here has little margin, and an arbitrary seed silently turns the run into
# one that proves nothing. Measured on axi4_master_wr_mon at
# MAX_TRANSACTIONS=12, where block_ready asserts at depth - CMD_ENTRY_RESERVE
# = 9:
#
#     12345 (default)  peak 9/12   block_ready low 69 cycles   -> saturates
#     1234             peak 7/12   never blocked -> layer 1 fails
#     42               peak 8/12   never blocked -> layer 1 fails
#     7                peak 7/12   never blocked -> layer 1 fails
#
# Layer 1 is RIGHT to fail those three: the table never filled, so the run
# proves nothing about the gate. The defect is in the premise, not the check.
#
# The write path cannot currently be pushed deeper to buy margin. It is capped
# by the axi4 interface's single _aw_w_lock, held across (send AW, send all W
# beats), which serialises writes whatever their ID -- measured with 1, 2, 8
# and 32 distinct IDs, byte-identical results. Spreading IDs is therefore NOT
# the fix it looks like; decoupling AW issuance from the W critical section is
# an RDS-DV framework change. Depth 8 has real margin (block_ready low for
# 850-2200 cycles at every seed tried), depth 12 sits on the edge, and both
# are kept: 8 as the honest check, 12 because at the pinned seed it does
# saturate and does exercise a deeper table.
#
# To sweep deliberately:
#     BLOCKREADY_SEED=1234 pytest val/amba/test_axi_mon_block_ready.py
DEFAULT_SEED = "12345"


def _seed() -> str:
    return os.environ.get("BLOCKREADY_SEED", DEFAULT_SEED)


@contextlib.contextmanager
def _pinned_seed():
    """Pin SEED for the child simulation, overriding any exported value.

    Passing "SEED" in extra_env is NOT enough, and this is worth stating
    plainly because it is not obvious and it is repo-wide: cocotb_test's
    Simulator.set_env() does

        for e in os.environ:
            self.env[e] = os.environ[e]

    -- it copies the whole parent environment ON TOP of extra_env, so an
    exported variable always wins over the extra_env entry of the same name.
    A runner that "sets" SEED in extra_env is therefore only choosing the
    default for when SEED is unset; export SEED and the runner's value is
    silently discarded.

    So pin it in os.environ, where set_env() will read it, and restore after.
    """
    prev = os.environ.get("SEED")
    os.environ["SEED"] = _seed()
    try:
        yield
    finally:
        if prev is None:
            os.environ.pop("SEED", None)
        else:
            os.environ["SEED"] = prev


async def _wait_clocks(tb, n):
    """Advance n aclk edges regardless of which testbench shape `tb` is.

    The axi4/axi5 monitor TBs wrap a base TB that owns wait_clocks; the axil4
    ones build BFM components directly and have no base_tb at all. Reaching
    for tb.base_tb unconditionally is what made the four axil4 wrappers fail
    in setup with AttributeError instead of running.
    """
    base = getattr(tb, "base_tb", None)
    if base is not None and hasattr(base, "wait_clocks"):
        await base.wait_clocks("aclk", n)
        return
    for _ in range(n):
        await RisingEdge(tb.aclk if hasattr(tb, "aclk") else tb.dut.aclk)


def _resolve_driver(tb, is_write: str):
    """The one-transaction driver, whatever this TB calls it and wherever it
    lives. Raises rather than returning None: a missing driver must never read
    as a run in which the RTL simply accepted nothing."""
    names = (["single_write_test", "single_write_response_test", "simple_write_test",
              "single_write", "simple_write"] if is_write else
             ["single_read_test", "single_read_response_test", "simple_read_test",
              "single_read", "simple_read"])
    base = getattr(tb, "base_tb", None)
    if base is not None:
        for n in names:
            if hasattr(base, n):
                return getattr(base, n)
    comps = getattr(tb, "master_components", None)
    if isinstance(comps, dict):
        for n in names:
            if n in comps:
                return comps[n]
    raise RuntimeError(
        f"{type(tb).__name__} exposes none of {names} on base_tb or "
        f"master_components; cannot drive traffic.")



def _apply_hold(tb, hold):
    """Push the response-holding randomizer onto whichever components exist.

    Saturation is the PREMISE of this test -- layer 1 fails the run outright if
    the table never fills. The axi4/axi5 TBs expose their BFM components as
    attributes of base_tb; the axil4 TBs hand back dicts (master_components /
    slave_components). Only reaching for the first shape left the axil4
    wrappers running at full speed, so entries retired as fast as they were
    made and block_ready never went low -- which layer 1 correctly refused to
    call a pass.
    """
    n = 0
    base = getattr(tb, "base_tb", None)
    for comp in ("aw_master", "w_master", "b_slave", "ar_master", "r_slave"):
        c = getattr(base, comp, None)
        if c is not None and hasattr(c, "randomizer"):
            c.randomizer = hold; n += 1
    for attr in ("master_components", "slave_components"):
        d = getattr(tb, attr, None)
        if isinstance(d, dict):
            for v in d.values():
                if hasattr(v, "randomizer"):
                    v.randomizer = hold; n += 1
                for sub in ("master", "slave", "interface"):
                    s = getattr(v, sub, None) if not isinstance(v, dict) else v.get(sub)
                    if s is not None and hasattr(s, "randomizer"):
                        s.randomizer = hold; n += 1
    return n


def _monitor_tb_for(dut_name: str):
    """Pick the testbench that matches the wrapper's PORT NAMES.

    The BFM binds by port name, and the twelve wrappers do not share one
    naming: an axi4/axi5 MASTER monitor drives `m_axi_*`, a SLAVE monitor has
    `s_axi_*` upstream and `fub_axi_*` downstream, and the axil4 family uses
    `*_axil_*` throughout. Using the master TB for all twelve -- which this
    file did -- meant eight of them looked for `m_axi_arvalid` on a DUT that
    has no such port, and died in setup with "Missing required signals for
    AR_Slave" before a single transaction was driven.

    That is why block_ready had 16 standing failures: not a monitor defect,
    a testbench bound to the wrong half of the family. The four wrappers it
    did fit (axi4/axi5 master rd/wr) were the only ones ever exercised.
    """
    from TBClasses.axi4.monitor.axi4_slave_monitor_tb import AXI4SlaveMonitorTB
    from TBClasses.axi5.monitor.axi5_master_monitor_tb import AXI5MasterMonitorTB
    from TBClasses.axi5.monitor.axi5_slave_monitor_tb import AXI5SlaveMonitorTB
    from TBClasses.axil4.monitor.axil4_master_monitor_tb import AXIL4MasterMonitorTB
    from TBClasses.axil4.monitor.axil4_slave_monitor_tb import AXIL4SlaveMonitorTB

    is_slave = "_slave_" in dut_name
    if dut_name.startswith("axil4"):
        return AXIL4SlaveMonitorTB if is_slave else AXIL4MasterMonitorTB
    if dut_name.startswith("axi5"):
        return AXI5SlaveMonitorTB if is_slave else AXI5MasterMonitorTB
    return AXI4SlaveMonitorTB if is_slave else AXI4MasterMonitorTB


@cocotb.test(timeout_time=180, timeout_unit="sec")
async def cocotb_test_block_ready(dut):
    """Saturate the table, then check all three layers."""
    dut_name = os.environ["DUT"]
    depth = int(os.environ.get("MAX_TRANSACTIONS", "16"))
    n_txns = int(os.environ.get("TXN_COUNT", "192"))
    is_write = "_wr_" in dut_name

    tb = _monitor_tb_for(dut_name)(dut, is_write=is_write,
                                   aclk=dut.aclk, aresetn=dut.aresetn)
    await tb.initialize()

    # Every cone enabled: a single-cone build drains far faster and may never
    # saturate, which would fail layer 1 rather than exercise layer 3.
    dut.cfg_monitor_enable.value = 1
    dut.cfg_error_enable.value = 1
    dut.cfg_compl_enable.value = 1
    dut.cfg_timeout_enable.value = 1
    dut.cfg_perf_enable.value = 1
    # Long timeout: do not let the timeout path retire slots underneath us, or
    # the table drains for a reason unrelated to what is being measured.
    dut.cfg_timeout_cycles.value = 0xFFFF
    await _wait_clocks(tb, 4)

    chk = BlockReadyCheck(dut, tb.log, depth=depth)
    chk.start()

    # Slow responses keep transactions resident so the table fills through the
    # NORMAL path -- commands still gated by block_ready. This is the difference
    # from the trans_mgr FUB test, which injects unmatched data directly and so
    # constructs the symptom instead of reproducing the cause.
    if hasattr(getattr(tb, "base_tb", None), "set_timing_profile"):
        tb.base_tb.set_timing_profile("slow")

    # Writes need an asymmetric profile. A write entry is held from AW until its
    # B response, so occupancy is built by slow responses -- but the stock
    # 'slow' profile also delays aw/w, which starves injection and caps
    # occupancy at 8/12 however many transactions are queued. Zero command delay
    # against a long response delay is what fills a write table.
    if is_write:
        hold = FlexRandomizer({
            'aw_delay': [(0, 0)],            # commands as fast as the RTL takes
            'w_delay':  [(0, 0)],
            'b_delay':  [(120, 400)],        # responses held -> entries persist
        })
        _apply_hold(tb, hold)
    else:
        # READ side, same intent as the write profile above: commands as fast
        # as the RTL takes them, RESPONSES held so entries stay resident and
        # the table actually fills. This branch did not exist -- reads relied
        # entirely on base_tb.set_timing_profile("slow"), which the axil4
        # testbenches do not have, so the axil4 read wrappers ran at full speed
        # and layer 1 correctly refused to call the run a pass.
        hold = FlexRandomizer({
            'ar_delay': [(0, 0)],
            'r_delay':  [(120, 400)],
        })
        _apply_hold(tb, hold)

    # The six base testbenches spell their one-transaction driver differently
    # -- single_{read,write}_test on the axi4/axi5 masters and the axi5 slaves,
    # single_{read,write}_response_test on the axi4/axil4 slaves, and
    # simple_{read,write}_test on the axil4 masters -- while all of them take
    # (addr) for a read and (addr, data) for a write. Resolve by name once,
    # and FAIL LOUDLY if none is present: a missing driver must not read as a
    # run where the RTL simply never accepted anything.
    drive = _resolve_driver(tb, is_write)

    # CONCURRENT, not sequential. The single-transaction driver awaits
    # completion, so a plain loop keeps exactly one transaction in flight and
    # occupancy never exceeds 1 -- the table cannot fill and the run proves
    # nothing (assert_saturation_reached catches that, and did). Saturation
    # needs many commands outstanding at once, which is what the monitor sees
    # in the real design.
    async def one(i):
        addr = 0x1000 + i * 0x40
        try:
            if is_write:
                # The driver takes (address, data) -- data is REQUIRED. Calling
                # it with the address alone raises TypeError, and swallowing
                # that below reported admitted=0 as if the RTL never accepted a
                # command. Hence the narrow except: a transaction that stalls
                # or is dropped is the thing under test, but a bad call is a
                # bug in this file and must not masquerade as a result.
                await drive(addr, 0xA5A50000 | i)
            else:
                await drive(addr)
        except (TypeError, AttributeError, NameError):
            raise                                 # programming error -- surface it
        except Exception as e:                    # a stalled/dropped txn is
            tb.log.debug(f"txn {i}: {e}")         # the thing under test

    tasks = [cocotb.start_soon(one(i)) for i in range(n_txns)]
    await _wait_clocks(tb, 8000)      # let everything retire
    chk.stop()
    await _wait_clocks(tb, 2)

    tb.log.info(f"{dut_name} MAX_TRANSACTIONS={depth}: {chk.summary()}")

    chk.assert_saturation_reached()
    chk.assert_gating_contract()
    chk.assert_no_untracked_admissions(depth=depth)


# Depths are per-direction because the two paths reach different occupancies.
# A read entry is held from AR to the last R beat and reaches 15/16. A write
# entry is held from AW to B, and the write path tops out around 12 outstanding
# no matter how the randomizers are set (measured: 8/12 symmetric-slow, 14/16
# fast-command, 12/16 with responses held 120-400 cycles). At MAX=16 the margin
# of 1 only blocks at active_count >= 15, which the write path never reaches --
# so a MAX=16 write case could never saturate and would assert-fail forever on
# layer 1. Using depths the path can actually fill keeps the check honest
# instead of tuning the stimulus until a number appears.
def _cases():
    """(wrapper, MAX_TRANSACTIONS) pairs the stimulus can actually SATURATE.

    Depth matters here only insofar as the run fills the table: block_ready
    asserts at depth - CMD_ENTRY_RESERVE, so a depth the stimulus cannot reach
    produces a run that proves nothing, and layer 1 fails it outright rather
    than reporting a hollow pass.

    The AXIL read path tops out around 9-10 concurrent outstanding with this
    testbench -- single-beat, no IDs, one master component shared by every
    task. That clears depth 12 (blocks at 10) and cannot clear depth 16
    (blocks at 14), which is exactly what the two standing failures were: not
    a monitor defect, a depth the stimulus was never able to fill. Until the
    AXIL read stimulus can sustain >14 outstanding, a depth-16 AXIL read case
    is untestable rather than failing, so it is not claimed.

    THE SAME RULE, APPLIED TO THE WRITE PATH AT DEPTH 12 (measured 2026-08-29,
    BLOCKREADY_SEED swept; block_ready asserts at 12 - 3 = 9):

        axi4_slave_wr_mon     peak 10   blocked 383-587 cyc   sustains
        axil4_slave_wr_mon    peak 10   blocked  89-442 cyc   sustains
        axil4_master_wr_mon   peak  9   blocked  88-451 cyc   sustains (7/7 seeds)
        axi5_master_wr_mon    peak 8-9  FAILS at seed 3       does not sustain
        axi5_slave_wr_mon     peak 8-9  FAILS at seed 3       does not sustain
        axi4_master_wr_mon    peak 6-9  FAILS at 5 of 10      does not sustain

    The last three are DROPPED at depth 12, for the same reason AXIL-16 was:
    a depth the stimulus cannot sustain produces a run that proves nothing.
    They are NOT dropped at depth 8, which every one of them fills with real
    margin -- axi4_master_wr_mon blocks for 770-1033 cycles at 7/7 seeds
    tried, versus 11-69 cycles on the rare depth-12 seed that reaches 9.

    This replaces an earlier attempt that pinned a passing seed instead.
    Pinning made the suite green while leaving axi4_master_wr_mon failing on
    half the seed space -- it selected a winning coin toss rather than
    reporting that the coin was being tossed. The seed pin is kept for
    REPRODUCIBILITY, but it is no longer what makes these cases pass.

    Buying depth-12 margin on the weak paths means letting more writes go
    outstanding, which is blocked by the axi4 interface's single _aw_w_lock
    (held across send-AW plus all W beats, so writes serialise whatever their
    ID -- measured with 1, 2, 8 and 32 distinct IDs, byte-identical results).
    That is an RDS-DV change; until then these are untestable, not failing.
    """
    # Write wrappers whose stimulus cannot sustain depth 12 -- see above.
    NO_DEPTH_12 = {"axi4_master_wr_mon", "axi5_master_wr_mon", "axi5_slave_wr_mon"}

    for w in WRAPPERS:
        if "_wr_" in w:
            depths = [8] if w in NO_DEPTH_12 else [8, 12]
        elif w.startswith("axil4"):
            depths = [8, 12]        # see docstring: 16 is unreachable here
        else:
            depths = [12, 16]
        for d in depths:
            yield (w, d)


@pytest.mark.parametrize("dut_name,max_trans", list(_cases()))
def test_axi_mon_block_ready(dut_name, max_trans):
    """Every accepted command must get a table slot -- all 12 wrappers."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({"rtl_amba": "rtl/amba"})

    worker_id = os.environ.get("PYTEST_XDIST_WORKER", "gw0")
    test_name = f"test_{worker_id}_{dut_name}_blockready_mt{max_trans}"
    log_path = os.path.join(log_dir, f"{test_name}.log")
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f"rtl/amba/filelists/{dut_name}.f")

    # Parameter names differ by family -- AXI-Lite uses AXIL_* and has no ID or
    # USER, and passing a name the module does not declare is a hard Verilator
    # error, not a warning. Only MAX_TRANSACTIONS is common, and it is the one
    # that matters here.
    if dut_name.startswith("axil4"):
        rtl_parameters = {
            "AXIL_ADDR_WIDTH": "32", "AXIL_DATA_WIDTH": "32",
            "MAX_TRANSACTIONS": str(max_trans),
        }
    else:
        rtl_parameters = {
            "AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32", "AXI_DATA_WIDTH": "32",
            "AXI_USER_WIDTH": "1",
            "MAX_TRANSACTIONS": str(max_trans),
        }

    with _pinned_seed():
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=os.path.splitext(os.path.basename(__file__))[0],
            testcase="cocotb_test_block_ready",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env={
                "DUT": dut_name,
                "MAX_TRANSACTIONS": str(max_trans),
                "TXN_COUNT": os.environ.get("TXN_COUNT", "1024" if "_wr_" in dut_name else "192"),
                "LOG_PATH": log_path,
                "COCOTB_LOG_LEVEL": "INFO",
                "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                "SEED": _seed(),
            },
            keep_files=True,
            compile_args=["--public-flat-rw", "-Wno-fatal", "--timescale", "1ns/1ps",
                          "--unroll-count", "4096", "--unroll-stmts", "20000"],
        )


# =============================================================================
# ID-range slicing: four monitors snooping one bus, each owning a slice.
#
# The point of the slice is CAPACITY. One monitor on an 8-channel bus with 8
# outstanding per channel needs a 72-entry table, which does not close timing
# here (16 entries measured at WNS +1.018 ns, 40 at -25.183 ns). Four monitors
# owning two channels each need 16.
#
# That only works if a monitor IGNORES ids outside its range. If it still
# allocates for everything, four instances need the full depth and the split
# buys nothing -- while looking like it worked, because the packets and totals
# from each instance are still plausible. Hence the test: drive ids across the
# whole bus, and check the sliced monitor tracked ONLY its own.
# =============================================================================

@cocotb.test(timeout_time=180, timeout_unit="sec")
async def cocotb_test_id_slice(dut):
    """A sliced monitor must ignore ids outside its range."""
    depth = int(os.environ.get("MAX_TRANSACTIONS", "16"))
    base  = int(os.environ.get("ID_MATCH_BASE", "0"))
    count = int(os.environ.get("ID_MATCH_COUNT", "2"))

    tb = AXI4MasterMonitorTB(dut, is_write=False,
                             aclk=dut.aclk, aresetn=dut.aresetn)
    await tb.initialize()
    dut.cfg_monitor_enable.value = 1
    dut.cfg_error_enable.value = 1
    dut.cfg_compl_enable.value = 1
    dut.cfg_timeout_enable.value = 1
    dut.cfg_timeout_cycles.value = 0xFFFF
    await _wait_clocks(tb, 4)

    chk = BlockReadyCheck(dut, tb.log, depth=depth)
    chk.start()
    if hasattr(getattr(tb, "base_tb", None), "set_timing_profile"):
        tb.base_tb.set_timing_profile("slow")

    # Spread ids 0..7 evenly; only [base, base+count) belong to this instance.
    n_txns = 128
    async def one(i):
        try:
            await tb.base_tb.single_read_test(0x1000 + i * 0x40, arid=(i % 8))
        except (TypeError, AttributeError, NameError):
            raise
        except Exception as e:
            tb.log.debug(f"txn {i}: {e}")

    for i in range(n_txns):
        cocotb.start_soon(one(i))
    await _wait_clocks(tb, 6000)
    chk.stop()
    await _wait_clocks(tb, 2)

    owned_frac = count / 8.0
    tb.log.info(f"slice=[{base},{base + count}) of 8 ids -> "
                f"{owned_frac:.0%} of traffic owned; {chk.summary()}")

    # Occupancy is the measurement that matters: it is what the table has to
    # hold, and therefore what sets the depth the slice is supposed to reduce.
    assert chk.peak_occupancy <= depth, (
        f"occupancy peaked at {chk.peak_occupancy} with {depth} entries")

    # With 2 of 8 ids owned, the table must stay near a quarter of what an
    # unfiltered monitor would hold. The bound is loose (ungated data/resp
    # orphans and in-flight skew both add a little) but it is far below the
    # unfiltered case, which is the whole claim.
    bound = max(4, int(depth * owned_frac) + 6)
    assert chk.peak_occupancy <= bound, (
        f"peak occupancy {chk.peak_occupancy} for a {count}/8 slice exceeds "
        f"{bound}: the monitor is still allocating for ids it does not own, so "
        f"four parallel instances would each need the FULL table and the split "
        f"saves nothing. Check ID_FILTER_ENABLE reached axi_monitor_base.")
    tb.log.info(f"slice confirmed: peak {chk.peak_occupancy} <= {bound}")


# Four instances owning two channels each is the shape that lets an 8-channel
# bus be tracked at all: 4 x 16 entries instead of 1 x 72. Each parametrization
# below is one of those instances.
@pytest.mark.parametrize("ch_base", [0, 2, 4, 6])
def test_axi_mon_id_slice(ch_base):
    """A monitor sliced to 2 of 8 ids must not allocate for the other 6."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({"rtl_amba": "rtl/amba"})

    dut_name = "axi4_master_rd_mon"
    max_trans, count = 16, 2
    worker_id = os.environ.get("PYTEST_XDIST_WORKER", "gw0")
    test_name = f"test_{worker_id}_{dut_name}_idslice_ch{ch_base}"
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f"rtl/amba/filelists/{dut_name}.f")

    with _pinned_seed():
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=os.path.splitext(os.path.basename(__file__))[0],
            testcase="cocotb_test_id_slice",
            parameters={
                "AXI_ID_WIDTH": "8", "AXI_ADDR_WIDTH": "32", "AXI_DATA_WIDTH": "32",
                "AXI_USER_WIDTH": "1",
                "MAX_TRANSACTIONS": str(max_trans),
                "ID_FILTER_ENABLE": "1",
                "ID_MATCH_BASE": str(ch_base),
                "ID_MATCH_COUNT": str(count),
            },
            sim_build=sim_build,
            extra_env={
                "DUT": dut_name,
                "MAX_TRANSACTIONS": str(max_trans),
                "ID_MATCH_BASE": str(ch_base),
                "ID_MATCH_COUNT": str(count),
                "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                "COCOTB_LOG_LEVEL": "INFO",
                "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
                "SEED": _seed(),
            },
            keep_files=True,
            compile_args=["--public-flat-rw", "-Wno-fatal", "--timescale", "1ns/1ps",
                          "--unroll-count", "4096", "--unroll-stmts", "20000"],
        )

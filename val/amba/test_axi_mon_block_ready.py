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

import os

import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.axi_monitor.block_ready_check import BlockReadyCheck
from TBClasses.axi4.monitor.axi4_master_monitor_tb import AXI4MasterMonitorTB


# Wrappers under test. Every one instantiates axi_monitor_base, so every one
# inherits the gate -- axi4_intf_observer is a thin wrapper over these, which is
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


@cocotb.test(timeout_time=180, timeout_unit="sec")
async def cocotb_test_block_ready(dut):
    """Saturate the table, then check all three layers."""
    dut_name = os.environ["DUT"]
    depth = int(os.environ.get("MAX_TRANSACTIONS", "16"))
    n_txns = int(os.environ.get("TXN_COUNT", "192"))
    is_write = "_wr_" in dut_name

    tb = AXI4MasterMonitorTB(dut, is_write=is_write,
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
    await tb.base_tb.wait_clocks("aclk", 4)

    chk = BlockReadyCheck(dut, tb.log, depth=depth)
    chk.start()

    # Slow responses keep transactions resident so the table fills through the
    # NORMAL path -- commands still gated by block_ready. This is the difference
    # from the trans_mgr FUB test, which injects unmatched data directly and so
    # constructs the symptom instead of reproducing the cause.
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
        for comp in ("aw_master", "w_master", "b_slave"):
            c = getattr(tb.base_tb, comp, None)
            if c is not None and hasattr(c, "randomizer"):
                c.randomizer = hold

    # CONCURRENT, not sequential. single_read_test/single_write_test await
    # completion, so a plain loop keeps exactly one transaction in flight and
    # occupancy never exceeds 1 -- the table cannot fill and the run proves
    # nothing (assert_saturation_reached catches that, and did). Saturation
    # needs many commands outstanding at once, which is what the monitor sees
    # in the real design.
    async def one(i):
        addr = 0x1000 + i * 0x40
        try:
            if is_write:
                # single_write_test(address, data) -- data is REQUIRED. Calling
                # it with the address alone raises TypeError, and swallowing
                # that below reported admitted=0 as if the RTL never accepted a
                # command. Hence the narrow except: a transaction that stalls
                # or is dropped is the thing under test, but a bad call is a
                # bug in this file and must not masquerade as a result.
                await tb.base_tb.single_write_test(addr, 0xA5A50000 | i)
            else:
                await tb.base_tb.single_read_test(addr)
        except (TypeError, AttributeError, NameError):
            raise                                 # programming error -- surface it
        except Exception as e:                    # a stalled/dropped txn is
            tb.log.debug(f"txn {i}: {e}")         # the thing under test

    tasks = [cocotb.start_soon(one(i)) for i in range(n_txns)]
    await tb.base_tb.wait_clocks("aclk", 8000)      # let everything retire
    chk.stop()
    await tb.base_tb.wait_clocks("aclk", 2)

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
    for w in WRAPPERS:
        for d in ([8, 12] if "_wr_" in w else [12, 16]):
            yield (w, d)


@pytest.mark.parametrize("dut_name,max_trans", list(_cases()))
def test_axi_mon_block_ready(dut_name, max_trans):
    """Every accepted command must get a table slot -- all 12 wrappers."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({"rtl_amba": "rtl/amba"})

    worker_id = os.environ.get("PYTEST_XDIST_WORKER", "gw0")
    test_name = f"test_{worker_id}_{dut_name}_blockready_mt{max_trans}"
    log_path = os.path.join(log_dir, f"{test_name}.log")
    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
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
            "SEED": os.environ.get("SEED", "12345"),
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
    await tb.base_tb.wait_clocks("aclk", 4)

    chk = BlockReadyCheck(dut, tb.log, depth=depth)
    chk.start()
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
    await tb.base_tb.wait_clocks("aclk", 6000)
    chk.stop()
    await tb.base_tb.wait_clocks("aclk", 2)

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
    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f"rtl/amba/filelists/{dut_name}.f")

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
            "SEED": os.environ.get("SEED", "12345"),
        },
        keep_files=True,
        compile_args=["--public-flat-rw", "-Wno-fatal", "--timescale", "1ns/1ps",
                      "--unroll-count", "4096", "--unroll-stmts", "20000"],
    )

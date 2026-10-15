"""
amber_top boundary reset synchronizer -- directed test.

The control FSM resets into its init-walk state, so the init walk is the
first thing the core does after reset release. Deasserting aresetn at a
deliberately asynchronous (mid-cycle) instant starts the walk at the next
clock edge if the port reset is fanned out directly, or N+walk cycles
later once a reset_sync (N=3) sits at the boundary. The test counts clock
edges from deassert to init_busy falling and enforces the synchronized
bound, then smoke-checks normal request acceptance and the async-assert
contract.

Geometry is pinned small (4 sets) so the walk is a handful of cycles and
the +N sync latency is resolvable. Memory/snoop/sideband inputs stay
idle: acceptance precedes any downstream response.

Author: RTL Design Sherpa
Created: 2026-10-14
"""

import os
import sys

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, Timer, ReadOnly
from cocotb_test.simulator import run

from TBClasses.shared.utilities import (get_paths, create_view_cmd,
                                        get_repo_root, sim_build_path)
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

FILELIST_DIR = 'projects/components/cache-ip/amber-mesi-l1/rtl/filelists'
DUT_TOP = 'amber_top'
TEST_PREFIX = 'amber_top_reset_sync'

# Small geometry: init walk = SETS cycles + 2 (registered exit + fall).
GEOM = dict(SETS=4, WAYS=2, LINE_BYTES=32, BUS_WIDTH=32, REPL_POLICY=0,
            USE_MONITOR=0)
# Measured pre-fix completion = 4 cycles (SETS=4 walk + registered exit).
# The internal reset_sync (N=3) adds exactly 3. Bound = measured + N.
MIN_INIT_COMPLETE_CYCLES = 7


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_amber_top_reset_sync(dut):
    clock = Clock(dut.aclk, 10, unit="ns")
    cocotb.start_soon(clock.start())

    # Tie every input idle; the test observes the init-walk status and
    # request acceptance, which precede any downstream response.
    dut.aresetn.value = 0
    dut.cpu_req_wr_valid.value = 0
    dut.cpu_req_wr_data.value = 0
    dut.cpu_rsp_rd_ready.value = 1
    dut.m_axi_arready.value = 0
    dut.m_axi_rid.value = 0
    dut.m_axi_rdata.value = 0
    dut.m_axi_rresp.value = 0
    dut.m_axi_rlast.value = 0
    dut.m_axi_ruser.value = 0
    dut.m_axi_rvalid.value = 0
    dut.m_axi_awready.value = 0
    dut.m_axi_wready.value = 0
    dut.m_axi_bid.value = 0
    dut.m_axi_bresp.value = 0
    dut.m_axi_buser.value = 0
    dut.m_axi_bvalid.value = 0
    dut.m_axi_acaddr.value = 0
    dut.m_axi_acsnoop.value = 0
    dut.m_axi_acprot.value = 0
    dut.m_axi_acvalid.value = 0
    dut.m_axi_crready.value = 0
    dut.m_axi_cdready.value = 0
    dut.i_mon_time.value = 0
    dut.mon_ready.value = 1

    # Hold reset through several edges, then deassert asynchronously:
    # two nanoseconds after a falling edge, off every clock boundary.
    for _ in range(5):
        await RisingEdge(dut.aclk)
    await FallingEdge(dut.aclk)
    await Timer(2, "ns")
    dut.aresetn.value = 1

    # Count edges from deassert until the init walk completes.
    cycles = 0
    done = False
    while cycles < 200:
        await RisingEdge(dut.aclk)
        await ReadOnly()
        cycles += 1
        if dut.init_busy.value == 0:
            done = True
            break
    assert done, "init walk never completed after reset release"
    assert cycles >= MIN_INIT_COMPLETE_CYCLES, (
        f"init walk completed {cycles} clock(s) after asynchronous reset "
        f"deassert -- amber_top forwarded the port reset directly instead "
        f"of synchronizing it internally (expected >= "
        f"{MIN_INIT_COMPLETE_CYCLES})")

    # Functional smoke: with the walk done, present a read request
    # mid-cycle. The FSM is receptive combinationally while idle (ready
    # high before the edge) and consumes the request at the next edge.
    await FallingEdge(dut.aclk)
    dut.cpu_req_wr_valid.value = 1
    await Timer(1, "ns")
    await ReadOnly()
    assert dut.cpu_req_wr_ready.value == 1, (
        "req-ready not receptive after init walk")
    await RisingEdge(dut.aclk)
    await ReadOnly()
    assert int(dut.ctrl_state.value) != 0, (
        "request presented to idle FSM was not consumed")
    await FallingEdge(dut.aclk)
    dut.cpu_req_wr_valid.value = 0

    # Async-assert contract: a mid-cycle assertion must drop the FSM back
    # into the init state without waiting for a clock edge -- even mid-
    # transaction (the request above left the FSM waiting in MISS_FILL).
    await FallingEdge(dut.aclk)
    await Timer(2, "ns")
    dut.aresetn.value = 0
    await Timer(1, "ns")
    await ReadOnly()
    assert dut.init_busy.value == 1, (
        "mid-cycle reset assertion did not re-enter init asynchronously")


def test_amber_top_reset_sync(request):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'{FILELIST_DIR}/amber_top.f')

    test_name = TEST_PREFIX
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')

    extra_env = {
        'DUT': DUT_TOP,
        'LOG_PATH': log_path,
        'COCOTB_RESULTS_FILE': results_path,
        'COCOTB_LOG_LEVEL': 'INFO',
    }

    compile_args = (["--trace-fst", "--trace-structs", "--trace-depth", "99"]
                    if enable_waves else [])
    plusargs = ["+trace"] if enable_waves else []

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module,
                                   test_name)
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=DUT_TOP,
        module=module,
        testcase="cocotb_test_amber_top_reset_sync",
        parameters={k: str(v) for k, v in GEOM.items()},
        sim_build=sim_build,
        extra_env=extra_env,
        waves=enable_waves,
        keep_files=True,
        compile_args=compile_args,
        plusargs=plusargs,
    )

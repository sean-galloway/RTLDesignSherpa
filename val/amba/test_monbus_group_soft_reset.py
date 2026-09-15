"""TASK-084: does a mid-run reset restore the monbus group's ability to emit?

The board symptom: on Genesys 2 `build-mon`, a scenario emits its packets only
when it is the FIRST thing run after the bitstream is programmed. Run anything
before it and it emits ZERO. Only REPROGRAMMING recovers -- and programming is
what asserts the global aresetn. Every scenario already begins with
CTRL.SOFT_RESET, which drives unit_aresetn and provably clears the monitor CSRs
(cocotb_test_soft_reset_scope), so the surviving state is NOT configuration.

TASK-084's own next step is "instrument reporter grants and monbus group FIFO
occupancy in cosim across two back-to-back scenarios, rather than reasoning from
CSR reads". This is that probe at the GROUP level: two identical back-to-back
batches separated by a reset pulse, with the group's FIFO occupancy sampled
either side.

This is a REPRODUCTION ATTEMPT, and both outcomes are informative:
  * batch 2 emits ~0  -> reproduced in cosim at the group level; the surviving
    state is inside monbus_*_group and can be bisected here.
  * batch 2 == batch 1 -> the group resets cleanly, so the board's surviving
    state is NOT here. That points at u_stream / the monitors, and eliminates a
    whole subsystem without a board run.

The criterion is READ-SIDE and that is the whole point. An earlier draft of
this test keyed on test_basic_packet_flow, whose success_rate counts
send_packet() returns -- i.e. the GAXI master accepting packets INTO the group.
That is the stimulus, not the emission: it reads 1.0 even if the group emits
nothing, so it could never have detected the defect. Records drained back out
through the AXIL slave-read port are the only honest measure here.

Deliberately NOT asserted: that the two batches match exactly. The point is
whether the second batch is ALIVE, not whether it is bit-identical.
"""
import os
import sys

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import (get_paths, create_view_cmd,
                                        get_repo_root, sim_build_path)
from TBClasses.shared.filelist_utils import get_sources_from_filelist
import TBClasses.amba.monbus_axil4_axil4_group.monbus_axil4_axil4_group_tb as _tbmod
from TBClasses.amba.monbus_axil4_axil4_group.monbus_axil4_axil4_group_tb import (
    MonbusAxilAxilGroupTB)

PktType = _tbmod.PktType

RESET_CLOCKS = 16          # matches the board's SOFT_RESET pulse width
BATCH = 16


async def _fill(tb, count, tag):
    """Drive `count` packets across BOTH FIFO paths, and do NOT drain them.

    cfg_axi_err_select routes ERROR packets to the err FIFO; everything else
    lands in the write FIFO. An all-ERROR fill leaves write_fifo_count at 0,
    which makes the post-reset "write FIFO is clear" assertion VACUOUS -- it
    would hold because that path was never exercised, not because the reset
    cleared it. Measured: an all-ERROR fill gives err=16 write=0, a mixed fill
    gives both non-zero.
    """
    for i in range(count):
        is_err = (i % 2 == 0)
        await tb.send_packet(tb.create_monbus_packet_dict(
            pkt_type=PktType.PktTypeError if is_err else PktType.PktTypeCompletion,
            event_code=0x1 if is_err else 0x0,
            channel_id=i & 0x1FF, data=(tag << 16) + i))
        await tb.wait_clocks(tb.clk_name, 2)
    await tb.wait_clocks(tb.clk_name, 50)


def _fifo_counts(dut):
    return (int(dut.err_fifo_count.value), int(dut.write_fifo_count.value))


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_monbus_group_soft_reset_reissue(dut):
    tb = MonbusAxilAxilGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.setup_interfaces()

    # ---- Phase A: fill without draining --------------------------------
    await _fill(tb, BATCH, 0xA)
    err_a, wr_a = _fifo_counts(dut)
    tb.log.info(f"[TASK-084] phase A (filled, undrained): "
                f"err_fifo_count={err_a} write_fifo_count={wr_a}")

    # ---- Phase B: the reset the campaign pulses between scenarios ------
    await tb.assert_reset()
    await tb.wait_clocks(tb.clk_name, RESET_CLOCKS)
    await tb.deassert_reset()
    await tb.wait_clocks(tb.clk_name, 5)
    err_b, wr_b = _fifo_counts(dut)
    tb.log.info(f"[TASK-084] phase B (after reset):        "
                f"err_fifo_count={err_b} write_fifo_count={wr_b}")

    # The GAXI driver is not reset-aware; re-arm exactly as a fresh
    # scenario would.
    await tb.setup_interfaces()

    # ---- Phase C: full drive-and-DRAIN after a predecessor -------------
    ok_c, stats_c = await tb.test_error_fifo_decode(count=8)
    err_c, wr_c = _fifo_counts(dut)
    tb.log.info(f"[TASK-084] phase C (post-reset decode): ok={ok_c} "
                f"stats={stats_c} err_fifo_count={err_c} write_fifo_count={wr_c}")

    # ARMED FIRST: if phase A never filled, phases B and C say nothing.
    assert err_a > 0 and wr_a > 0, (
        f"phase A drove {BATCH} packets but did not fill BOTH FIFO paths "
        f"(err={err_a} write={wr_a}); phase B's 0/0 check is only meaningful "
        f"for a path that actually held state, so an unfilled path would make "
        f"that assertion pass vacuously.")

    # The reset must actually clear the group's buffered state.
    assert err_b == 0 and wr_b == 0, (
        f"group FIFOs survived the reset pulse: err={err_b} write={wr_b} "
        f"(expected 0/0), having been {err_a}/{wr_a} before it. Retained state "
        f"across reset is a direct TASK-084 candidate.")

    # THE REGRESSION, measured on the OUTPUT side: a scenario must not be dead
    # merely because one ran before it.
    assert ok_c, (
        f"post-reset drain FAILED: {stats_c}. Packets driven after a reset that "
        f"followed prior traffic did not come back out of the err-FIFO. This "
        f"reproduces the board's order dependence in cosim at the monbus group "
        f"level. NOTE before blaming RTL: tb.mon is built in __init__ and "
        f"survives the reset, so rule out stale harness drain state first. "
        f"TASK-084.")
    assert stats_c.get('records') == stats_c.get('expected'), (
        f"post-reset drain returned {stats_c.get('records')} of "
        f"{stats_c.get('expected')} records: {stats_c}")


@pytest.mark.parametrize("fifo_depth_err, fifo_depth_write, addr_width, "
                         "num_protocols, s_axil_data_width",
                         [(16, 64, 32, 1, 64)])
def test_monbus_group_soft_reset(request, fifo_depth_err, fifo_depth_write,
                                 addr_width, num_protocols, s_axil_data_width):
    """TASK-084: back-to-back scenarios across a reset pulse."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_includes': 'rtl/amba/includes',
        'rtl_shared':   'rtl/amba/shared',
        'rtl_monitor':  'rtl/amba/monitor',
        'rtl_axil4':    'rtl/amba/axil4',
        'rtl_gaxi':     'rtl/amba/gaxi',
        'rtl_common':   'rtl/common',
    })

    dut_name = "monbus_axil4_axil4_group"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/monbus_axil4_axil4_group.f")
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name_plus_params = f"test_{worker_id}_{dut_name}_soft_reset"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    includes = includes + [rtl_dict['rtl_common'], sim_build]

    rtl_parameters = {
        'FIFO_DEPTH_ERR':    fifo_depth_err,
        'FIFO_DEPTH_WRITE':  fifo_depth_write,
        'ADDR_WIDTH':        addr_width,
        'NUM_PROTOCOLS':     num_protocols,
        'S_AXIL_DATA_WIDTH': s_axil_data_width,
    }
    extra_env = {
        'LOG_PATH': log_path,
        'TEST_TYPE': 'basic_flow',
        'TEST_FIFO_DEPTH_ERR':    str(fifo_depth_err),
        'TEST_FIFO_DEPTH_WRITE':  str(fifo_depth_write),
        'TEST_ADDR_WIDTH':        str(addr_width),
        'TEST_NUM_PROTOCOLS':     str(num_protocols),
        'TEST_S_AXIL_DATA_WIDTH': str(s_axil_data_width),
    }
    create_view_cmd(log_dir, log_path, sim_build,
                    'test_monbus_group_soft_reset', test_name_plus_params)

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=os.path.splitext(os.path.basename(__file__))[0],
        testcase="cocotb_test_monbus_group_soft_reset_reissue",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        compile_args=["-Wno-TIMESCALEMOD", "-Wno-SELRANGE",
                      "-Wno-WIDTHEXPAND", "-Wno-WIDTH"],
    )

# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_cg_peer_ready
# Purpose: a parked peer READY must not prevent the clock from gating
#
# Documentation: vault/handbook/design/clock-gating-activity-terms.md
# Subsystem: amba
#
# Author: sean galloway
# Created: 2026-09-02
"""An idle bus must gate, even with the peer's READY parked high.

`vault/handbook/design/clock-gating-activity-terms.md` states the rule as its
first bullet: peer VALID, never peer READY. A consumer that holds its
response-ready high while idle is behaving correctly, and folding that into the
activity term pins the block permanently awake -- the wrapper's only feature,
silently dead, with function unaffected so nothing fails.

That rule was recorded as "fixed family-wide" after an axi4/axi5 sweep. It was
not: ten more wrappers (axil4 x4, axil5 x4, axis4 x2) still had it on
2026-09-02, and `test_mon_cg_gating.py` could not see them -- its DUT table
generates only `*_mon_cg` names, so every plain `_cg` wrapper was unreachable
by any gating test. The whole suite passed identically before and after the
fix.

This file covers the plain `_cg` wrappers, and asserts the property the rule is
about rather than the shape of the expression.
"""
import os

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist


# dut -> (upstream valids to hold low, the peer READY to PARK HIGH)
DUTS = {
    'axil4_master_rd_cg': (['fub_arvalid'], 'fub_rready'),
    'axil4_master_wr_cg': (['fub_awvalid', 'fub_wvalid'], 'fub_bready'),
    'axil4_slave_rd_cg':  (['s_axil_arvalid'], 's_axil_rready'),
    'axil4_slave_wr_cg':  (['s_axil_awvalid', 's_axil_wvalid'], 's_axil_bready'),
    'axil5_master_rd_cg': (['fub_arvalid'], 'fub_rready'),
    'axil5_master_wr_cg': (['fub_awvalid', 'fub_wvalid'], 'fub_bready'),
    'axil5_slave_rd_cg':  (['s_axil_arvalid'], 's_axil_rready'),
    'axil5_slave_wr_cg':  (['s_axil_awvalid', 's_axil_wvalid'], 's_axil_bready'),
    'axis4_master_cg':     (['fub_axis_tvalid'], 'm_axis_tready'),
    'axis4_slave_cg':      (['s_axis_tvalid'], 'fub_axis_tready'),
    # axis5 was not in the peer-READY sweep -- its wrappers were already clean
    # there -- but it IS in scope for the outward-READY mask below, which is
    # where they turned out to differ from their axis4 siblings.
    'axis5_master_cg':     (['fub_axis5_tvalid'], 'm_axis5_tready'),
    'axis5_slave_cg':      (['s_axis_tvalid'], 'fub_axis5_tready'),
}

IDLE_COUNT = 4


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def idle_bus_gates_with_peer_ready_parked(dut):
    """Hold every VALID low, park the peer READY high, expect cg_gating."""
    name = os.environ['DUT']
    valids, peer_ready = DUTS[name]

    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())

    dut.aresetn.value = 0
    dut.cfg_cg_enable.value = 1
    dut.cfg_cg_idle_count.value = IDLE_COUNT
    for v in valids:
        getattr(dut, v).value = 0
    # The whole point: a well-behaved consumer parks its READY high while idle.
    getattr(dut, peer_ready).value = 1
    for _ in range(8):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1

    # Gating asserts cfg_cg_idle_count + 2 cycles after the last activity
    # (one extra for the r_wakeup flop). Allow generous margin.
    for _ in range(IDLE_COUNT + 20):
        await RisingEdge(dut.aclk)

    gating = int(dut.cg_gating.value)
    dut._log.info(f"{name}: {peer_ready} parked high, all valids low -> "
                  f"cg_gating={gating}")
    assert gating == 1, (
        f"{name} never gated. Every VALID was low for {IDLE_COUNT + 20} cycles "
        f"with only {peer_ready} (a PEER's ready) high. If that signal is in "
        f"the activity term, this block can never gate against a consumer that "
        f"parks its ready -- see "
        f"vault/handbook/design/clock-gating-activity-terms.md"
    )


@pytest.mark.parametrize('dut_name', sorted(DUTS.keys()))
def test_cg_peer_ready(request, dut_name):
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba_includes': 'rtl/amba/includes'})

    test_name = f"test_{worker_id}_{dut_name}_peer_ready"
    sim_build = sim_build_path(tests_dir, test_name)
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
        compile_args=["-Wno-WIDTH", "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE",
                      "-Wno-BLKANDNBLK", "--timescale", "1ns/1ps"],
        parameters={'CG_IDLE_COUNT_WIDTH': '4'},
        sim_build=sim_build,
        extra_env={
            'DUT': dut_name,
            'LOG_PATH': os.path.join(log_dir, f'{test_name}.log'),
            'COCOTB_LOG_LEVEL': 'INFO',
        },
        waves=False,
        keep_files=True,
    )


# --- outward READY must be masked while the clock is gated -------------------
# A wrapper's outward READY is driven by a register on the GATED clock. When
# that clock stops the register holds its last value -- it does not fall. If
# READY was high at the moment gating engaged, a peer sees a still-asserted
# READY, drives a beat, and considers it accepted while the gated logic never
# observes it. The beat is lost.
#
# axis4_slave_cg guards this explicitly:
#     assign s_axis_tready = cg_gating ? 1'b0 : int_tready;
# and the axil4/axi4 families do the same for their AW/W/AR readys. The axis5
# wrappers did not, while their doc pages claimed the READY "stays low while
# the clock is stopped" -- describing the sibling's behaviour, not their own.
# Raised as a SUSPECTED finding by qc round_35 (TASK-076), confirmed here.

# The wrapper's OWN output, i.e. the READY it drives toward its producer.
# A master's producer is on the fub side; a slave's is the s_axis side. Getting
# this backwards tests an input the wrapper does not control.
READY_OUT = {
    'axis4_master_cg':    'fub_axis_tready',
    'axis4_slave_cg':     's_axis_tready',
    'axis5_master_cg':    'fub_axis5_tready',
    'axis5_slave_cg':     's_axis_tready',
}


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def outward_ready_is_masked_while_gated(dut):
    """Once cg_gating is high, the outward READY must read 0."""
    name = os.environ['DUT']
    valids, peer_ready = DUTS[name]
    ready_out = READY_OUT.get(name)
    if ready_out is None or not hasattr(dut, ready_out):
        return                      # not a stream wrapper; nothing to assert

    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    dut.aresetn.value = 0
    dut.cfg_cg_enable.value = 1
    dut.cfg_cg_idle_count.value = IDLE_COUNT
    for v in valids:
        getattr(dut, v).value = 0
    getattr(dut, peer_ready).value = 1
    for _ in range(8):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1

    for _ in range(IDLE_COUNT + 20):
        await RisingEdge(dut.aclk)

    gating = int(dut.cg_gating.value)
    assert gating == 1, f"{name} never gated; cannot test the mask"
    rdy = int(getattr(dut, ready_out).value)
    dut._log.info(f"{name}: cg_gating=1 -> {ready_out}={rdy}")
    assert rdy == 0, (
        f"{name}: {ready_out} is {rdy} while cg_gating is high. A peer sees an "
        f"asserted READY, drives a beat, and the gated logic never observes it "
        f"-- the beat is lost. Mask it with !cg_gating, as axis4_slave_cg does."
    )

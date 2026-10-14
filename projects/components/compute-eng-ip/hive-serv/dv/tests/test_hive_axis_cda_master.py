# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_hive_axis_cda_master
# Purpose: TDD test for the HIVE-C AXI4-Stream CDA descriptor master
#
# Documentation: projects/components/compute-eng-ip/hive-serv/docs/hive_has/ch04_interfaces/02_packet_formats.md
# Subsystem: hive-serv
#
# Author: sean galloway
# Created: 2026-10-13

"""
Test for hive_axis_cda_master

Drives 256-bit CDA descriptors into the AXI4-Stream master and checks:
  - CDA-01: constant sidebands (tuser=2'b01, tdest=16, tlast=1) on every beat
  - CDA-02: single-outstanding handshake discipline; no retraction of tvalid/data
  - CDA-03: tready stall absorption with randomized stall patterns
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer, ReadOnly
from cocotb_test.simulator import run

# Import framework utilities (PYTHONPATH includes bin/)
from TBClasses.shared.utilities import get_repo_root, sim_build_path
from TBClasses.shared.test_levels import current_level, level_env, reg_level_grid
from cov_utils.conftest_coverage import get_coverage_compile_args

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)


# Depth by level. gate is a quick smoke; func exercises randomized stalls.
_LVL = current_level()
_D = {'gate': dict(beats=8,  stall_max=8,  seed=0x5A5A),
      'func': dict(beats=64, stall_max=32, seed=None)}[_LVL]
_TIMEOUT_US = {'gate': 40, 'func': 120}[_LVL]


@cocotb.test(timeout_time=_TIMEOUT_US, timeout_unit='us')
async def cocotb_test_hive_axis_cda_master(dut):
    """TDD test for hive_axis_cda_master"""

    log = dut._log
    log.info("=" * 80)
    log.info("Starting hive_axis_cda_master TDD test")
    log.info(f"TEST_LEVEL={_LVL}")
    log.info("=" * 80)

    cfg = _D
    if cfg['seed'] is not None:
        random.seed(cfg['seed'])

    # Clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst_n.value = 0
    dut.s_desc.value = 0
    dut.s_valid.value = 0
    dut.m_axis_tready.value = 0

    await Timer(100, units="ns")
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    await RisingEdge(dut.clk)
    log.info("Reset complete")

    # Protocol checker: continuous assertions for CDA-01 and CDA-02 (retraction).
    async def protocol_checker():
        prev_tvalid = 0
        prev_tready = 0
        captured_tdata = None
        while True:
            await RisingEdge(dut.clk)
            if dut.rst_n.value == 0:
                prev_tvalid = 0
                prev_tready = 0
                captured_tdata = None
                continue

            tvalid = int(dut.m_axis_tvalid.value)
            tready = int(dut.m_axis_tready.value)
            tdata = int(dut.m_axis_tdata.value)
            tuser = int(dut.m_axis_tuser.value)
            tdest = int(dut.m_axis_tdest.value)
            tlast = int(dut.m_axis_tlast.value)

            # CDA-01: sidebands are constant on every presented beat.
            if tvalid:
                assert tuser == 0b01, f"CDA-01: tuser={tuser:02b}, expected 2'b01"
                assert tdest == 16, f"CDA-01: tdest={tdest}, expected 8'd16"
                assert tlast == 1, f"CDA-01: tlast={tlast}, expected 1'b1"

            # CDA-02: no retraction / stability during stall.
            if prev_tvalid and not prev_tready:
                assert tvalid == 1, "CDA-02: tvalid retracted while tready was low"
                assert tdata == captured_tdata, (
                    f"CDA-02: tdata changed during stall: "
                    f"0x{tdata:064x} != 0x{captured_tdata:064x}"
                )
            elif tvalid:
                captured_tdata = tdata

            prev_tvalid = tvalid
            prev_tready = tready

    cocotb.start_soon(protocol_checker())

    # Consumer coroutine: drives m_axis_tready with randomized stall patterns.
    beats_received = 0
    received_data = []

    async def consumer():
        nonlocal beats_received, received_data
        while True:
            await RisingEdge(dut.clk)
            if dut.rst_n.value == 0:
                continue

            # If a beat is completing this cycle, record it.
            if dut.m_axis_tvalid.value == 1 and dut.m_axis_tready.value == 1:
                beats_received += 1
                received_data.append(int(dut.m_axis_tdata.value))

            # Randomize next-cycle tready.
            if random.random() < 0.3:
                # Insert a stall burst of 1..stall_max cycles.
                stall = random.randint(1, cfg['stall_max'])
                dut.m_axis_tready.value = 0
                for _ in range(stall):
                    await RisingEdge(dut.clk)
                    if dut.rst_n.value == 0:
                        break
                    # Still record any completion that happens during the stall
                    # setup window (should not happen because we just set 0).
                    if dut.m_axis_tvalid.value == 1 and dut.m_axis_tready.value == 1:
                        beats_received += 1
                        received_data.append(int(dut.m_axis_tdata.value))
                dut.m_axis_tready.value = 1
            else:
                dut.m_axis_tready.value = 1

    # Helper to sample the combinational s_ready after simulator settles.
    # Reads happen in the ReadOnly phase; the 1 ps advance exits that phase so
    # the caller may legally drive signals afterwards.
    async def get_s_ready():
        await ReadOnly()
        v = int(dut.s_ready.value)
        await Timer(1, units="ps")
        return v

    cocotb.start_soon(consumer())

    # Drive descriptors and verify CDA-02/03 in the main loop.
    sent_data = []
    for i in range(cfg['beats']):
        desc = (random.getrandbits(256) & ((1 << 256) - 1))
        # Ensure uniqueness for the final ordering check.
        desc |= (i << 224)
        sent_data.append(desc)

        # Wait until the module can accept a new descriptor (s_ready == 1).
        while await get_s_ready() != 1:
            await RisingEdge(dut.clk)

        # Present descriptor and assert valid.
        dut.s_desc.value = desc
        dut.s_valid.value = 1
        await RisingEdge(dut.clk)
        # s_ready is combinational; sample after the edge settles.
        s_ready_after = await get_s_ready()

        # Descriptor accepted this cycle; s_ready must drop because we are now busy.
        assert s_ready_after == 0, "CDA-02: s_ready stayed high after accepting a descriptor"
        dut.s_valid.value = 0
        dut.s_desc.value = 0

        # Wait for the AXIS handshake to complete.
        while not (dut.m_axis_tvalid.value == 1 and dut.m_axis_tready.value == 1):
            await RisingEdge(dut.clk)

        log.info(f"Descriptor {i}: handshake complete")

    # Drain a few cycles so the consumer records the last beat.
    await Timer(50, units="ns")

    # CDA-03 / integrity: every sent descriptor arrived exactly once, in order.
    assert beats_received == cfg['beats'], (
        f"CDA-03: received {beats_received} beats, expected {cfg['beats']}"
    )
    assert received_data == sent_data, (
        f"CDA-03: data ordering mismatch. "
        f"first diff at index {next((j for j in range(len(received_data)) if received_data[j] != sent_data[j]), 'none')}"
    )

    log.info("=" * 80)
    log.info(f"hive_axis_cda_master test PASSED at {_LVL} level")
    log.info(f"Descriptors sent/received: {cfg['beats']}")
    log.info("=" * 80)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_hive_axis_cda_master(request, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    """Pytest wrapper for hive_axis_cda_master"""

    rtl_path = os.path.join(
        repo_root,
        'projects/components/compute-eng-ip/hive-serv/rtl/hive_c_controller/axis4_master.sv'
    )
    verilog_sources = [rtl_path]
    includes = [os.path.join(repo_root, 'rtl/amba/includes')]

    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
        "--no-timing",
    ]
    for inc in includes:
        compile_args.append(f"+incdir+{inc}")
    compile_args.extend(get_coverage_compile_args())

    module = os.path.splitext(os.path.basename(__file__))[0]
    tests_dir = os.path.dirname(__file__)
    log_dir = os.path.join(tests_dir, 'logs')
    os.makedirs(log_dir, exist_ok=True)

    test_name = f'{module}_{test_level}'
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)

    run(
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="hive_axis_cda_master",
        module=module,
        simulator="verilator",
        compile_args=compile_args,
        sim_build=sim_build,
        work_dir=sim_build,
        waves=enable_waves,
        plus_args=['--trace'] if enable_waves else [],
        extra_env={**level_env(test_level)},
    )


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

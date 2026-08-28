# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_monbus_arbiter_grant_hold
# Purpose: Regression coverage for the monbus_arbiter grant-hold contract
#          under downstream backpressure (GitHub issue #41, defect 2).
#
# Documentation: docs/markdown/rtl-amba/index.md
# Subsystem: amba (shared)
#
# Author: sean galloway
# Created: 2026-07-20

"""
MonBus Arbiter Grant-Hold Regression

Targets `rtl/amba/monitor/monbus_arbiter.sv`.

WHY THIS TEST EXISTS
--------------------
`monbus_arbiter` runs `arbiter_round_robin` in ACK mode (WAIT_GNT_ACK=1),
whose contract is: the grant is HELD until the granted client acknowledges,
and the ack means "the granted beat was consumed". The arbiter originally
drove::

    grant_ack[i] = grant[i] && int_monbus_valid_in[i];      // no ready term

while an actual transfer additionally requires `int_monbus_ready`. With the
sink holding `monbus_ready` low, `grant_ack` was therefore asserted every
cycle with ZERO transfers occurring, so `arbiter_round_robin` retired and
rotated the grant every single cycle.

Consequences:
  * the documented grant-hold contract is broken;
  * with OUTPUT_SKID_ENABLE=0 the arbiter's mux output IS the module port, so
    `monbus_packet` changes underneath a high `monbus_valid` while
    `monbus_ready` is low -- a valid/payload stability violation;
  * fairness under backpressure becomes a function of the phase of `ready`.

No packet is lost (each client's data sits in its own skid), which is exactly
why the pre-existing suite stayed green. This test asserts the *contract*
rather than the observed behaviour.

Test Types:
- 'grant_hold':   sink held not-ready -> grant must not rotate, and
                  valid/payload must remain stable.
- 'drain_fair':   grant_hold phase followed by releasing the sink; every
                  requesting client must be served, fairly.

STRUCTURE FOLLOWS REPOSITORY STANDARD:
  - Single CocoTB test function (dispatches based on TEST_TYPE)
  - Single parameter generator (includes test_type as first parameter)
  - Single pytest wrapper (fully parametrized)
"""

import os
import sys

import pytest
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge
from cocotb.clock import Clock
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.monbus_arbiter_grant_hold_tb import MonbusArbiterGrantHoldTB
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)


# ===========================================================================
# TESTBENCH CLASS
# ===========================================================================



# ===========================================================================
# COCOTB TEST FUNCTION - Single test that handles all variants
# ===========================================================================

@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_monbus_arbiter_grant_hold(dut):
    """Unified monbus_arbiter grant-hold test -- dispatches via TEST_TYPE."""
    test_type = os.environ.get('TEST_TYPE', 'grant_hold')

    tb = MonbusArbiterGrantHoldTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize()

    cocotb.start_soon(tb.run_transfer_counter())
    cocotb.start_soon(tb.run_stability_monitor())

    # Two clients contend; the sink is held off.
    contenders = [0, 1]

    rotations, moved = await tb.phase_backpressured_hold(contenders, cycles=16)

    tb.log.info(f"backpressured phase: rotations={rotations} transfers={moved}")

    assert sum(moved) == 0, (
        f"transfers occurred while monbus_ready was low: {moved}")

    assert rotations == 0, (
        f"GRANT-HOLD VIOLATION: grant rotated {rotations} times across 16 "
        f"backpressured cycles with ZERO transfers. arbiter_round_robin is in "
        f"ACK mode; grant_ack must mean 'beat consumed' (grant && valid && "
        f"ready), not merely 'grant && valid'.")

    assert tb.stability_violations == 0, (
        f"VALID/PAYLOAD STABILITY VIOLATION: monbus_packet changed "
        f"{tb.stability_violations} times while monbus_valid was asserted and "
        f"monbus_ready was low (OUTPUT_SKID_ENABLE=0 exposes the mux directly "
        f"at the port).")

    if test_type == 'drain_fair':
        before = list(tb.xfers)
        await tb.phase_drain(cycles=24)
        served = [tb.xfers[i] - before[i] for i in range(tb.CLIENTS)]
        tb.log.info(f"drain phase: served={served}")
        for i in contenders:
            assert served[i] > 0, \
                f"client {i} was starved after the sink went ready: {served}"
        spread = max(served[i] for i in contenders) - min(served[i] for i in contenders)
        assert spread <= 2, \
            f"round-robin unfair across contenders: {served}"

    tb.log.info(f"PASS: grant-hold contract upheld ({test_type})")


# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_monbus_arbiter_grant_hold_params():
    """Generate parameters for the monbus_arbiter grant-hold regression.

    Parameters:
        (test_type, clients, input_skid_enable, output_skid_enable)

    OUTPUT_SKID_ENABLE=0 is the configuration that exposes the arbiter's
    combinational mux straight at the module port, so the valid/payload
    stability violation is directly observable there. INPUT_SKID_ENABLE=0
    keeps each client's payload driven by the TB rather than a skid, which
    makes the rotation visible in `monbus_packet`.
    """
    params = []
    for test_type in ('grant_hold', 'drain_fair'):
        params.append((test_type, 4, 0, 0))
    # Also prove the contract holds with the input skids in the path.
    params.append(('grant_hold', 4, 1, 0))
    return params


monbus_arbiter_grant_hold_params = generate_monbus_arbiter_grant_hold_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTION - Single wrapper for all test types
# ===========================================================================

@pytest.mark.parametrize(
    "test_type, clients, input_skid_enable, output_skid_enable",
    monbus_arbiter_grant_hold_params)
def test_monbus_arbiter_grant_hold(request, test_type, clients,
                                   input_skid_enable, output_skid_enable):
    """Pytest wrapper for the monbus_arbiter grant-hold regression."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_includes': 'rtl/amba/includes',
        'rtl_monitor':  'rtl/amba/monitor',
        'rtl_gaxi':     'rtl/amba/gaxi',
        'rtl_common':   'rtl/common',
    })

    dut_name = "monbus_arbiter_grant_hold_dut"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="val/amba/filelists/monbus_arbiter_grant_hold_dut.f")
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    cl_str = TBBase.format_dec(clients, 2)
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name_plus_params = (
        f"test_{worker_id}_{dut_name}_grant_hold_{test_type}_"
        f"cl{cl_str}_is{input_skid_enable}_os{output_skid_enable}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    includes = includes + [rtl_dict['rtl_common'], sim_build]

    rtl_parameters = {
        'CLIENTS':            clients,
        'INPUT_SKID_ENABLE':  input_skid_enable,
        'OUTPUT_SKID_ENABLE': output_skid_enable,
    }

    extra_env = {
        'LOG_PATH':     log_path,
        'TEST_TYPE':    test_type,
        'TEST_CLIENTS': str(clients),
    }

    create_view_cmd(log_dir, log_path, sim_build,
                    'test_monbus_arbiter_grant_hold', test_name_plus_params)

    compile_args = ["-Wno-TIMESCALEMOD", "-Wno-SELRANGE",
                    "-Wno-WIDTHEXPAND", "-Wno-WIDTH"]
    sim_args = []

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module='test_monbus_arbiter_grant_hold',
        testcase="cocotb_test_monbus_arbiter_grant_hold",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        simulator="verilator",
        waves=enable_waves,
        keep_files=True,
        compile_args=compile_args,
        sim_args=sim_args,
        plus_args=['--trace'] if enable_waves else [],
    )

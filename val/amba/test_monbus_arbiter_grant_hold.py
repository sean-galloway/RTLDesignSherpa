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
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)


# ===========================================================================
# TESTBENCH CLASS
# ===========================================================================

class MonbusArbiterGrantHoldTB(TBBase):
    """Minimal driver/checker for the monbus_arbiter grant-hold contract.

    The arbiter's client-side ports are SystemVerilog unpacked arrays
    (`monbus_valid_in [CLIENTS]`), so they are driven by index rather than
    through a packed-bus BFM.
    """

    def __init__(self, dut):
        super().__init__(dut)
        self.CLIENTS = int(os.environ.get('TEST_CLIENTS', '4'))
        self.PKT_W = 128   # MONBUS_PKT_WIDTH
        self.TS_W = 64     # MONBUS_TS_WIDTH
        self.clk_name = 'axi_aclk'
        self.axi_aclk = dut.axi_aclk
        self.rst_n = dut.axi_aresetn
        # per-client transfer counters
        self.xfers = [0] * self.CLIENTS
        # contract violation counters
        self.grant_rotations_without_xfer = 0
        self.stability_violations = 0

    # ---- MANDATORY three methods -----------------------------------------

    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    # ---- stimulus ---------------------------------------------------------

    async def initialize(self):
        """Idle all client inputs and give each client a unique payload."""
        self.dut.block_arb.value = 0
        self.dut.monbus_ready.value = 0
        self.dut.monbus_valid_in.value = 0
        # unique, easily-identified payload per client, packed side by side
        pkt = 0
        ts = 0
        for i in range(self.CLIENTS):
            pkt |= (i + 1) << (i * self.PKT_W)
            ts |= (i + 1) << (i * self.TS_W)
        self.dut.monbus_packet_in.value = pkt
        self.dut.monbus_timestamp_in.value = ts
        await self.wait_clocks(self.clk_name, 1)

    def request(self, clients):
        """Assert monbus_valid_in for the given client indices, clear others."""
        vec = 0
        for i in clients:
            vec |= (1 << i)
        self.dut.monbus_valid_in.value = vec

    def _grant_vector(self):
        return int(self.dut.grant.value)

    # ---- monitors ---------------------------------------------------------

    async def run_transfer_counter(self):
        """Count real client-side transfers (valid && ready) forever."""
        while True:
            await RisingEdge(self.axi_aclk)
            if self.rst_n.value != 1:
                continue
            try:
                vvec = int(self.dut.monbus_valid_in.value)
                rvec = int(self.dut.monbus_ready_in.value)
            except ValueError:
                continue
            for i in range(self.CLIENTS):
                if (vvec >> i) & 1 and (rvec >> i) & 1:
                    self.xfers[i] += 1

    async def run_stability_monitor(self):
        """AXI-style payload stability check on the arbitrated output port.

        While `monbus_valid` is asserted and `monbus_ready` is low, the
        payload presented at `monbus_packet` must not change.
        """
        prev_valid = 0
        prev_ready = 0
        prev_pkt = None
        while True:
            await RisingEdge(self.axi_aclk)
            if self.rst_n.value != 1:
                continue
            try:
                valid = int(self.dut.monbus_valid.value)
                ready = int(self.dut.monbus_ready.value)
                pkt = int(self.dut.monbus_packet.value)
            except ValueError:
                prev_valid, prev_ready, prev_pkt = 0, 0, None
                continue

            if (prev_valid == 1 and prev_ready == 0 and valid == 1
                    and prev_pkt is not None and pkt != prev_pkt):
                self.stability_violations += 1
                self.log.error(
                    f"payload changed while valid && !ready: "
                    f"0x{prev_pkt:x} -> 0x{pkt:x}")

            prev_valid, prev_ready, prev_pkt = valid, ready, pkt

    # ---- test phases ------------------------------------------------------

    async def phase_backpressured_hold(self, clients, cycles=16):
        """Sink held not-ready. The grant must not move and no transfer may
        occur. Returns (rotations, transfers_seen)."""
        self.dut.monbus_ready.value = 0
        self.request(clients)

        # let the arbiter settle on a grant
        await self.wait_clocks(self.clk_name, 4)
        base_xfers = list(self.xfers)
        ref_grant = self._grant_vector()
        grant_valid = int(self.dut.grant_valid.value)
        self.log.info(f"settled grant=0b{ref_grant:0{self.CLIENTS}b} "
                      f"grant_valid={grant_valid}")
        assert grant_valid == 1, \
            "arbiter never issued a grant with live requests"

        rotations = 0
        for cyc in range(cycles):
            await RisingEdge(self.axi_aclk)
            await FallingEdge(self.axi_aclk)   # sample settled mid-cycle
            g = self._grant_vector()
            if g != ref_grant:
                rotations += 1
                self.log.error(
                    f"cyc{cyc}: grant rotated 0b{ref_grant:0{self.CLIENTS}b} "
                    f"-> 0b{g:0{self.CLIENTS}b} with ready low")
                ref_grant = g

        moved = [self.xfers[i] - base_xfers[i] for i in range(self.CLIENTS)]
        self.grant_rotations_without_xfer = rotations
        return rotations, moved

    async def phase_drain(self, cycles=24):
        """Release the sink and let the requesting clients drain."""
        self.dut.monbus_ready.value = 1
        await self.wait_clocks(self.clk_name, cycles)
        self.request([])
        self.dut.monbus_ready.value = 0
        await self.wait_clocks(self.clk_name, 4)


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
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
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

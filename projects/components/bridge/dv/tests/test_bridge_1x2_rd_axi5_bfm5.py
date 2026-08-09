#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-002 A5-1 sign-off test.
#
# The generated test drives the AXI5 master port with the AXI4 BFM
# (base-subset interop). This test closes the sign-off gap: the port
# is driven by the real AXI5MasterRead BFM with the
# AXI5ComplianceChecker attached to the same prefix, proving the
# generated AXI5 boundary speaks AXI5 to an AXI5 agent while the
# fabric behind stays AXI4.

import os
import sys
import logging

from TBClasses.shared.utilities import get_repo_root

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist

from CocoTBFramework.components.axi5.axi5_interfaces import AXI5MasterRead
from CocoTBFramework.components.axi5.axi5_compliance_checker import (
    AXI5ComplianceChecker,
)

from projects.components.bridge.dv.tbclasses.bridge1x2_rd_axi5_tb import (
    Bridge1x2RdAxi5TB,
)


class Bridge1x2RdAxi5Bfm5TB(Bridge1x2RdAxi5TB):
    """Generated TB with the AXI5 master port driven by the AXI5 BFM.

    Only the master-side setup changes; slave BFMs, memory seeding,
    clocking, and the read helpers are inherited unchanged.
    """

    def _setup_master_0_cpu_rd(self):
        self.master_rd[0] = AXI5MasterRead(
            self.dut, self.clock,
            prefix="cpu_rd_axi_",
            log=self.log,
            data_width=32,
            addr_width=32,
            id_width=4,
            user_width=1,
            multi_sig=True,
        )


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_1x2_rd_axi5_bfm5(dut):
    """AXI5 BFM reads through the AXI5 boundary into both AXI4 slaves,
    with the AXI5 compliance checker watching the port."""
    tb = Bridge1x2RdAxi5Bfm5TB(dut)
    await tb.setup_clocks_and_reset()

    # Attach the compliance checker to the AXI5 port.
    checker = AXI5ComplianceChecker(
        dut, tb.clock,
        prefix="cpu_rd_axi_",
        log=tb.log,
        data_width=32,
        addr_width=32,
        id_width=4,
        user_width=1,
    )
    checker.setup_monitors()
    cocotb.start_soon(checker.monitor_transactions())
    cocotb.start_soon(checker.monitor_handshakes())

    tb.log.info("=" * 80)
    tb.log.info("A5-1 sign-off: AXI5 BFM + compliance checker on the AXI5 port")
    tb.log.info("=" * 80)

    # Reads against both slaves' seeded patterns, several offsets each,
    # so AR/R see back-to-back traffic (not just one transaction).
    for slave_idx, base in ((0, 0x0000_0000), (1, 0x8000_0000)):
        for off in (0x100, 0x1F4, 0x0FC):
            addr = base + off
            expected = tb.slave_mem_read(slave_idx, addr, master_idx=0)
            actual = await tb.master_read(0, addr)
            assert actual == expected, (
                f"AXI5-BFM read mismatch slave {slave_idx} @ 0x{addr:08x}: "
                f"got 0x{actual:08x}, expected 0x{expected:08x}"
            )
            tb.log.info(f"  R slave={slave_idx} addr=0x{addr:08x} "
                        f"data=0x{actual:08x} OK")

    await ClockCycles(tb.clock, 50)

    # Compliance verdict — zero violations.
    report = checker.get_compliance_report()
    tb.log.info(f"AXI5 compliance report: {report}")
    violations = report.get("total_violations",
                            report.get("violations", 0))
    if isinstance(violations, (list, tuple)):
        violations = len(violations)
    assert not violations, f"AXI5 compliance violations: {report}"

    tb.log.info("=" * 80)
    tb.log.info("A5-1 sign-off test PASSED")
    tb.log.info("=" * 80)


# ============================================================================
# Pytest runner (mirrors the generated harness)
# ============================================================================


def test_bridge_1x2_rd_axi5_bfm5(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })

    dut_name = "bridge_1x2_rd_axi5"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/bridge/rtl/filelists/bridge_1x2_rd_axi5.f'
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    test_name_plus_params = f"test_{dut_name}_bfm5"
    sim_build_name = f"{test_name_plus_params}{worker_suffix}"

    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    waves = get_wave_config(sim_build)

    extra_args = ['--assert', '--coverage'] + waves['extra_args']
    extra_env = {
        'COCOTB_LOG_LEVEL': 'INFO',
        'LOG_PATH': log_path,
        'COCOTB_RESULTS_FILE': results_path,
        **waves['extra_env'],
    }

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_bridge_1x2_rd_axi5_bfm5",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env
    )

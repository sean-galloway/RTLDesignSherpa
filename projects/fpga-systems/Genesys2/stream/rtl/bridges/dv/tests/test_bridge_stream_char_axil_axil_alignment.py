#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Standalone test for AXIL-master → wider-slave byte-lane alignment.
#
# This file lives outside the bridge-generator-regenerated test runner
# (test_bridge_stream_char_axil.py) so it survives `make tests` cycles.
# It reuses the same generated TB class and the same compiled DUT.
#
# What it verifies:
#   When a 32-bit AXIL master (host) writes a single beat at a byte
#   offset N within a 32-byte row of a 256-bit AXIL slave (desc_ram),
#   AXI4 requires the four strobed bytes to sit at byte lanes
#   [N..N+3] of the wide bus — i.e. wstrb bits [N+3:N] are 1 and
#   wdata bits [(N+3)*8+7 : N*8] carry the data.
#
#   Pre-fix: the bridge wired `axi_data_upsize` for narrow→wide and
#   always emitted wstrb=0x0000000F + wdata at bits[31:0] regardless
#   of awaddr. Real AXI4-strict slaves (e.g. byte-strobed BRAMs)
#   misplaced every host descriptor byte.
#
#   Post-fix: when master.protocol=='axil' and upsize is needed, the
#   bridge generator emits `axil_to_axi4_wide_align_wr` instead.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist

from projects.NexysA7.stream_characterization.stream_char_framework.rtl.bridges.dv.tbclasses.bridge_stream_char_axil_tb import BridgeStreamCharAxilTB


# ============================================================================
# CocoTB test function
# ============================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_stream_char_axil_axil_narrow_to_wide_alignment(dut):
    """
    Spy on the desc_ram slave-side AW/W signals while the host writes
    four 32-bit values at distinct byte offsets within a single 32-byte
    row. Assert wstrb is positioned at byte_offset+:4 and wdata's
    masked slot carries the value written.
    """
    tb = BridgeStreamCharAxilTB(dut)
    await tb.setup_clocks_and_reset()

    tb.log.info("=" * 80)
    tb.log.info("Starting AXIL narrow→wide alignment test")
    tb.log.info("=" * 80)

    captured_aw = []
    captured_w  = []

    async def mon_aw():
        while True:
            await RisingEdge(tb.clock)
            if (int(dut.desc_ram_axi_awvalid.value) == 1 and
                int(dut.desc_ram_axi_awready.value) == 1):
                captured_aw.append(int(dut.desc_ram_axi_awaddr.value))

    async def mon_w():
        while True:
            await RisingEdge(tb.clock)
            if (int(dut.desc_ram_axi_wvalid.value) == 1 and
                int(dut.desc_ram_axi_wready.value) == 1):
                captured_w.append({
                    'wdata': int(dut.desc_ram_axi_wdata.value),
                    'wstrb': int(dut.desc_ram_axi_wstrb.value),
                })

    cocotb.start_soon(mon_aw())
    cocotb.start_soon(mon_w())

    row_base = 0x00020100
    write_plan = [
        (row_base + 0x00, 0xAAAA_0001),  # slot 0
        (row_base + 0x04, 0xBBBB_0002),  # slot 1
        (row_base + 0x08, 0xCCCC_0003),  # slot 2
        (row_base + 0x1C, 0xDDDD_0008),  # slot 7
    ]

    for addr, data in write_plan:
        tb.log.info(f"  master_write: addr=0x{addr:08X} data=0x{data:08X}")
        await tb.master_write(0, addr, data)

    await ClockCycles(tb.clock, 50)

    assert len(captured_aw) >= len(write_plan), (
        f"Expected at least {len(write_plan)} AW handshakes on desc_ram, "
        f"got {len(captured_aw)}")
    assert len(captured_w) >= len(write_plan), (
        f"Expected at least {len(write_plan)} W handshakes on desc_ram, "
        f"got {len(captured_w)}")

    errors = []
    for i, ((addr, data), aw_addr, w) in enumerate(
            zip(write_plan, captured_aw, captured_w)):
        byte_off = addr & 0x1F
        expected_wstrb = 0xF << byte_off
        expected_wdata_slice = (data & 0xFFFFFFFF) << (byte_off * 8)
        expected_wdata_mask  = 0xFFFFFFFF << (byte_off * 8)

        got_wstrb = w['wstrb']
        got_wdata = w['wdata']
        got_wdata_slice = got_wdata & expected_wdata_mask

        if got_wstrb != expected_wstrb:
            errors.append(
                f"  [#{i}] addr=0x{addr:08X} (byte_off={byte_off}): "
                f"wstrb expected 0x{expected_wstrb:08X}, "
                f"got 0x{got_wstrb:08X}")
        if got_wdata_slice != expected_wdata_slice:
            errors.append(
                f"  [#{i}] addr=0x{addr:08X} (byte_off={byte_off}): "
                f"wdata@slot expected 0x{expected_wdata_slice:064X}, "
                f"got 0x{got_wdata_slice:064X}")

    if errors:
        tb.log.error("AXIL narrow→wide alignment FAILED:")
        for e in errors:
            tb.log.error(e)
        assert False, (
            "Bridge generator does not emit master-side alignment for "
            "AXIL master → wider slave. Expected wstrb/wdata positioned "
            "by awaddr's low bits; got everything at lane 0.")

    tb.log.info("AXIL narrow→wide alignment test PASSED")


# ============================================================================
# Pytest wrapper
# ============================================================================

def test_bridge_stream_char_axil_axil_narrow_to_wide_alignment(request):
    """Pytest wrapper. Same compile knobs as the basic_connectivity test."""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })

    dut_name = "bridge_stream_char_axil"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/filelists/bridge_stream_char_axil.f'
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    test_name_plus_params = f"test_{dut_name}_axil_narrow_to_wide_alignment"
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
        testcase="cocotb_test_bridge_stream_char_axil_axil_narrow_to_wide_alignment",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env
    )

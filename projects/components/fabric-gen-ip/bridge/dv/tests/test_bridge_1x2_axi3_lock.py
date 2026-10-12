#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): AXI3 Review Focus 5 lock pass-through.
#
# bridge_1x2_axi3 has a 2-bit AxLOCK AXI3 master port. Since bridge GitHub
# #99 the generated TB instantiates AXI3MasterRead/Write itself (they drive
# the 2-bit lock field and WID), so this test drives the TB's own BFMs and
# adds the one thing the generated suite does not: directed AxLOCK traffic.
# It drives AxLOCK=2'b10 (locked per the ARM AXI3 encoding, IHI 0022) and
# AxLOCK=2'b01 (exclusive) and asserts every response is OKAY with no
# fabricated lock semantics — the converters demote AXI3 locked to normal
# (AXI4 dropped locked accesses) and the bridge fabric carries exclusive as
# a qualifier it never answers with EXOKAY (no exclusive monitor).
# Depth (TEST_LEVEL): fixed single address, so level only affects repeats.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from bridge1x2_axi3_tb import Bridge1x2Axi3TB

S0_BASE = 0x0000_0000
AXI3_LOCKED = 2    # 2'b10 on the AXI3 2-bit AxLOCK field: locked access
AXI3_EXCLUSIVE = 1 # 2'b01 on the AXI3 2-bit AxLOCK field: exclusive access


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bridge_1x2_axi3_lock(dut):
    tb = Bridge1x2Axi3TB(dut)
    await tb.setup_clocks_and_reset()

    repeats = tb.level_cfg.get('lock_repeats', 1)
    tb.log.info("=" * 80)
    tb.log.info(f"AXI3 AxLOCK pass-through: {repeats} locked read+write pair(s) "
                f"(level={tb.level})")
    tb.log.info("=" * 80)

    # Directed AxLOCK traffic over the generated TB's own AXI3 BFMs (bridge
    # GitHub #99): they drive the 2-bit lock field, so no parallel BFM set
    # is needed — a second set bound to cpu_axi_ would race this one.
    axi3_rd = tb.master_rd[0]
    axi3_wr = tb.master_wr[0]

    # Even repeats drive locked (2'b10, demoted to normal by the converters
    # since AXI4 dropped locked accesses); odd repeats drive exclusive
    # (2'b01, carried as a qualifier the no-monitor fabric answers OKAY).
    for i in range(repeats):
        addr = S0_BASE + 0x1000 + i * 0x100
        write_data = 0xA5A5_B5B5_C5C5_D5D5 + i
        lock = AXI3_LOCKED if (i % 2 == 0) else AXI3_EXCLUSIVE

        # Locked/exclusive read first.
        rd = await axi3_rd.read_transaction(
            addr, burst_len=1, size=3, id=0, lock=lock)
        assert len(rd) == 1, f"locked read {i} returned {len(rd)} beats"
        tb.log.info(f"  lock=2'b{lock:02d} read {i} @0x{addr:08x} "
                    f"returned 0x{rd[0]:016x} OKAY")

        # Locked/exclusive write to the same address.
        wr = await axi3_wr.write_transaction(
            addr, write_data, burst_len=1, size=3, id=0, lock=lock)
        assert wr.get('success'), f"locked write {i} failed: {wr}"
        assert wr.get('response') == 0, (
            f"locked write {i}: expected OKAY, got {wr.get('response')}")
        tb.log.info(f"  lock=2'b{lock:02d} write {i} @0x{addr:08x} returned OKAY")

    await ClockCycles(tb.clock, 20)
    tb.assert_compliance()
    tb.log.info("=" * 80)
    tb.log.info("AXI3 AxLOCK pass-through test PASSED")
    tb.log.info("=" * 80)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_1x2_axi3_lock(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_1x2_axi3"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/fabric-gen-ip/bridge/rtl/filelists/{dut_name}.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_lock_{test_level}_{reg_level}"
    sim_build_name = f"{test_name_plus_params}{worker_suffix}"
    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = sim_build_path(tests_dir, sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    waves = get_wave_config(sim_build)
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_bridge_1x2_axi3_lock",
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert', '--coverage'] + waves['extra_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            **level_env(test_level),
            **waves['extra_env'],
        },
        plus_args=waves['sim_args'],
        keep_files=True,
    )

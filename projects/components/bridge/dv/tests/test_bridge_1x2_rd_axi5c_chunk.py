#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): chunking is DROPPABLE sideband (BRIDGE-018).
#
# bridge_1x2_rd_axi5c: a 128-bit AXI5 master with read-data chunking, an
# AXI5 slave that chunks (sram_rd, native path) and an AXI4 slave that
# cannot (ddr_rd, drop path). ARCHUNKEN is permission, not demand:
#   - to sram_rd the enable arrives at the port (sampled at every AR
#     handshake) and every R beat comes back with RCHUNKV set and RCHUNKNUM
#     counting the beat;
#   - to ddr_rd the enable terminates in the fabric (the AXI4 port has no
#     such pin) and the same read returns ordered data with RCHUNKV low --
#     the requester must accept that, and the data is right either way;
#   - the AXI5 compliance checker on the master port: zero violations.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from projects.components.bridge.dv.tbclasses.bridge1x2_rd_axi5c_tb import Bridge1x2RdAxi5cTB

DDR, SRAM = 0, 1
DDR_BASE, SRAM_BASE = 0x0000_0000, 0x8000_0000
BEATS, SIZE = 4, 4


class SramArSampler:
    def __init__(self, dut, clock):
        self.dut, self.clock, self.ar, self.r = dut, clock, [], []

    async def run(self):
        d = self.dut
        while True:
            await RisingEdge(self.clock)
            if int(d.sram_rd_axi_arvalid.value) and int(d.sram_rd_axi_arready.value):
                self.ar.append(int(d.sram_rd_axi_archunken.value))
            if int(d.sram_rd_axi_rvalid.value) and int(d.sram_rd_axi_rready.value):
                self.r.append((int(d.sram_rd_axi_rchunkv.value), int(d.sram_rd_axi_rchunknum.value)))


@cocotb.test(timeout_time=8000, timeout_unit="ms")
async def cocotb_test_bridge_1x2_rd_axi5c_chunk(dut):
    tb = Bridge1x2RdAxi5cTB(dut)
    await tb.setup_clocks_and_reset()
    sampler = SramArSampler(dut, tb.clock)
    cocotb.start_soon(sampler.run())
    n = tb.level_cfg['arb_per_master']
    tb.log.info(f"BRIDGE-018 chunking drop path: {n} reads per slave (level={tb.level})")

    for i in range(n):
        for slave, base in ((SRAM, SRAM_BASE), (DDR, DDR_BASE)):
            addr = base + i * BEATS * 16
            beats = await tb.master_rd[0].read_transaction(addr, burst_len=BEATS, size=SIZE, id=i % 16, chunken=1)
            want = [tb.slave_mem_read(slave, addr + k * 16, byte_count=16) for k in range(BEATS)]
            assert [b['data'] for b in beats] == want, f"slave {slave} read @0x{addr:08X}: data mismatch"
            got_v = [b['chunkv'] for b in beats]
            if slave == SRAM:
                assert got_v == [1] * BEATS, f"sram (chunking slave): RCHUNKV {got_v}, expected all set"
                assert [b['chunknum'] for b in beats] == list(range(BEATS)), (
                    f"sram: RCHUNKNUM {[b['chunknum'] for b in beats]}")
            else:
                assert got_v == [0] * BEATS, f"ddr (AXI4 slave): RCHUNKV {got_v}, expected none -- the enable must terminate"
    assert sampler.ar == [1] * n, f"sram port saw ARCHUNKEN {sampler.ar}, expected {n} enabled ARs"
    assert sum(1 for v, _ in sampler.r if v) == n * BEATS, "sram port: chunk-valid beats != beats read"
    tb.assert_compliance()
    tb.log.info("BRIDGE-018 chunking native-and-dropped PASSED")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_1x2_rd_axi5c_chunk(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_1x2_rd_axi5c"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/bridge/rtl/filelists/{dut_name}.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_chunk_{test_level}_{reg_level}"
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
        testcase="cocotb_test_bridge_1x2_rd_axi5c_chunk",
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

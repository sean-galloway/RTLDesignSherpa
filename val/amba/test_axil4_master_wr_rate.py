# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_axil4_master_wr_rate
# Purpose: sustained-throughput pin for rtl/amba/axil4/axil4_master_wr.sv
#
# Documentation: rtl/amba/axil4/axil4_master_wr.sv (header)
# Subsystem: tests
#
# Author: sean galloway

"""Sustained-write-rate pin for the AXIL4 write master leaf (amba BUG-039).

BUG-039's record chain (monitor queues -> arbiter -> group raw expander ->
write FIFO -> THIS leaf -> tally ingest) sustains only ~0.08 records/cycle
on the board.  The leaf itself is three INDEPENDENT skid buffers (AW, W, B),
so with any elastic downstream it should accept one (AW, W) pair per cycle
for as long as the B skid (depth 2) drains -- i.e. ~1 write/cycle against a
sink that completes one write per cycle.

This test drives the FUB input flat out against a programmable-latency
AXIL sink and requires the sustained rate to clear RATE_FLOOR.  It exists so
the leaf can be formally exonerated (or named) before the group write FSM
(the actual serializer) is touched: a leaf that passes here cannot be the
reason the chain delivers 1 record per ~12 cycles.
"""

import os
import random

import pytest
import cocotb
from cocotb.triggers import RisingEdge, ReadOnly

from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist


class RateTB(TBBase):
    """Flat-out FUB producer + programmable-latency AXIL sink."""

    def __init__(self, dut):
        super().__init__(dut)
        self.dut = dut
        self.AW = int(os.environ['PARAM_ADDR_WIDTH'])
        self.DW = int(os.environ['PARAM_DATA_WIDTH'])

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def setup(self):
        await self.start_clock('aclk', 10, 'ns')
        for sig, val in (
            ('fub_awaddr', 0), ('fub_awprot', 0), ('fub_awvalid', 0),
            ('fub_wdata', 0), ('fub_wstrb', 0), ('fub_wvalid', 0),
            ('fub_bready', 1),
            ('m_axil_awready', 0), ('m_axil_wready', 0),
            ('m_axil_bvalid', 0), ('m_axil_bresp', 0),
        ):
            getattr(self.dut, sig).value = val
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)

    async def sink(self, b_latency: int):
        """AXIL slave: AW/W always ready; each AW's B returns exactly
        b_latency cycles after its handshake, in order, back-to-back once
        the pipe fills (a pipelined register-file slave).  One B in flight
        at a time is enough: the leaf's B skid absorbs the return burst.
        """
        dut = self.dut
        dues = []         # ordered cycle indices at which each pending B may assert
        cyc = 0
        while True:
            await ReadOnly()
            aw_h = int(dut.m_axil_awvalid.value) and int(dut.m_axil_awready.value)
            b_h = int(dut.m_axil_bvalid.value) and int(dut.m_axil_bready.value)
            await RisingEdge(dut.aclk)
            cyc += 1
            dut.m_axil_awready.value = 1
            dut.m_axil_wready.value = 1
            if b_h:
                dues.pop(0)
            if dues and cyc >= dues[0]:
                dut.m_axil_bvalid.value = 1
                dut.m_axil_bresp.value = 0
            else:
                dut.m_axil_bvalid.value = 0
            if aw_h:
                dues.append(cyc + b_latency)


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def axil4_master_wr_rate_test(dut):
    tb = RateTB(dut)
    await tb.setup()

    n = int(os.environ.get('RATE_N', '500'))
    b_latency = int(os.environ.get('B_LATENCY', '2'))
    floor = float(os.environ.get('RATE_FLOOR', '0.8'))

    cocotb.start_soon(tb.sink(b_latency))

    dut = tb.dut
    aw_issued = 0
    w_issued = 0
    b_seen = 0
    cycles = 0

    # Flat-out producer: present a fresh AW / W every cycle the leaf accepts
    # one.  Stop issuing at n; keep counting until the n-th B returns so the
    # measured window covers the full drain of the last skid contents.
    while b_seen < n:
        await ReadOnly()
        aw_ready = int(dut.fub_awready.value)
        w_ready = int(dut.fub_wready.value)
        b_done = int(dut.fub_bvalid.value) and int(dut.fub_bready.value)
        await RisingEdge(dut.aclk)
        cycles += 1
        if b_done:
            b_seen += 1
        if aw_issued < n:
            dut.fub_awaddr.value = 0x1000 + aw_issued * 8
            dut.fub_awvalid.value = 1
            if aw_ready:
                aw_issued += 1
        else:
            dut.fub_awvalid.value = 0
        if w_issued < n:
            dut.fub_wdata.value = 0xA5A50000_00000000 + w_issued
            dut.fub_wstrb.value = (1 << (tb.DW // 8)) - 1
            dut.fub_wvalid.value = 1
            if w_ready:
                w_issued += 1
        else:
            dut.fub_wvalid.value = 0

    rate = n / cycles
    tb.log.info(
        f"[axil4_master_wr rate] n={n} b_latency={b_latency} "
        f"cycles={cycles} rate={rate:.3f} writes/cycle "
        f"(1 per {cycles / n:.2f})")
    assert rate >= floor, (
        f"AXIL4 write master sustained {rate:.3f} writes/cycle (< {floor}) "
        f"against a one-per-cycle sink with B latency {b_latency} -- the leaf "
        f"IS a BUG-039 serializer; skid depths "
        f"AW={os.environ['PARAM_SKID_AW']} W={os.environ['PARAM_SKID_W']} "
        f"B={os.environ['PARAM_SKID_B']} do not cover the B return latency")


# ----------------------------------------------------------------------------
# Pytest wrapper
# ----------------------------------------------------------------------------
def get_params():
    # (addr_width, data_width, skid_aw, skid_w, skid_b)
    # Board/group config first (monbus_axil4_axil4_group drives 32/64 2/2/2),
    # then a deeper-skid point for coverage.
    return [
        (32, 64, 2, 2, 2),
        (32, 64, 4, 4, 4),
    ]


@pytest.mark.parametrize(
    "addr_width, data_width, skid_aw, skid_w, skid_b", get_params())
def test_axil4_master_wr_rate(request, addr_width, data_width,
                              skid_aw, skid_w, skid_b):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axil4':    'rtl/amba/axil4/',
        'rtl_gaxi':     'rtl/amba/gaxi',
        'rtl_includes': 'rtl/amba/includes',
    })

    dut_name = 'axil4_master_wr'
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name = (f"test_{worker_id}_{dut_name}_rate"
                 f"_a{addr_width}_d{data_width}"
                 f"_s{skid_aw}{skid_w}{skid_b}_{reg_level}")
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        module=dut_name)
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    rtl_parameters = {
        'AXIL_ADDR_WIDTH': str(addr_width),
        'AXIL_DATA_WIDTH': str(data_width),
        'SKID_DEPTH_AW':   str(skid_aw),
        'SKID_DEPTH_W':    str(skid_w),
        'SKID_DEPTH_B':    str(skid_b),
    }

    extra_env = {
        'DUT':                 dut_name,
        'LOG_PATH':            log_path,
        'COCOTB_LOG_LEVEL':    'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED':                os.environ.get('SEED', str(random.randint(0, 100000))),
        'PARAM_ADDR_WIDTH':    str(addr_width),
        'PARAM_DATA_WIDTH':    str(data_width),
        'PARAM_SKID_AW':       str(skid_aw),
        'PARAM_SKID_W':        str(skid_w),
        'PARAM_SKID_B':        str(skid_b),
    }

    compile_args = [
        '--trace-fst', '--trace-structs',
        '-Wno-DECLFILENAME', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC',
        '-Wno-UNUSEDPARAM', '-Wno-TIMESCALEMOD', '-Wno-UNUSEDSIGNAL',
    ]

    create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=enable_waves,
        keep_files=True,
        compile_args=compile_args,
    )

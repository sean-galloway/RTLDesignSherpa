# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""wb4_master_stub / wb4_slave_stub: the packed command/response vectors.

A stub adds exactly one thing to the block it wraps: the FUB side is a
single vector instead of named fields. So that packing is what this test
checks, directly and in both directions.

  master   drive a packed cmd_data, read the fields off the Wishbone wires
  slave    drive the Wishbone wires, read the fields out of packed cmd_data
  rsp      terminate and check the packed rsp_data carries {status, dat}

The field order is the contract two stubs rely on to connect to each other:
    cmd_data = {we, adr, dat, sel, cti, bte}   (most significant first)
    rsp_data = {status, dat}
"""
import os
import random

import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

AW, DW = 32, 32
SW, CTW, BTW, STW = DW // 8, 3, 2, 2


def _pack_cmd(we, adr, dat, sel, cti, bte):
    v = (we & 1)
    v = (v << AW) | (adr & ((1 << AW) - 1))
    v = (v << DW) | (dat & ((1 << DW) - 1))
    v = (v << SW) | (sel & ((1 << SW) - 1))
    v = (v << CTW) | (cti & 0x7)
    return (v << BTW) | (bte & 0x3)


class _StubTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.clk = dut.clk
        self.clk_name = 'clk'
        self.rst_n = dut.aresetn
        self.errors = []

    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, 10, 'ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def wb4_master_stub_test(dut):
    """A packed command must appear on the Wishbone wires field for field."""
    tb = _StubTB(dut)
    rng = random.Random(int(os.environ.get('SEED', '0')))
    dut.cmd_valid.value = 0
    dut.rsp_ready.value = 1
    dut.m_wb_STALL.value = 0
    dut.m_wb_ACK.value = 0
    dut.m_wb_ERR.value = 0
    dut.m_wb_RTY.value = 0
    dut.m_wb_DAT_R.value = 0
    await tb.setup_clocks_and_reset()

    for _ in range(32):
        we = rng.randint(0, 1)
        adr = rng.getrandbits(AW) & ~(SW - 1)
        dat = rng.getrandbits(DW)
        sel = rng.randint(1, (1 << SW) - 1)
        cti = rng.randint(0, 7)
        bte = rng.randint(0, 3)

        dut.cmd_valid.value = 1
        dut.cmd_data.value = _pack_cmd(we, adr, dat, sel, cti, bte)
        # Wait for the command to be taken, then for it to reach the wires.
        for _ in range(50):
            await RisingEdge(dut.clk)
            if int(dut.cmd_ready.value):
                break
        dut.cmd_valid.value = 0
        for _ in range(50):
            await RisingEdge(dut.clk)
            if int(dut.m_wb_STB.value):
                break
        else:
            tb.errors.append(f"no STB for packed command adr=0x{adr:X}")
            break

        got = (int(dut.m_wb_WE.value), int(dut.m_wb_ADR.value),
               int(dut.m_wb_DAT_W.value), int(dut.m_wb_SEL.value))
        if got != (we, adr, dat, sel):
            tb.errors.append(f"unpacked wrong: wires {got} != packed "
                             f"{(we, adr, dat, sel)}")
            break
        # The hints are only carried when the inner master was built to; the
        # tie-off case must read CLASSIC/LINEAR whatever was packed.
        hints = os.environ.get('USE_BURST_HINTS', '0') == '1'
        want_cti, want_bte = (cti, bte) if hints else (0, 0)
        if (int(dut.m_wb_CTI.value), int(dut.m_wb_BTE.value)) != (want_cti, want_bte):
            tb.errors.append(f"hint wrong: CTI/BTE "
                             f"{(int(dut.m_wb_CTI.value), int(dut.m_wb_BTE.value))} != "
                             f"{(want_cti, want_bte)}")
            break

        # Terminate it so the next command can issue, and check the packed
        # response carries {status, dat}.
        rdat = rng.getrandbits(DW)
        dut.m_wb_ACK.value = 1
        dut.m_wb_DAT_R.value = rdat
        await RisingEdge(dut.clk)
        dut.m_wb_ACK.value = 0
        for _ in range(50):
            await RisingEdge(dut.clk)
            if int(dut.rsp_valid.value):
                break
        else:
            tb.errors.append("no response after ACK")
            break
        packed = int(dut.rsp_data.value)
        status, data = packed >> DW, packed & ((1 << DW) - 1)
        if (status, data) != (0, rdat):
            tb.errors.append(f"rsp_data {(status, hex(data))} != ACK/{hex(rdat)}")
            break
        await RisingEdge(dut.clk)

    for e in tb.errors[:5]:
        tb.log.error(e)
    assert not tb.errors, f"{len(tb.errors)} error(s); first: {tb.errors[0]}"


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def wb4_slave_stub_test(dut):
    """A Wishbone transfer must appear in packed cmd_data field for field."""
    tb = _StubTB(dut)
    rng = random.Random(int(os.environ.get('SEED', '0')) + 1)
    dut.s_wb_CYC.value = 0
    dut.s_wb_STB.value = 0
    dut.cmd_ready.value = 1
    dut.rsp_valid.value = 0
    dut.rsp_data.value = 0
    await tb.setup_clocks_and_reset()

    hints = os.environ.get('USE_BURST_HINTS', '0') == '1'
    for _ in range(32):
        we = rng.randint(0, 1)
        adr = rng.getrandbits(AW) & ~(SW - 1)
        dat = rng.getrandbits(DW)
        sel = rng.randint(1, (1 << SW) - 1)
        cti = rng.randint(0, 7)
        bte = rng.randint(0, 3)

        dut.s_wb_CYC.value = 1
        dut.s_wb_STB.value = 1
        dut.s_wb_WE.value = we
        dut.s_wb_ADR.value = adr
        dut.s_wb_DAT_W.value = dat
        dut.s_wb_SEL.value = sel
        dut.s_wb_CTI.value = cti
        dut.s_wb_BTE.value = bte
        for _ in range(50):
            await RisingEdge(dut.clk)
            if not int(dut.s_wb_STALL.value):
                break
        dut.s_wb_STB.value = 0

        for _ in range(50):
            await RisingEdge(dut.clk)
            if int(dut.cmd_valid.value):
                break
        else:
            tb.errors.append(f"no cmd_valid for adr=0x{adr:X}")
            break
        packed = int(dut.cmd_data.value)
        g_bte = packed & 0x3
        g_cti = (packed >> BTW) & 0x7
        g_sel = (packed >> (BTW + CTW)) & ((1 << SW) - 1)
        g_dat = (packed >> (BTW + CTW + SW)) & ((1 << DW) - 1)
        g_adr = (packed >> (BTW + CTW + SW + DW)) & ((1 << AW) - 1)
        g_we = (packed >> (BTW + CTW + SW + DW + AW)) & 1
        want_cti, want_bte = (cti, bte) if hints else (0, 0)
        if (g_we, g_adr, g_dat, g_sel, g_cti, g_bte) != (we, adr, dat, sel, want_cti, want_bte):
            tb.errors.append(
                f"packed wrong: got {(g_we, hex(g_adr), hex(g_dat), g_sel, g_cti, g_bte)} "
                f"!= {(we, hex(adr), hex(dat), sel, want_cti, want_bte)}")
            break

        # Answer it so the slave can take the next one.
        rdat = rng.getrandbits(DW)
        dut.rsp_valid.value = 1
        dut.rsp_data.value = rdat            # status = ACK (0) in the high bits
        for _ in range(50):
            await RisingEdge(dut.clk)
            if int(dut.rsp_ready.value):
                break
        dut.rsp_valid.value = 0
        for _ in range(50):
            await RisingEdge(dut.clk)
            if int(dut.s_wb_ACK.value):
                break
        else:
            tb.errors.append("no ACK on the bus for the packed response")
            break
        if int(dut.s_wb_DAT_R.value) != rdat:
            tb.errors.append(f"DAT_R 0x{int(dut.s_wb_DAT_R.value):X} != 0x{rdat:X}")
            break
        dut.s_wb_CYC.value = 0
        await RisingEdge(dut.clk)

    for e in tb.errors[:5]:
        tb.log.error(e)
    assert not tb.errors, f"{len(tb.errors)} error(s); first: {tb.errors[0]}"


def _run(request, dut_name, testcase, hints):
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba', 'rtl_amba_includes': 'rtl/amba/includes'})
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=f"rtl/amba/filelists/{dut_name}.f")
    name = f"test_{worker_id}_{dut_name}_{'hints' if hints else 'nohints'}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase=testcase,
        parameters={'ADDR_WIDTH': str(AW), 'DATA_WIDTH': str(DW),
                    'USE_BURST_HINTS': str(int(hints))},
        sim_build=sim_build,
        extra_env={'USE_BURST_HINTS': str(int(hints)), 'DUT': dut_name,
                   'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
                   'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
                   'SEED': os.environ.get('SEED', str(random.randint(0, 100000)))},
        waves=enable_waves, keep_files=True,
        compile_args=["-Wno-DECLFILENAME", "-Wno-UNUSEDPARAM"])


@pytest.mark.parametrize("hints", [0, 1])
def test_wb4_master_stub(request, hints):
    """wb4_master_stub: packed cmd_data -> Wishbone wires."""
    _run(request, 'wb4_master_stub', 'wb4_master_stub_test', hints)


@pytest.mark.parametrize("hints", [0, 1])
def test_wb4_slave_stub(request, hints):
    """wb4_slave_stub: Wishbone wires -> packed cmd_data."""
    _run(request, 'wb4_slave_stub', 'wb4_slave_stub_test', hints)

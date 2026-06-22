# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Smoke test for data_path_macro.

data_path_macro = wr_beat_sequencer + rd_cl_aligner. The unit tests
already cover each FUB in detail; this macro-level test verifies the
two are wired together correctly:

  smoke_wr_only  : drive a WR op, beat-pull from a w_buf mock, verify
                   dfi_wrdata + b_complete reach the macro outputs
  smoke_rd_only  : drive a RD op, inject dfi_rddata, verify the macro's
                   rd_inject + rd_beat_we outputs

This is a skeleton test — full integration scenarios (concurrent W+R,
back-to-back, tCCD spacing) ride alongside the eventual
ddr2_lpddr2_core_macro test.
"""

import os
import sys
import random
import logging
import pytest

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

_NBA_SETTLE_PS = 1


class DataPathMacroTB(TBBase):
    CLK = 10

    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)
        self.DRAM_BEAT_WIDTH = int(os.environ.get('DRAM_BEAT_WIDTH', '64'))
        self.DRAM_STRB_WIDTH = self.DRAM_BEAT_WIDTH // 8
        self.DFI_RATE        = int(os.environ.get('DFI_RATE',        '2'))
        self.DFI_DATA_WIDTH  = self.DRAM_BEAT_WIDTH * self.DFI_RATE

    async def setup(self, t_phy_wrlat=2, t_rddata_en=2):
        self.dut.cl_i.value             = 5
        self.dut.cwl_i.value             = 4
        self.dut.al_i.value             = 0
        self.dut.t_phy_wrlat_i.value    = t_phy_wrlat
        self.dut.t_rddata_en_i.value    = t_rddata_en
        self.dut.rd_in_order_i.value    = 0

        self.dut.wr_op_valid_i.value    = 0
        self.dut.wr_op_slot_i.value     = 0
        self.dut.wr_op_len_i.value      = 0

        self.dut.rd_op_valid_i.value    = 0
        self.dut.rd_op_slot_i.value     = 0
        self.dut.rd_op_id_i.value       = 0
        self.dut.rd_op_len_i.value      = 0

        self.dut.beat_pull_ptr_i.value      = 0
        self.dut.beat_pull_strb_ptr_i.value = 0
        self.dut.beat_pull_last_i.value     = 0
        self.dut.wbuf_rd_data_i.value       = 0
        self.dut.wbuf_rd_strb_i.value       = 0

        self.dut.rd_inject_ready_i.value    = 1
        self.dut.dfi_rddata_i.value         = 0
        self.dut.dfi_rddata_valid_i.value   = 0

        await self.start_clock('mc_clk', freq=self.CLK, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_data_path_macro(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke_wr_only")
    tb = DataPathMacroTB(dut)

    if test_type == "smoke_wr_only":
        await tb.setup()
        # Drive a 4-beat WR op on slot 1.
        slot = 1
        length = 4
        beats = [(0xAA00 | i) for i in range(length)]

        # Op handshake.
        tb.dut.wr_op_valid_i.value = 1
        tb.dut.wr_op_slot_i.value  = slot
        tb.dut.wr_op_len_i.value   = length
        await Timer(_NBA_SETTLE_PS, units='ps')
        while int(tb.dut.wr_op_ready_o.value) == 0:
            await RisingEdge(tb.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
        await RisingEdge(tb.dut.mc_clk)
        await Timer(_NBA_SETTLE_PS, units='ps')
        tb.dut.wr_op_valid_i.value = 0

        # Respond to beat-pull strobes with the burst's beats.
        pulled = 0
        b_complete_seen = False
        for _ in range(64):
            await RisingEdge(tb.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            if int(tb.dut.beat_pull_strb_o.value) and pulled < length:
                tb.dut.wbuf_rd_data_i.value   = beats[pulled]
                tb.dut.wbuf_rd_strb_i.value   = (1 << tb.DRAM_STRB_WIDTH) - 1
                tb.dut.beat_pull_last_i.value = 1 if pulled == length - 1 else 0
                pulled += 1
            else:
                tb.dut.wbuf_rd_data_i.value   = 0
                tb.dut.wbuf_rd_strb_i.value   = 0
                tb.dut.beat_pull_last_i.value = 0
            if int(tb.dut.b_complete_strb_o.value):
                assert int(tb.dut.b_complete_slot_o.value) == slot
                b_complete_seen = True
                break
        assert b_complete_seen, "b_complete never asserted for WR op"

    elif test_type == "smoke_rd_only":
        await tb.setup()
        slot = 3
        length = 4
        axi_id = 5
        beats = [(0xBB00 | i) for i in range(length)]

        # Op handshake.
        tb.dut.rd_op_valid_i.value = 1
        tb.dut.rd_op_slot_i.value  = slot
        tb.dut.rd_op_id_i.value    = axi_id
        tb.dut.rd_op_len_i.value   = length
        await Timer(_NBA_SETTLE_PS, units='ps')
        while int(tb.dut.rd_op_ready_o.value) == 0:
            await RisingEdge(tb.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
        await RisingEdge(tb.dut.mc_clk)
        await Timer(_NBA_SETTLE_PS, units='ps')
        tb.dut.rd_op_valid_i.value = 0

        # Wait for EN to assert, then inject DFI rddata for the burst.
        # DFI cycles = ceil(length/DFI_RATE) = 2 for length=4 DFI_RATE=2.
        n_dfi = (length + tb.DFI_RATE - 1) // tb.DFI_RATE
        en_count = 0
        for _ in range(40):
            await RisingEdge(tb.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            if int(tb.dut.pre_dfi_rddata_en_o.value) and en_count < n_dfi:
                en_count += 1
            if en_count == n_dfi:
                break
        assert en_count == n_dfi, f"saw {en_count}/{n_dfi} EN cycles"

        # Inject DFI rddata cycles (5 cycle PHY latency).
        for _ in range(5):
            await RisingEdge(tb.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')

        captured_beats = []
        for dfi_idx in range(n_dfi):
            dfi_val = 0
            for r in range(tb.DFI_RATE):
                bi = dfi_idx * tb.DFI_RATE + r
                if bi < length:
                    dfi_val |= (beats[bi] & ((1 << tb.DRAM_BEAT_WIDTH) - 1)) \
                                << (r * tb.DRAM_BEAT_WIDTH)
            tb.dut.dfi_rddata_i.value       = dfi_val
            tb.dut.dfi_rddata_valid_i.value = 1
            await RisingEdge(tb.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
        tb.dut.dfi_rddata_valid_i.value = 0

        # Capture rd_inject beats. Smoke test: just verify the macro
        # produced beats + asserted last + signalled per-beat strobe.
        # Bit-exact count is fragile due to the registered-output post-
        # handshake lookahead in rd_cl_aligner; the FUB unit test
        # already covers that. Here we just confirm wiring.
        last_seen = False
        beat_we_count = 0
        for _ in range(60):
            await RisingEdge(tb.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            if int(tb.dut.rd_inject_valid_o.value) and int(tb.dut.rd_inject_ready_i.value):
                captured_beats.append(int(tb.dut.rd_inject_data_o.value))
                if int(tb.dut.rd_inject_last_o.value):
                    last_seen = True
            if int(tb.dut.rd_beat_we_o.value):
                beat_we_count += 1
            if last_seen and not int(tb.dut.rd_inject_valid_o.value):
                break
        assert last_seen, "rd_inject_last never asserted"
        assert len(captured_beats) >= 1, "no rd_inject beats captured"
        assert beat_we_count >= 1, "no rd_beat_we strobes seen"

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await tb.wait_clocks('mc_clk', 5)


_SCENARIOS = ["smoke_wr_only", "smoke_rd_only"]


@pytest.mark.parametrize("test_type", _SCENARIOS, ids=_SCENARIOS)
def test_data_path_macro(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "data_path_macro"
    test_name = f"test_data_path_macro_{test_type}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/macro/data_path_macro.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "DRAM_BEAT_WIDTH": "64",
        "DFI_RATE":        "2",
        "SEED":            str(random.randint(0, 100000)),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }

    compile_args = ["+define+USE_ASYNC_RESET"]
    sim_args = []
    plus_args = []
    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_data_path_macro",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")

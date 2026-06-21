# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Unit-test runner for `global_timers_fub`. Verifies tFAW window (max 4
ACTs), tRRD spacing, tWTR / tRTW turnaround flags.
"""

import os
import sys
import random
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


class GtTB(TBBase):
    CLK = 10

    async def setup(self, t_faw=20, t_rrd=4, t_wtr=4, t_rtw=4):
        self.dut.t_faw_i.value          = t_faw
        self.dut.t_rrd_i.value          = t_rrd
        self.dut.t_wtr_global_i.value   = t_wtr
        self.dut.t_rtw_i.value          = t_rtw
        self.dut.evt_act_i.value        = 0
        self.dut.evt_act_rank_i.value   = 0
        self.dut.evt_rd_i.value         = 0
        self.dut.evt_wr_i.value         = 0
        await self.start_clock('mc_clk', freq=self.CLK, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    async def pulse(self, kind: str):
        sig = {'act': self.dut.evt_act_i,
               'rd':  self.dut.evt_rd_i,
               'wr':  self.dut.evt_wr_i}[kind]
        sig.value = 1
        await RisingEdge(self.dut.mc_clk)
        await Timer(1, units='ps')
        sig.value = 0

    def tfaw_ok(self) -> bool: return bool(int(self.dut.tfaw_window_ok_o.value))
    def trrd_ok(self) -> bool: return bool(int(self.dut.trrd_window_ok_o.value))
    def twtr_ok(self) -> bool: return bool(int(self.dut.twtr_global_ok_o.value))
    def trtw_ok(self) -> bool: return bool(int(self.dut.trtw_window_ok_o.value))


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_global_timers(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    tb = GtTB(dut)

    if test_type == "smoke":
        await tb.setup(t_faw=20, t_rrd=4, t_wtr=4, t_rtw=4)
        assert tb.tfaw_ok() and tb.trrd_ok() and tb.twtr_ok() and tb.trtw_ok()

    elif test_type == "tfaw_4_acts":
        await tb.setup(t_faw=20, t_rrd=0)  # disable tRRD constraint
        # Fire 4 ACTs in rapid succession; window should stay OPEN through
        # the 4th, then become CLOSED on the 5th.
        for _ in range(4):
            assert tb.tfaw_ok(), "window should be open before 4 ACTs"
            await tb.pulse('act')
            await tb.wait_clocks('mc_clk', 1)
        # After 4th ACT, window should be CLOSED (all 4 slots busy).
        assert not tb.tfaw_ok(), "window should close after 4 ACTs"
        # Wait t_faw cycles → first slot expires → window opens.
        await tb.wait_clocks('mc_clk', 20)
        assert tb.tfaw_ok(), "window should reopen after t_faw"

    elif test_type == "trrd_spacing":
        await tb.setup(t_rrd=5)
        # ACT, immediately check trrd not ok
        await tb.pulse('act')
        await tb.wait_clocks('mc_clk', 1)
        assert not tb.trrd_ok()
        # Wait for tRRD to expire
        await tb.wait_clocks('mc_clk', 5)
        assert tb.trrd_ok()

    elif test_type == "twtr_after_wr":
        await tb.setup(t_wtr=4)
        await tb.pulse('wr')
        await tb.wait_clocks('mc_clk', 1)
        assert not tb.twtr_ok()
        await tb.wait_clocks('mc_clk', 4)
        assert tb.twtr_ok()

    elif test_type == "trtw_after_rd":
        await tb.setup(t_rtw=4)
        await tb.pulse('rd')
        await tb.wait_clocks('mc_clk', 1)
        assert not tb.trtw_ok()
        await tb.wait_clocks('mc_clk', 4)
        assert tb.trtw_ok()

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await tb.wait_clocks('mc_clk', 3)


_GATE = [("smoke",), ("tfaw_4_acts",)]
_FUNC = _GATE + [("trrd_spacing",), ("twtr_after_wr",), ("trtw_after_rd",)]
_FULL = _FUNC

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_global_timers(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "global_timers_fub"
    test_name = f"test_global_timers_{test_type}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/fub/global_timers_fub.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "SEED": str(random.randint(0, 100000)),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET"]
    sim_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_global_timers",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")

# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Unit-test runner for `pumice_zq_ctrl`. Verifies ZQCS/ZQCL interval firing,
grant hold time, deferral/overdue policy, DDR2 inertness, and command payload.
"""

import os
import sys
import random
import pytest

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from pumice_coverage import (  # noqa: E402
    get_coverage_compile_args, get_coverage_env,
)


class ZqTB(TBBase):
    CLK = 10

    async def setup(self, interval: int = 20, t_zqcs: int = 3, t_zqcl: int = 6,
                    defer_en: int = 0, overdue_max: int = 0):
        self.dut.zq_en_i.value = 0
        self.dut.init_done_i.value = 0
        self.dut.memtype_i.value = 0b100      # LPDDR2 (family encoding, mc_common_pkg)
        self.dut.t_zqcs_interval_i.value = interval
        self.dut.t_zqcs_i.value = t_zqcs
        self.dut.t_zqcl_i.value = t_zqcl
        self.dut.zq_defer_en_i.value = defer_en
        self.dut.overdue_max_i.value = overdue_max
        self.dut.demand_i.value = 0
        self.dut.zq_grant_i.value = 0

        await self.start_clock('mc_clk', freq=self.CLK, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    async def enable(self):
        self.dut.zq_en_i.value = 1
        self.dut.init_done_i.value = 1

    async def grant_one(self):
        self.dut.zq_grant_i.value = 1
        await RisingEdge(self.dut.mc_clk)
        await Timer(1, units='ps')
        self.dut.zq_grant_i.value = 0

    def req(self) -> bool:
        return bool(int(self.dut.zq_req_o.value))

    def busy(self) -> bool:
        return bool(int(self.dut.cal_busy_o.value))

    def overdue(self) -> bool:
        return bool(int(self.dut.obs_overdue_o.value))

    def total(self) -> int:
        return int(self.dut.obs_zqcs_total_o.value)

    def row(self) -> int:
        return int(self.dut.zq_row_o.value)

    def is_zqcl(self) -> bool:
        return bool(int(self.dut.zq_is_zqcl_o.value))


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_pumice_zq_ctrl(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    tb = ZqTB(dut)
    await tb.setup()

    if test_type == "smoke":
        # Disabled: no request, not busy, no overdue.
        await tb.wait_clocks('mc_clk', 10)
        assert not tb.req()
        assert not tb.busy()
        assert not tb.overdue()

        # Enable and wait for interval expiry.
        await tb.enable()
        for _ in range(30):
            await tb.wait_clocks('mc_clk', 1)
            if tb.req():
                break
        assert tb.req(), "ZQ req should fire after interval expiry"
        assert not tb.is_zqcl(), "first request should be ZQCS"

        # Grant: hold for t_zqcs cycles, then idle again.
        await tb.grant_one()
        await tb.wait_clocks('mc_clk', 1)
        assert tb.busy(), "busy should be high in ZQ_HOLD"
        while tb.busy():
            await tb.wait_clocks('mc_clk', 1)
        assert not tb.busy(), "busy should drop after t_zqcs hold"
        assert tb.total() == 1

    elif test_type == "ddr2_inert":
        # DDR2 memtype should keep the FUB quiet regardless of enable.
        dut.memtype_i.value = 0
        await tb.enable()
        await tb.wait_clocks('mc_clk', 40)
        assert not tb.req()
        assert not tb.busy()
        assert tb.total() == 0

    elif test_type == "zqcl_long_run":
        # Force a ZQCL by deferring until overdue_max.
        dut.t_zqcs_interval_i.value = 10
        dut.zq_defer_en_i.value = 1
        dut.overdue_max_i.value = 5
        dut.demand_i.value = 1
        await tb.enable()
        # Wait until overdue deferral converts to a request.
        for _ in range(40):
            await tb.wait_clocks('mc_clk', 1)
            if tb.req():
                break
        assert tb.req(), "ZQ should request after overdue deferral"
        assert tb.is_zqcl(), "overdue deferral should select ZQCL"
        assert tb.overdue(), "overdue flag should be set"

        # MR10 row packing: {4'b0, MA[5:0]=10, OP[7:0]=0xAB}
        assert tb.row() == ((10 << 8) | 0xAB), f"ZQCL row={tb.row():#x}"
        await tb.grant_one()
        await tb.wait_clocks('mc_clk', 8)
        assert tb.total() == 1

    elif test_type == "defer_drop_demand":
        # Defer under demand, then drop demand -> immediate ZQCS request.
        dut.t_zqcs_interval_i.value = 10
        dut.zq_defer_en_i.value = 1
        dut.demand_i.value = 1
        await tb.enable()
        # Wait until the interval expires and the FSM enters DEFER.
        for _ in range(40):
            await tb.wait_clocks('mc_clk', 1)
            if tb.overdue():
                break
        assert tb.overdue(), "should be in deferral/overdue"
        # Drop demand -> should transition to REQ on next cycle. If any
        # deferral cycles elapsed, the FUB selects ZQCL; if demand drops on
        # the very first DEFER cycle it selects ZQCS. Either is legal.
        dut.demand_i.value = 0
        for _ in range(10):
            await tb.wait_clocks('mc_clk', 1)
            if tb.req():
                break
        assert tb.req(), "ZQ req should fire when demand drops"

    elif test_type == "hold_time":
        # Verify the post-grant quiet window lasts exactly t_zqcs/t_zqcl.
        for t_zqcs, t_zqcl in [(2, 4), (5, 9)]:
            dut.t_zqcs_i.value = t_zqcs
            dut.t_zqcl_i.value = t_zqcl
            dut.t_zqcs_interval_i.value = 10
            await tb.enable()
            for _ in range(40):
                await tb.wait_clocks('mc_clk', 1)
                if tb.req():
                    break
            assert tb.req(), "ZQCS req never fired"
            await tb.grant_one()
            for _ in range(10):
                await tb.wait_clocks('mc_clk', 1)
                if tb.busy():
                    break
            assert tb.busy(), "busy did not assert after ZQCS grant"
            busy_cycles = 0
            while tb.busy():
                await tb.wait_clocks('mc_clk', 1)
                busy_cycles += 1
            # cal_busy_o is registered: it is high for t_zqcs+1 cycles.
            assert busy_cycles == t_zqcs + 1, f"ZQCS hold = {busy_cycles}, expected {t_zqcs + 1}"
            # Force a ZQCL grant and check its hold.
            dut.zq_defer_en_i.value = 1
            dut.demand_i.value = 1
            dut.overdue_max_i.value = 3
            for _ in range(40):
                await tb.wait_clocks('mc_clk', 1)
                if tb.req() and tb.is_zqcl():
                    break
            assert tb.req() and tb.is_zqcl(), "ZQCL req never fired"
            await tb.grant_one()
            for _ in range(10):
                await tb.wait_clocks('mc_clk', 1)
                if tb.busy():
                    break
            assert tb.busy(), "busy did not assert after ZQCL grant"
            busy_cycles = 0
            while tb.busy():
                await tb.wait_clocks('mc_clk', 1)
                busy_cycles += 1
            assert busy_cycles == t_zqcl + 1, f"ZQCL hold = {busy_cycles}, expected {t_zqcl + 1}"
            # Cleanup for next param set.
            dut.zq_defer_en_i.value = 0
            dut.demand_i.value = 0
            dut.overdue_max_i.value = 0
            await tb.wait_clocks('mc_clk', 5)

    elif test_type == "interval_0_disabled":
        # interval=0 disables the periodic timer.
        dut.t_zqcs_interval_i.value = 0
        await tb.enable()
        await tb.wait_clocks('mc_clk', 50)
        assert not tb.req()
        assert tb.total() == 0

    elif test_type == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '12345')))
        test_level = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n_cycles = {"GATE": 200, "FUNC": 1000, "FULL": 5000}.get(test_level, 1000)

        dut.zq_defer_en_i.value = 1
        await tb.enable()
        grants = 0
        for _ in range(n_cycles):
            dut.demand_i.value = 1 if rng.random() < 0.4 else 0
            dut.overdue_max_i.value = rng.randint(0, 20)
            await tb.wait_clocks('mc_clk', 1)
            if tb.req() and rng.random() < 0.8:
                await tb.grant_one()
                grants += 1
        assert grants >= n_cycles // 200
        assert tb.total() == grants

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await tb.wait_clocks('mc_clk', 3)


_GATE = [("smoke",), ("ddr2_inert",)]
_FUNC = _GATE + [("zqcl_long_run",), ("defer_drop_demand",), ("hold_time",),
                 ("interval_0_disabled",), ("random_soak",)]
_FULL = _FUNC

_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_pumice_zq_ctrl(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_zq_ctrl"
    test_name = f"test_pumice_zq_ctrl_{test_type}"

    filelist_path = ("projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/"
                     "rtl/filelists/fub/pumice_zq_ctrl.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
        "TEST_LEVEL": _TEST_LEVEL,
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
        sim_args += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    compile_args += get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_pumice_zq_ctrl",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")

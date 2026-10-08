# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Unit-test runner for `pumice_lp_cal`. Verifies MRR32/MRR40 sequencing,
grant-to-expect pulse, data capture, tMRR spacing, timeout error, and DDR2
inertness.
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


class LpCalTB(TBBase):
    CLK = 10
    DFI_DW = 128

    async def setup(self, t_mrr: int = 3, t_readout: int = 20):
        self.dut.cal_start_i.value = 0
        self.dut.cal_abort_i.value = 0
        self.dut.init_done_i.value = 0
        self.dut.memtype_i.value = 1           # LPDDR2
        self.dut.t_mrr_i.value = t_mrr
        self.dut.t_readout_i.value = t_readout
        self.dut.cmd_grant_i.value = 0
        self.dut.cal_data_i.value = 0
        self.dut.cal_data_valid_i.value = 0

        await self.start_clock('mc_clk', freq=self.CLK, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    async def start(self):
        self.dut.cal_start_i.value = 1
        await RisingEdge(self.dut.mc_clk)
        await Timer(1, units='ps')
        self.dut.cal_start_i.value = 0

    async def abort(self):
        self.dut.cal_abort_i.value = 1
        await RisingEdge(self.dut.mc_clk)
        await Timer(1, units='ps')
        self.dut.cal_abort_i.value = 0

    async def grant_one(self):
        self.dut.cmd_grant_i.value = 1
        await RisingEdge(self.dut.mc_clk)
        await Timer(1, units='ps')
        self.dut.cmd_grant_i.value = 0

    async def send_data(self, data: int):
        self.dut.cal_data_i.value = data
        self.dut.cal_data_valid_i.value = 1
        await RisingEdge(self.dut.mc_clk)
        await Timer(1, units='ps')
        self.dut.cal_data_valid_i.value = 0
        self.dut.cal_data_i.value = 0

    def req(self) -> bool:
        return bool(int(self.dut.cmd_req_o.value))

    def busy(self) -> bool:
        return bool(int(self.dut.cal_busy_o.value))

    def done(self) -> bool:
        return bool(int(self.dut.cal_done_o.value))

    def err(self) -> bool:
        return bool(int(self.dut.cal_err_o.value))

    def expect(self) -> bool:
        return bool(int(self.dut.cal_expect_o.value))

    def row(self) -> int:
        return int(self.dut.cmd_row_o.value)

    def mrr32(self) -> int:
        return int(self.dut.mrr32_data_o.value)

    def mrr40(self) -> int:
        return int(self.dut.mrr40_data_o.value)

    def mrr32_valid(self) -> bool:
        return bool(int(self.dut.mrr32_valid_o.value))

    def mrr40_valid(self) -> bool:
        return bool(int(self.dut.mrr40_valid_o.value))


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_pumice_lp_cal(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    tb = LpCalTB(dut)
    await tb.setup()

    if test_type == "smoke":
        # Inert before init_done.
        dut.init_done_i.value = 0
        await tb.start()
        await tb.wait_clocks('mc_clk', 10)
        assert not tb.busy()
        assert not tb.req()

        # Enable run and start one-shot.
        dut.init_done_i.value = 1
        await tb.wait_clocks('mc_clk', 2)
        cocotb.start_soon(tb.start())

        # Wait for MR32 request.
        for _ in range(20):
            await tb.wait_clocks('mc_clk', 1)
            if tb.req():
                break
        assert tb.req(), "MR32 req should fire after start"
        # Row packing: {4'b0, MA[5:0]=32, OP[7:0]=0}
        assert tb.row() == (32 << 8), f"MR32 row={tb.row():#x}"

        # Grant moves to PULSE_EXPECT32 on the next cycle, which asserts
        # cal_expect_o for exactly one cycle.
        await tb.grant_one()
        assert tb.expect(), "cal_expect should pulse in PULSE_EXPECT32 after MR32 grant"
        await tb.wait_clocks('mc_clk', 1)
        assert not tb.expect(), "cal_expect should be one cycle wide"

        # Provide captured data.
        await tb.send_data(0xAAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA)
        await tb.wait_clocks('mc_clk', 2)
        assert tb.mrr32_valid(), "MRR32 data should be valid"
        assert tb.mrr32() == 0xAAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA

        # Wait t_mrr spacing, then MR40 request.
        for _ in range(20):
            await tb.wait_clocks('mc_clk', 1)
            if tb.req():
                break
        assert tb.req(), "MR40 req should fire after t_mrr"
        assert tb.row() == (40 << 8), f"MR40 row={tb.row():#x}"

        await tb.grant_one()
        assert tb.expect(), "cal_expect should pulse in PULSE_EXPECT40 after MR40 grant"
        await tb.wait_clocks('mc_clk', 1)
        assert not tb.expect(), "cal_expect should be one cycle wide"

        await tb.send_data(0x5555_5555_5555_5555_5555_5555_5555_5555)
        await tb.wait_clocks('mc_clk', 2)
        assert tb.mrr40_valid(), "MRR40 data should be valid"
        assert tb.mrr40() == 0x5555_5555_5555_5555_5555_5555_5555_5555
        assert tb.done(), "cal_done should be sticky after MR40 capture"
        assert not tb.err()
        assert not tb.busy()

    elif test_type == "ddr2_inert":
        dut.memtype_i.value = 0              # DDR2
        dut.init_done_i.value = 1
        await tb.start()
        await tb.wait_clocks('mc_clk', 30)
        assert not tb.busy()
        assert not tb.req()
        assert not tb.done()

    elif test_type == "timeout_error":
        dut.init_done_i.value = 1
        dut.t_readout_i.value = 5
        await tb.start()
        for _ in range(20):
            await tb.wait_clocks('mc_clk', 1)
            if tb.req():
                break
        await tb.grant_one()
        # Never provide data; wait for timeout.
        for _ in range(20):
            await tb.wait_clocks('mc_clk', 1)
            if tb.err():
                break
        assert tb.err(), "cal_err should assert on readout timeout"
        assert tb.done()

    elif test_type == "abort_clears_state":
        dut.init_done_i.value = 1
        await tb.start()
        for _ in range(20):
            await tb.wait_clocks('mc_clk', 1)
            if tb.req():
                break
        await tb.abort()
        await tb.wait_clocks('mc_clk', 3)
        assert not tb.busy(), "abort should return FSM to IDLE"
        assert not tb.req()

    elif test_type == "sticky_done_persists":
        dut.init_done_i.value = 1
        await tb.start()
        # MR32
        for _ in range(20):
            await tb.wait_clocks('mc_clk', 1)
            if tb.req():
                break
        await tb.grant_one()
        await tb.wait_clocks('mc_clk', 1)  # PULSE_EXPECT32 -> WAIT_DATA32
        await tb.send_data(0xDEAD_BEEF_DEAD_BEEF_DEAD_BEEF_DEAD_BEEF)
        # MR40
        for _ in range(20):
            await tb.wait_clocks('mc_clk', 1)
            if tb.req():
                break
        await tb.grant_one()
        await tb.wait_clocks('mc_clk', 1)  # PULSE_EXPECT40 -> WAIT_DATA40
        await tb.send_data(0xCAFE_BABE_CAFE_BABE_CAFE_BABE_CAFE_BABE)
        await tb.wait_clocks('mc_clk', 2)
        # Wait well past completion; done/valid should stay set.
        await tb.wait_clocks('mc_clk', 50)
        assert tb.mrr32_valid()
        assert tb.mrr40_valid()
        assert tb.done()

    elif test_type == "tmrr_spacing":
        # Measure spacing between MR32 capture and MR40 request.
        dut.init_done_i.value = 1
        dut.t_mrr_i.value = 7
        await tb.start()
        for _ in range(20):
            await tb.wait_clocks('mc_clk', 1)
            if tb.req():
                break
        await tb.grant_one()
        await tb.wait_clocks('mc_clk', 2)  # PULSE_EXPECT32 -> WAIT_DATA32 -> capture
        await tb.send_data(0x1111_2222_3333_4444_5555_6666_7777_8888)
        # Count cycles from end of data-valid cycle to next req assertion.
        # The FSM loads t_mrr then decrements it in WAIT_TMRR; it transitions
        # to WAIT_GRANT40 on the cycle AFTER r_timer reaches 0, so the observed
        # spacing is t_mrr_i + 1.
        spacing = 0
        while not tb.req():
            await tb.wait_clocks('mc_clk', 1)
            spacing += 1
        assert spacing == 8, f"t_mrr spacing = {spacing}, expected 8 (t_mrr+1)"

    elif test_type == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '12345')))
        test_level = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n_runs = {"GATE": 5, "FUNC": 20, "FULL": 100}.get(test_level, 20)

        dut.init_done_i.value = 1
        for _ in range(n_runs):
            dut.t_mrr_i.value = rng.randint(1, 8)
            dut.t_readout_i.value = rng.randint(5, 30)
            await tb.start()
            # MR32
            while not tb.req():
                await tb.wait_clocks('mc_clk', 1)
            await tb.grant_one()
            while not tb.expect():
                await tb.wait_clocks('mc_clk', 1)
            await tb.wait_clocks('mc_clk', 1)  # PULSE_EXPECT32 -> WAIT_DATA32
            d32 = rng.getrandbits(128)
            await tb.send_data(d32)
            # MR40
            while not tb.req():
                await tb.wait_clocks('mc_clk', 1)
            await tb.grant_one()
            while not tb.expect():
                await tb.wait_clocks('mc_clk', 1)
            await tb.wait_clocks('mc_clk', 1)  # PULSE_EXPECT40 -> WAIT_DATA40
            d40 = rng.getrandbits(128)
            await tb.send_data(d40)
            while not tb.done():
                await tb.wait_clocks('mc_clk', 1)
            assert tb.mrr32() == d32
            assert tb.mrr40() == d40
            await tb.wait_clocks('mc_clk', rng.randint(2, 10))

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await tb.wait_clocks('mc_clk', 3)


_GATE = [("smoke",), ("ddr2_inert",)]
_FUNC = _GATE + [("timeout_error",), ("abort_clears_state",),
                 ("sticky_done_persists",), ("tmrr_spacing",), ("random_soak",)]
_FULL = _FUNC

_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_pumice_lp_cal(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_lp_cal"
    test_name = f"test_pumice_lp_cal_{test_type}"

    filelist_path = ("projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2/"
                     "rtl/filelists/fub/pumice_lp_cal.f")
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
        testcase="cocotb_test_pumice_lp_cal",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")

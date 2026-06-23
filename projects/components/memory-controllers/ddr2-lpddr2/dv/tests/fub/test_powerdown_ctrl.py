# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Unit-test runner for `powerdown_ctrl`. Verifies the FSM
AWAKE → ARMING → REQ → ASLEEP → AWAKE.
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

from tbclasses.trackers import PowerdownTracker  # noqa: E402


class PdnTB(TBBase):
    CLK = 10

    async def setup(self, idle_threshold: int = 10):
        self.dut.idle_threshold_i.value   = idle_threshold
        self.dut.enable_pde_i.value       = 1
        self.dut.enable_sref_i.value      = 0
        self.dut.controller_idle_i.value  = 0
        self.dut.pdn_grant_i.value        = 0
        await self.start_clock('mc_clk', freq=self.CLK, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    def req(self) -> bool:
        return bool(int(self.dut.pdn_req_o.value))

    def cke(self) -> int:
        return int(self.dut.dfi_cke_o.value)

    def kind(self) -> int:
        return int(self.dut.pdn_kind_o.value)

    def sref_active(self) -> bool:
        return bool(int(self.dut.sref_active_o.value))

    async def go_idle(self):
        self.dut.controller_idle_i.value = 1

    async def go_active(self):
        self.dut.controller_idle_i.value = 0

    async def grant(self):
        self.dut.pdn_grant_i.value = 1
        await RisingEdge(self.dut.mc_clk)
        await Timer(1, units='ps')
        self.dut.pdn_grant_i.value = 0


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_powerdown_ctrl(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    tb = PdnTB(dut)
    # Tracker auto-dumps <sim_build>/pdn.out at end of sim.
    pdn_tracker = PowerdownTracker(dut, num_ranks=1)
    cocotb.start_soon(pdn_tracker.run())
    await tb.setup(idle_threshold=10)

    if test_type == "smoke":
        # Initial state: awake, CKE high.
        assert tb.cke() == 1
        # Go idle; after 10+ cycles req should rise.
        await tb.go_idle()
        await tb.wait_clocks('mc_clk', 15)
        assert tb.req(), "pdn_req should rise after idle threshold"
        # Grant — FSM goes to ASLEEP, CKE drops.
        await tb.grant()
        await tb.wait_clocks('mc_clk', 2)
        assert tb.cke() == 0, "CKE should be low after grant"
        assert not tb.req()
        # Activity — wake up.
        await tb.go_active()
        await tb.wait_clocks('mc_clk', 2)
        assert tb.cke() == 1, "CKE should rise on wake"

    elif test_type == "early_wake":
        # Idle starts, but activity arrives before threshold expires.
        await tb.go_idle()
        await tb.wait_clocks('mc_clk', 5)   # below threshold of 10
        assert not tb.req()
        await tb.go_active()
        await tb.wait_clocks('mc_clk', 2)
        # FSM returned to AWAKE.
        assert tb.cke() == 1

    elif test_type == "disable_pde":
        tb.dut.enable_pde_i.value = 0
        await tb.go_idle()
        await tb.wait_clocks('mc_clk', 50)
        assert not tb.req(), "PDE disabled should never raise req"

    elif test_type == "req_then_active":
        # Get into REQ state, then activity arrives before grant.
        await tb.go_idle()
        await tb.wait_clocks('mc_clk', 15)
        assert tb.req()
        await tb.go_active()
        await tb.wait_clocks('mc_clk', 2)
        assert not tb.req(), "req should clear when activity arrives"
        assert tb.cke() == 1

    elif test_type == "sref_entry":
        # E: enable_sref_i takes priority over enable_pde_i. After idle
        # threshold, pdn_kind_o should be 1 (SR). After grant, sref_active_o
        # should be high while CKE is low.
        tb.dut.enable_sref_i.value = 1
        tb.dut.enable_pde_i.value  = 1
        await tb.go_idle()
        await tb.wait_clocks('mc_clk', 15)
        assert tb.req(), "req should rise after idle threshold"
        assert tb.kind() == 1, f"SR should have priority, got kind={tb.kind()}"
        await tb.grant()
        await tb.wait_clocks('mc_clk', 2)
        assert tb.cke() == 0, "CKE should drop after grant"
        assert tb.sref_active(), "sref_active should be high in SR"
        # Activity → wake
        await tb.go_active()
        await tb.wait_clocks('mc_clk', 2)
        assert tb.cke() == 1
        assert not tb.sref_active()

    elif test_type == "pde_only_when_sref_off":
        # E: enable_sref_i low + enable_pde_i high → PDE path (kind=0).
        tb.dut.enable_sref_i.value = 0
        tb.dut.enable_pde_i.value  = 1
        await tb.go_idle()
        await tb.wait_clocks('mc_clk', 15)
        assert tb.req()
        assert tb.kind() == 0, f"PDE expected when sref disabled, got {tb.kind()}"
        await tb.grant()
        await tb.wait_clocks('mc_clk', 2)
        assert tb.cke() == 0
        assert not tb.sref_active(), "sref_active should stay low in PDE path"

    elif test_type == "sref_alone":
        # E: enable_sref_i high, enable_pde_i low → SR should still work.
        tb.dut.enable_sref_i.value = 1
        tb.dut.enable_pde_i.value  = 0
        await tb.go_idle()
        await tb.wait_clocks('mc_clk', 15)
        assert tb.req(), "SR-only path should still arm + request"
        assert tb.kind() == 1

    elif test_type == "grant_no_reissue":
        # REGRESSION GUARD for the strict-flop strobe re-issue pattern
        # (see commit 66f32c7f / scheduler S_DONE bug). After a single
        # grant takes us to S_ASLEEP, pdn_req_o must drop and stay
        # dropped (until activity returns and idle re-arms).
        await tb.setup(idle_threshold=10)
        await tb.go_idle()
        await tb.wait_clocks('mc_clk', 15)
        assert tb.req(), "pdn_req should rise after idle threshold"
        await tb.grant()
        # Now in S_ASLEEP — observe over 50 cycles. While idle is
        # asserted, pdn_req must NOT re-fire (S_ASLEEP holds CKE low;
        # only an idle drop should wake).
        req_asserts = 0
        for _ in range(50):
            await tb.wait_clocks('mc_clk', 1)
            if tb.req():
                req_asserts += 1
        assert req_asserts == 0, \
            f"pdn_req_o re-asserted {req_asserts} times after single " \
            f"grant — strobe re-fire race regressed"
        assert tb.cke() == 0, "CKE should remain low in S_ASLEEP"

    elif test_type == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '12345')))
        test_level = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 50, "FUNC": 200, "FULL": 1000}.get(test_level, 200)
        tb.dut.enable_pde_i.value = 1

        for _ in range(n):
            if rng.random() < 0.5:
                await tb.go_idle()
            else:
                await tb.go_active()
            if rng.random() < 0.1:
                tb.dut.enable_pde_i.value = rng.randint(0, 1)
            if tb.req() and rng.random() < 0.5:
                tb.dut.pdn_grant_i.value = 1
                await tb.wait_clocks('mc_clk', 1)
                tb.dut.pdn_grant_i.value = 0
            await tb.wait_clocks('mc_clk', rng.randint(1, 15))
        tb.dut.enable_pde_i.value = 1

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await tb.wait_clocks('mc_clk', 3)


_GATE = [("smoke",), ("early_wake",)]
_FUNC = _GATE + [("disable_pde",), ("req_then_active",),
                 ("sref_entry",), ("pde_only_when_sref_off",),
                 ("sref_alone",),
                 ("grant_no_reissue",),  # strict-flop strobe race guard
                 ("random_soak",)]
_FULL = _FUNC

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_powerdown_ctrl(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "powerdown_ctrl"
    test_name = f"test_powerdown_ctrl_{test_type}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/fub/powerdown_ctrl.f")
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
    parameters = {"NUM_RANKS": "1", "CS_WIDTH": "1"}

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
        testcase="cocotb_test_powerdown_ctrl",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")

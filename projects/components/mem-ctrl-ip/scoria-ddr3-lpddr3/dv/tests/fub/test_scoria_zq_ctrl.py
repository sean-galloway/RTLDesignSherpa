# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `scoria_zq_ctrl` -- periodic ZQCS as maintenance traffic.

No pumice equivalent exists: DDR2 has no ZQ command at all, so this module has
never executed. Written from the module's contract rather than ported.

The properties worth testing are the ones a plausible implementation gets
wrong:

  interval 0 means DISABLED, not "as fast as possible". A reload-to-zero would
  request every cycle and saturate the arbiter with calibrations.

  the request does NOT withdraw under demand_i. That is deliberate -- a
  self-withdrawing request starves silently, which is the whole reason
  obs_overdue_o exists -- so a test that only checks "it eventually issues"
  would pass an implementation that quietly gives up under load.

  obs_overdue_o must latch when the interval has expired and no grant comes,
  and must NOT fire merely because the countdown is still running.

  tZQCS is held AFTER the grant, and the interval reloads only when the hold
  expires. Reloading at grant time would let the next request arrive inside
  the calibration window.
"""

import os
import random

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path


class ZqTB(TBBase):
    async def setup(self, *, enable=1, interval=64, t_zqcs=8, demand=0):
        await self.start_clock('mc_clk', 10, 'ns')
        self.dut.enable_i.value = enable
        self.dut.t_zqcs_interval_i.value = interval
        self.dut.t_zqcs_i.value = t_zqcs
        self.dut.demand_i.value = demand
        self.dut.zq_grant_i.value = 0
        await self.assert_reset()
        await self.wait_clocks('mc_clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('mc_clk', 3)

    async def assert_reset(self):
        self.dut.mc_rst_n.value = 0

    async def deassert_reset(self):
        self.dut.mc_rst_n.value = 1

    async def setup_clocks_and_reset(self):
        await self.setup()

    def obs(self):
        return {
            'req':      int(self.dut.zq_req_o.value),
            'busy':     int(self.dut.obs_busy_o.value),
            'total':    int(self.dut.obs_zqcs_total_o.value),
            'cnt':      int(self.dut.obs_interval_cnt_o.value),
            'overdue':  int(self.dut.obs_overdue_o.value),
        }

    async def wait_req(self, limit=4000):
        """Cycles until zq_req_o rises, or None."""
        for i in range(limit):
            await RisingEdge(self.dut.mc_clk)
            if int(self.dut.zq_req_o.value):
                return i
        return None

    async def grant(self):
        self.dut.zq_grant_i.value = 1
        await RisingEdge(self.dut.mc_clk)
        self.dut.zq_grant_i.value = 0


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_scoria_zq_ctrl(dut):
    tt = os.environ.get("TEST_TYPE", "smoke")
    tb = ZqTB(dut)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    if tt == "smoke":
        await tb.setup(interval=32, t_zqcs=8)
        n = await tb.wait_req(600)
        chk(n is not None, "zq_req_o never rose with ZQ enabled")
        t0 = tb.obs()['total']
        await tb.grant()
        await tb.wait_clocks('mc_clk', 3)
        chk(tb.obs()['busy'] == 1, "obs_busy_o not set after a grant")
        chk(tb.obs()['total'] == t0 + 1,
            f"total {tb.obs()['total']} != {t0 + 1} after one grant")

    elif tt == "interval_zero_disabled":
        # 0 must mean DISABLED. A reload-to-zero requests every cycle.
        await tb.setup(interval=0, t_zqcs=8)
        n = await tb.wait_req(1500)
        chk(n is None, f"interval=0 requested after {n} cycles -- 0 must disable")
        chk(tb.obs()['total'] == 0, "interval=0 issued a calibration")
        chk(tb.obs()['overdue'] == 0, "interval=0 reported overdue")

    elif tt == "enable_low_disabled":
        await tb.setup(enable=0, interval=16)
        n = await tb.wait_req(1000)
        chk(n is None, f"enable=0 requested after {n} cycles")
        chk(tb.obs()['total'] == 0, "enable=0 issued a calibration")

    elif tt == "request_does_not_withdraw_under_demand":
        # The deliberate behaviour. A self-withdrawing request starves in
        # silence, which is exactly what obs_overdue_o exists to expose.
        await tb.setup(interval=16, t_zqcs=8, demand=0)
        chk(await tb.wait_req(400) is not None, "no request to test withdrawal")
        dut.demand_i.value = 1
        held = True
        for _ in range(200):
            await RisingEdge(dut.mc_clk)
            if not int(dut.zq_req_o.value):
                held = False
                break
        chk(held, "zq_req_o WITHDREW under demand_i -- it must hold and rely "
                  "on obs_overdue_o to report the starvation")
        chk(tb.obs()['overdue'] == 1,
            "obs_overdue_o did not latch while starved under demand")

    elif tt == "overdue_needs_demand_and_expiry":
        # Must NOT fire merely because the countdown is running.
        await tb.setup(interval=800, t_zqcs=8, demand=1)
        await tb.wait_clocks('mc_clk', 50)
        chk(tb.obs()['req'] == 0, "requested before the interval expired")
        chk(tb.obs()['overdue'] == 0,
            "obs_overdue_o fired while the interval was still counting")

    elif tt == "hold_then_reload":
        # tZQCS is held AFTER the grant, and the interval reloads only when the
        # hold expires -- reloading at grant time lets the next request land
        # inside the calibration window.
        await tb.setup(interval=24, t_zqcs=40)
        chk(await tb.wait_req(400) is not None, "no first request")
        await tb.grant()
        busy_cycles = 0
        for _ in range(400):
            await RisingEdge(dut.mc_clk)
            if int(dut.obs_busy_o.value):
                busy_cycles += 1
            elif busy_cycles:
                break
            chk(not (int(dut.zq_req_o.value) and int(dut.obs_busy_o.value)),
                "requested again while still inside the tZQCS hold")
        chk(busy_cycles >= 35,
            f"held busy {busy_cycles} cycles, expected ~40 (t_zqcs)")

    elif tt == "repeats":
        # Several calibrations, so a one-shot FSM is caught.
        await tb.setup(interval=20, t_zqcs=6)
        for i in range(1, 5):
            chk(await tb.wait_req(500) is not None, f"no request #{i}")
            await tb.grant()
            await tb.wait_clocks('mc_clk', 20)
            got = tb.obs()['total']
            chk(got == i, f"after {i} grants total={got}")

    elif tt == "disable_midflight":
        # Clearing enable while requesting must park it, not wedge it.
        await tb.setup(interval=16, t_zqcs=8)
        chk(await tb.wait_req(400) is not None, "no request before disable")
        dut.enable_i.value = 0
        await tb.wait_clocks('mc_clk', 20)
        chk(tb.obs()['req'] == 0, "still requesting after enable cleared")
        dut.enable_i.value = 1
        chk(await tb.wait_req(600) is not None,
            "never requested again after re-enable -- the FSM wedged")

    elif tt == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '7')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 40, "FUNC": 150, "FULL": 600}.get(lvl, 150)
        await tb.setup(interval=12, t_zqcs=5, demand=1)
        for _ in range(n):
            dut.demand_i.value = rng.randint(0, 1)
            if rng.random() < 0.3:
                await tb.grant()
            await tb.wait_clocks('mc_clk', rng.randint(1, 6))
            o = tb.obs()
            chk(not (o['busy'] and o['req']),
                "busy and req asserted together -- a request inside tZQCS")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('mc_clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["smoke", "interval_zero_disabled", "enable_low_disabled"]
_FUNC = _GATE + ["request_does_not_withdraw_under_demand",
                 "overdue_needs_demand_and_expiry", "hold_then_reload",
                 "repeats", "disable_midflight", "random_soak"]
_FULL = _FUNC
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_scoria_zq_ctrl(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "scoria_zq_ctrl"
    test_name = f"test_scoria_zq_ctrl_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/"
                       "rtl/filelists/fub/scoria_zq_ctrl.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_scoria_zq_ctrl",
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")

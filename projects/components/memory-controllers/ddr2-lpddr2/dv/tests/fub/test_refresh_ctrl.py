# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Unit-test runner for `refresh_ctrl`. Verifies tREFI countdown,
refresh_req assertion, grant decrement, and saturating pending counter.
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

from tbclasses.trackers import RefreshTracker  # noqa: E402


class RefTB(TBBase):
    CLK = 10

    async def setup(self, t_refi: int = 10, refresh_burst: int = 1,
                    refpb_mode: int = 0):
        self.dut.t_refi_i.value         = t_refi
        self.dut.refresh_burst_i.value  = refresh_burst
        self.dut.refpb_mode_i.value     = refpb_mode
        self.dut.enable_i.value         = 0
        self.dut.refresh_grant_i.value  = 0
        await self.start_clock('mc_clk', freq=self.CLK, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    async def enable(self):
        self.dut.enable_i.value = 1

    async def grant_one(self):
        self.dut.refresh_grant_i.value = 1
        await RisingEdge(self.dut.mc_clk)
        await Timer(1, units='ps')
        self.dut.refresh_grant_i.value = 0

    def req(self) -> bool:
        return bool(int(self.dut.refresh_req_o.value))

    def pending(self) -> int:
        return int(self.dut.pending_refreshes_o.value)

    def drain_active(self) -> bool:
        return bool(int(self.dut.refresh_drain_active_o.value))

    def refresh_bank(self) -> int:
        return int(self.dut.refresh_bank_o.value)

    def refresh_kind(self) -> int:
        return int(self.dut.refresh_kind_o.value)


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_refresh_ctrl(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    tb = RefTB(dut)
    # Tracker auto-dumps <sim_build>/refr.out at end of sim.
    # The DUT lacks refresh_grant_o (that's the scheduler's output);
    # disable that signal to suppress missing-signal warnings.
    refr_tracker = RefreshTracker(dut, refresh_grant_signal=None)
    cocotb.start_soon(refr_tracker.run())
    await tb.setup(t_refi=10)

    if test_type == "smoke":
        # Before enable: no req
        await tb.wait_clocks('mc_clk', 20)
        assert not tb.req()
        # Enable and wait for tREFI expiry
        await tb.enable()
        await tb.wait_clocks('mc_clk', 20)
        assert tb.req(), "req should fire after tREFI expiry"
        assert tb.pending() >= 1

    elif test_type == "grant_decrements":
        await tb.enable()
        # Wait for first req
        for _ in range(40):
            await tb.wait_clocks('mc_clk', 1)
            if tb.req():
                break
        assert tb.req()
        # Grant — pending should decrement
        await tb.grant_one()
        await tb.wait_clocks('mc_clk', 2)
        assert tb.pending() == 0
        assert not tb.req()

    elif test_type == "multiple_pending":
        await tb.enable()
        # Don't grant; let pending accumulate
        await tb.wait_clocks('mc_clk', 50)
        # Should have ~5 pending (50 / 11 ≈ 4-5)
        assert tb.pending() >= 3, f"pending = {tb.pending()}"
        assert tb.req()

    elif test_type == "saturating":
        # Very short tREFI; let pending fully saturate at 8.
        tb.dut.t_refi_i.value = 2
        await tb.enable()
        await tb.wait_clocks('mc_clk', 200)
        assert tb.pending() == 8, f"saturating: pending = {tb.pending()}"

    elif test_type == "drain":
        await tb.enable()
        # Accumulate several pending
        await tb.wait_clocks('mc_clk', 60)
        initial = tb.pending()
        assert initial >= 2
        # Grant repeatedly; each grant decrements
        for _ in range(initial):
            await tb.grant_one()
            await tb.wait_clocks('mc_clk', 1)
        # All drained eventually
        # (more grants may have to fire as new pending tick in)
        # Just check pending dropped from initial
        assert tb.pending() < initial

    elif test_type == "drain_burst":
        # D: drain mode — drain_active should be high whenever there are
        # pending refreshes AND a burst quota is loaded. It stays high
        # across consecutive bursts (scheduler keeps granting REF), and
        # only drops when the full pending pool is exhausted.
        await tb.setup(t_refi=8, refresh_burst=4)
        await tb.enable()
        # Accumulate exactly enough pending for one burst.
        await tb.wait_clocks('mc_clk', 80)
        # Stop tREFI from re-arming so we can fully drain.
        tb.dut.enable_i.value = 0
        await tb.wait_clocks('mc_clk', 2)
        initial = tb.pending()
        assert initial >= 4, f"expected >=4 pending, got {initial}"
        assert tb.drain_active(), \
            "drain should be active while quota loaded + pending>0"
        # Grant `initial` times — drain stays high until last grant.
        for i in range(initial - 1):
            await tb.grant_one()
            await tb.wait_clocks('mc_clk', 2)
            assert tb.drain_active(), \
                f"drain should stay high while pending>0 (i={i}, " \
                f"pending={tb.pending()})"
        # Final grant — pending hits 0, drain drops.
        await tb.grant_one()
        await tb.wait_clocks('mc_clk', 3)
        assert not tb.drain_active(), \
            f"drain should clear after all pending drained " \
            f"(pending={tb.pending()})"

    elif test_type == "refpb_rotor":
        # D: REFpb mode — bank rotor walks 0..7 across grants.
        await tb.setup(t_refi=5, refpb_mode=1)
        await tb.enable()
        await tb.wait_clocks('mc_clk', 80)  # accumulate plenty
        assert tb.refresh_kind() == 1, "REFpb kind should be 1"
        banks_seen = []
        for _ in range(8):
            # If pending hits zero, accumulate more
            if tb.pending() == 0:
                await tb.wait_clocks('mc_clk', 20)
            banks_seen.append(tb.refresh_bank())
            await tb.grant_one()
            await tb.wait_clocks('mc_clk', 2)
        # Expect 0,1,2,3,4,5,6,7 (in order) across 8 grants.
        assert banks_seen == list(range(8)), \
            f"REFpb rotor sequence wrong: {banks_seen}"

    elif test_type == "refab_no_rotation":
        # D: REFab mode — bank stays at 0 across grants.
        await tb.setup(t_refi=5, refpb_mode=0)
        await tb.enable()
        await tb.wait_clocks('mc_clk', 80)
        assert tb.refresh_kind() == 0, "REFab kind should be 0"
        for _ in range(4):
            if tb.pending() == 0:
                await tb.wait_clocks('mc_clk', 20)
            assert tb.refresh_bank() == 0, \
                f"REFab bank should stay 0, got {tb.refresh_bank()}"
            await tb.grant_one()
            await tb.wait_clocks('mc_clk', 2)

    elif test_type == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '12345')))
        test_level = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n_grants = {"GATE": 50, "FUNC": 300, "FULL": 1500}.get(test_level, 300)

        await tb.enable()
        grants_done  = 0
        max_pending  = 0
        for _ in range(n_grants):
            tb.dut.t_refi_i.value = rng.randint(5, 30)
            await tb.wait_clocks('mc_clk', rng.randint(3, 25))
            max_pending = max(max_pending, tb.pending())
            if tb.req() and rng.random() < 0.85:
                await tb.grant_one()
                grants_done += 1
        assert max_pending <= 8, f"JEDEC violation: max_pending={max_pending}"
        assert grants_done >= n_grants // 3

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await tb.wait_clocks('mc_clk', 3)


_GATE = [("smoke",), ("grant_decrements",)]
_FUNC = _GATE + [("multiple_pending",), ("saturating",), ("drain",),
                 ("drain_burst",), ("refpb_rotor",), ("refab_no_rotation",),
                 ("random_soak",)]
_FULL = _FUNC

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", [t[0] for t in _PARAMS],
                         ids=[t[0] for t in _PARAMS])
def test_refresh_ctrl(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "refresh_ctrl"
    test_name = f"test_refresh_ctrl_{test_type}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/fub/refresh_ctrl.f")
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
        testcase="cocotb_test_refresh_ctrl",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")

# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `scoria_refresh_ctrl` -- tREFI, postpone/pullin, REFpb rotor.

Ported in shape from pumice's test_refresh_ctrl, but the REFpb rotor gets
cases pumice's does not, because the rotor is a MIRROR of state inside the
device and a mirror can desynchronise silently.

The rotor exists because REFpb carries NO bank address (JESD209-2 6.6 /
JESD209-3C): the device owns a fixed sequential counter and the controller must
predict which bank the next REFpb will hit, so it can precharge that bank and
only that bank. Get the mirror wrong and the controller precharges the wrong
bank ahead of each refresh -- which presents as data loss in banks nobody
touched, not as a refresh error.

The properties that follow from that, and which this tests:

  the rotor advances ONLY on a granted REFpb (grant_was_pb_i), not on any
  grant. Advancing on a REFab grant would shift the mirror by one per REFab
  and the prediction would be wrong from then on.

  it HOLDS across REFab mode rather than resetting. The device's counter
  persists through mode changes; clearing ours on a mode switch desynchronises
  it exactly when a system switches REFab -> REFpb at runtime.

  it wraps at NUM_BANKS-1, and a wrap that lands anywhere else walks the
  prediction off the end of the bank array.
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

NUM_BANKS = 8


class RefTB(TBBase):
    async def setup(self, *, refi=40, trefi_pb=0, burst=1, refpb=0,
                    enable=1, postpone=0, pullin=0, demand=0):
        await self.start_clock('mc_clk', 10, 'ns')
        d = self.dut
        d.t_refi_i.value = refi
        d.trefi_pb_i.value = trefi_pb
        d.refresh_burst_i.value = burst
        d.refpb_mode_i.value = refpb
        d.enable_i.value = enable
        d.refi_reload_i.value = 0
        d.postpone_limit_i.value = postpone
        d.pullin_limit_i.value = pullin
        d.demand_i.value = demand
        d.refresh_grant_i.value = 0
        d.grant_was_pb_i.value = 0
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
        d = self.dut
        return {
            'req':     int(d.refresh_req_o.value),
            'kind':    int(d.refresh_kind_o.value),
            'bank':    int(d.refresh_bank_o.value),
            'rotor':   int(d.obs_bank_rotor_o.value),
            'pending': int(d.pending_refreshes_o.value),
            'drain':   int(d.refresh_drain_active_o.value),
            'grants':  int(d.obs_grants_total_o.value),
            'credit':  int(d.obs_pullin_credit_o.value),
        }

    async def wait_req(self, limit=2000):
        for i in range(limit):
            await RisingEdge(self.dut.mc_clk)
            if int(self.dut.refresh_req_o.value):
                return i
        return None

    async def grant(self, *, was_pb=0, settle=3):
        """ONE-CYCLE grant pulse, then let the registered outputs settle.

        The pulse width is the CONTRACT, not a convenience: the arbiter drives
        refresh_grant_o as `w_fire_out && r_grant`, one cycle. And the accept
        term here is combinational -- `refresh_grant_i && (r_pending > 0)` --
        so the counter increments on EVERY cycle the grant is held.

        Both wrong shapes were tried and both produced nonsense that looked
        like RTL bugs:

          pulse 1 cycle, read immediately  -> grants 0, "the grant was ignored"
          hold until the counter moves     -> grants 3 and the rotor stepping
                                              by 3, sequence [0,3,6,1,4,7,2,5]

        The second is the instructive one: holding a single-cycle handshake
        multiplies it, and a rotor advancing 3 per refresh would desynchronise
        the mirror against the device immediately. The bug was in the
        testbench, but the failure mode it imitated is real.
        """
        self.dut.grant_was_pb_i.value = was_pb
        self.dut.refresh_grant_i.value = 1
        await RisingEdge(self.dut.mc_clk)
        self.dut.refresh_grant_i.value = 0
        self.dut.grant_was_pb_i.value = 0
        # Every observation port is Q of a flop; read too early and the
        # counters are pre-grant.
        for _ in range(settle):
            await RisingEdge(self.dut.mc_clk)


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_scoria_refresh_ctrl(dut):
    tt = os.environ.get("TEST_TYPE", "smoke")
    tb = RefTB(dut)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    if tt == "smoke":
        await tb.setup(refi=30)
        chk(await tb.wait_req(400) is not None, "no refresh request at tREFI")
        g0 = tb.obs()['grants']
        await tb.grant()
        chk(tb.obs()['grants'] == g0 + 1,
            f"grants {tb.obs()['grants']} != {g0 + 1}")

    elif tt == "disabled_never_requests":
        await tb.setup(refi=20, enable=0)
        n = await tb.wait_req(1200)
        chk(n is None, f"requested at cycle {n} with enable low")

    elif tt == "refab_kind_and_bank":
        await tb.setup(refi=25, refpb=0)
        chk(await tb.wait_req(400) is not None, "no request")
        o = tb.obs()
        chk(o['kind'] == 0, f"REFab mode reported kind {o['kind']}, expected 0")
        chk(o['bank'] == 0,
            f"REFab reported bank {o['bank']}; it must stay 0 -- REFab has no "
            f"bank and a nonzero value would make the arbiter precharge one")

    elif tt == "refpb_rotor_advances_only_on_pb_grant":
        # The core rotor property. A REFab grant must NOT move the mirror.
        await tb.setup(refi=20, refpb=1)
        chk(await tb.wait_req(400) is not None, "no request in REFpb mode")
        start = tb.obs()['rotor']
        await tb.grant(was_pb=0)              # granted command was REFab
        after_ab = tb.obs()['rotor']
        chk(after_ab == start,
            f"rotor moved {start} -> {after_ab} on a grant whose wire command "
            f"was NOT a REFpb. The device's counter only advances on REFpb, so "
            f"the mirror is now permanently out of step.")
        chk(await tb.wait_req(600) is not None, "no second request")
        await tb.grant(was_pb=1)
        after_pb = tb.obs()['rotor']
        chk(after_pb == (start + 1) % NUM_BANKS,
            f"rotor {start} -> {after_pb} on a REFpb grant, expected "
            f"{(start + 1) % NUM_BANKS}")

    elif tt == "refpb_rotor_wraps_at_num_banks":
        await tb.setup(refi=14, refpb=1)
        seen = []
        for _ in range(NUM_BANKS + 2):
            if await tb.wait_req(600) is None:
                break
            seen.append(tb.obs()['rotor'])
            await tb.grant(was_pb=1)
        chk(len(seen) >= NUM_BANKS + 1,
            f"only {len(seen)} REFpb grants observed, need > {NUM_BANKS}")
        if len(seen) >= NUM_BANKS + 1:
            chk(seen[:NUM_BANKS] == list(range(NUM_BANKS)),
                f"rotor sequence {seen[:NUM_BANKS]} != 0..{NUM_BANKS - 1}")
            chk(seen[NUM_BANKS] == 0,
                f"rotor wrapped to {seen[NUM_BANKS]}, expected 0 -- a wrap "
                f"anywhere else walks the prediction off the bank array")

    elif tt == "refpb_rotor_holds_across_mode_change":
        # The device's counter persists through a mode change. Clearing ours
        # desynchronises the mirror exactly when a system switches at runtime.
        await tb.setup(refi=16, refpb=1)
        for _ in range(3):
            if await tb.wait_req(500) is None:
                break
            await tb.grant(was_pb=1)
        mid = tb.obs()['rotor']
        chk(mid != 0, f"rotor still 0 after 3 REFpb grants -- not advancing")
        dut.refpb_mode_i.value = 0            # switch to REFab
        await tb.wait_clocks('mc_clk', 30)
        chk(tb.obs()['rotor'] == mid,
            f"rotor {mid} -> {tb.obs()['rotor']} on switching to REFab mode. "
            f"It must HOLD: the device's counter does not reset, so clearing "
            f"the mirror desynchronises it.")
        dut.refpb_mode_i.value = 1            # and back
        await tb.wait_clocks('mc_clk', 10)
        chk(tb.obs()['rotor'] == mid,
            f"rotor changed on switching back to REFpb: {tb.obs()['rotor']} "
            f"!= {mid}")

    elif tt == "postpone_withholds_under_demand":
        # postpone_limit defers the request while the scheduler has work.
        await tb.setup(refi=20, postpone=4, demand=1)
        n_with = await tb.wait_req(1500)
        await tb.setup(refi=20, postpone=0, demand=1)
        n_without = await tb.wait_req(1500)
        chk(n_with is not None and n_without is not None,
            "no request in one of the postpone configurations")
        if n_with is not None and n_without is not None:
            chk(n_with > n_without,
                f"postpone=4 requested at {n_with}, postpone=0 at "
                f"{n_without} -- postpone did not defer under demand")

    elif tt == "pending_accumulates_and_drains":
        await tb.setup(refi=12, burst=4, postpone=4, demand=1)
        await tb.wait_clocks('mc_clk', 400)
        p = tb.obs()['pending']
        chk(p > 0, "nothing pending after 400 cycles under demand with postpone")
        chk(p <= 8, f"pending {p} exceeds the JEDEC 8-postponed ceiling")
        dut.demand_i.value = 0
        drained = False
        for _ in range(900):
            await RisingEdge(dut.mc_clk)
            if int(dut.refresh_req_o.value):
                await tb.grant()
            if int(dut.pending_refreshes_o.value) == 0:
                drained = True
                break
        chk(drained, f"backlog never drained; pending "
                     f"{int(dut.pending_refreshes_o.value)}")

    elif tt == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '9')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 200, "FUNC": 800, "FULL": 3000}.get(lvl, 800)
        await tb.setup(refi=14, refpb=1, postpone=3, pullin=2, demand=1)
        for _ in range(n):
            dut.demand_i.value = rng.randint(0, 1)
            if int(dut.refresh_req_o.value) and rng.random() < 0.6:
                await tb.grant(was_pb=rng.randint(0, 1))
            else:
                await RisingEdge(dut.mc_clk)
            o = tb.obs()
            chk(o['rotor'] < NUM_BANKS,
                f"rotor {o['rotor']} out of range under soak")
            chk(o['pending'] <= 8,
                f"pending {o['pending']} exceeds the JEDEC ceiling under soak")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('mc_clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["smoke", "disabled_never_requests", "refab_kind_and_bank"]
_FUNC = _GATE + ["refpb_rotor_advances_only_on_pb_grant",
                 "refpb_rotor_wraps_at_num_banks",
                 "refpb_rotor_holds_across_mode_change",
                 "postpone_withholds_under_demand",
                 "pending_accumulates_and_drains", "random_soak"]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_scoria_refresh_ctrl(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "scoria_refresh_ctrl"
    test_name = f"test_scoria_refresh_ctrl_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/"
                       "rtl/filelists/fub/scoria_refresh_ctrl.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_scoria_refresh_ctrl",
        sim_build=sim_build, simulator="verilator",
        parameters={"NUM_BANKS": str(NUM_BANKS)},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")

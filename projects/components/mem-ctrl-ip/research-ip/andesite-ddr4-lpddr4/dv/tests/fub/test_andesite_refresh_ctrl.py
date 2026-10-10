# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `andesite_refresh_ctrl` -- tREFI, postpone/pullin, REFpb rotor.

Carried from scoria's suite; the andesite delta adds the DDR4
fine-granularity refresh (FGR) cases: the factor divides the tREFI reload
1x/2x/4x, the illegal encoding clamps to the 1x row (the kmap FGR select
table -- deliberately not the Mode B 3->2 clamp), tRFC(fgr) selects among
the per-density tRFC CSRs on refresh_trfc_o, the +-8 credit ceiling is
unchanged but scales in time with the interval, and a mid-run factor change
is reload-only (the armed interval completes at the old factor).

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
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path

NUM_BANKS = 8


class RefTB(TBBase):
    async def setup(self, *, refi=40, trefi_pb=0, burst=1, refpb=0,
                    enable=1, postpone=0, pullin=0, demand=0,
                    elastic_en=0, pullin_idle_streak=16,
                    postpone_demand_streak=16,
                    tcr_en=0, trefi_derate=0,
                    fgr_factor=0, t_rfc_1x=30, t_rfc_2x=20, t_rfc_4x=14):
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
        d.elastic_en_i.value = elastic_en
        d.pullin_idle_streak_i.value = pullin_idle_streak
        d.postpone_demand_streak_i.value = postpone_demand_streak
        d.tcr_en_i.value = tcr_en
        d.trefi_derate_i.value = trefi_derate
        d.fgr_factor_i.value = fgr_factor
        d.t_rfc_1x_i.value = t_rfc_1x
        d.t_rfc_2x_i.value = t_rfc_2x
        d.t_rfc_4x_i.value = t_rfc_4x
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
            'postpone_events': int(d.obs_postpone_events_o.value),
            'pullin_events':   int(d.obs_pullin_events_o.value),
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

    async def run_and_capture(self, *, refi=40, cycles=200, **setup_kwargs):
        """Run `cycles` loop iterations, grant every request, and return the
        request assertion times (ns, relative to the first request) and the
        obs_refi_cnt_o reload values.

        Two runs with the same effective interval produce bit-identical
        relative request sequences and `reloads`, which is how the TCR
        disabled and illegal-clamp cases are checked.
        """
        await self.setup(refi=refi, **setup_kwargs)
        d = self.dut
        req_ns = []
        reloads = []
        prev_refi = int(d.obs_refi_cnt_o.value)
        for _ in range(cycles):
            await RisingEdge(d.mc_clk)
            cur_refi = int(d.obs_refi_cnt_o.value)
            if cur_refi > prev_refi:
                reloads.append(cur_refi)
            prev_refi = cur_refi
            if int(d.refresh_req_o.value):
                req_ns.append(get_sim_time('ns'))
                await self.grant()
        if req_ns:
            t0 = req_ns[0]
            req_ns = [t - t0 for t in req_ns]
        return req_ns, reloads


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_andesite_refresh_ctrl(dut):
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

    elif tt == "elastic_pullin_idle_streak":
        # Mode A: after pullin_idle_streak idle cycles a pending-based request
        # fires.  Use pullin=0 so the only path that can raise the 8th-cycle
        # request is the pending backlog, not a pull-in grant.
        await tb.setup(refi=12, pullin=0, elastic_en=1,
                       pullin_idle_streak=8, demand=1)
        # Clear the first backlog so we start the idle window with pending == 0.
        chk(await tb.wait_req(400) is not None, "no initial refresh request")
        await tb.grant()
        # refi=12 leaves r_refi_cnt == 8 after grant()'s settle window, so the
        # next expiry lands at the 8-cycle idle confirmation and produces a
        # pending-based request rather than a pull-in.
        dut.demand_i.value = 0
        # No request for the first 7 idle cycles (no expiry, no pull-in path).
        for i in range(7):
            await RisingEdge(dut.mc_clk)
            chk(not int(dut.refresh_req_o.value),
                f"request fired at idle cycle {i + 1} (< 8)")
        # 8th idle cycle: tREFI expires, request fires from pending, not pull-in.
        await RisingEdge(dut.mc_clk)
        chk(int(dut.refresh_req_o.value),
            "request did not fire at 8th idle cycle")
        chk(int(dut.pending_refreshes_o.value) > 0,
            "request fired but pending is 0 (would be a pull-in grant)")
        chk(tb.obs()['pullin_events'] == 0,
            f"pull-in events {tb.obs()['pullin_events']} != 0 with pullin=0")

    elif tt == "elastic_postpone_sustained_demand":
        # Mode A: sporadic demand uses strict timing; sustained demand postpones.
        await tb.setup(refi=16, postpone=3, elastic_en=1,
                       postpone_demand_streak=16, demand=1)
        # Phase 1: sporadic demand (4 on / 4 off). Demand streak resets every
        # off period, so requests fire on every tREFI tick and pending stays 0/1.
        grants_before = int(dut.obs_grants_total_o.value)
        max_pending_sporadic = 0
        for cycle in range(128):
            dut.demand_i.value = 1 if (cycle % 8) < 4 else 0
            await RisingEdge(dut.mc_clk)
            p = int(dut.pending_refreshes_o.value)
            if p > max_pending_sporadic:
                max_pending_sporadic = p
            if int(dut.refresh_req_o.value):
                await tb.grant()
        chk(max_pending_sporadic <= 1,
            f"sporadic demand pending peaked at {max_pending_sporadic}, "
            f"expected <= 1")
        chk(int(dut.obs_grants_total_o.value) > grants_before,
            "no grants observed during sporadic demand phase")

        # Phase 2: sustained demand. Do not grant until the postpone branch
        # forces the backlog to exceed the effective postpone limit.
        dut.demand_i.value = 1
        max_pending_sustained = 0
        saw_request = False
        for _ in range(600):
            await RisingEdge(dut.mc_clk)
            p = int(dut.pending_refreshes_o.value)
            if p > max_pending_sustained:
                max_pending_sustained = p
            if int(dut.refresh_req_o.value):
                saw_request = True
                if max_pending_sustained >= 4:
                    break
        chk(max_pending_sustained >= 4,
            f"sustained demand pending only reached {max_pending_sustained}, "
            f"expected >= postpone_limit + 1 = 4")
        chk(saw_request, "request never fired during sustained demand")
        # Each withheld tREFI expiry while pending stayed at or below the
        # postpone limit counts as one event.  With postpone=3 the backlog
        # climbs 1 -> 2 -> 3 before the threshold-crossing tick forces the
        # request, so exactly three postpone events are expected.
        chk(tb.obs()['postpone_events'] == 3,
            f"postpone events {tb.obs()['postpone_events']} != 3")

    elif tt == "elastic_disabled_ignores_thresholds":
        # Mode A disabled: extreme thresholds must not change the smoke timing.
        async def run_baseline_like(elastic_en, pullin_idle_streak,
                                    postpone_demand_streak):
            await tb.setup(refi=30, elastic_en=elastic_en,
                           pullin_idle_streak=pullin_idle_streak,
                           postpone_demand_streak=postpone_demand_streak)
            req_cycles = []
            reloads = []
            prev_refi = int(dut.obs_refi_cnt_o.value)
            for c in range(200):
                await RisingEdge(dut.mc_clk)
                cur_refi = int(dut.obs_refi_cnt_o.value)
                if cur_refi > prev_refi:
                    reloads.append(cur_refi)
                prev_refi = cur_refi
                if int(dut.refresh_req_o.value):
                    req_cycles.append(c)
                    await tb.grant()
                    prev_refi = int(dut.obs_refi_cnt_o.value)
            return req_cycles, reloads

        baseline_req, baseline_reload = await run_baseline_like(0, 16, 16)
        disabled_req, disabled_reload = await run_baseline_like(
            0, 200, 100)
        chk(baseline_req == disabled_req,
            f"request cycles differ with elastic disabled: "
            f"baseline {baseline_req} vs disabled {disabled_req}")
        chk(baseline_reload == disabled_reload,
            f"reload values differ with elastic disabled: "
            f"baseline {baseline_reload} vs disabled {disabled_reload}")

    elif tt == "tcr_derate_intervals":
        # Mode B: tREFI derate scales the reload interval 1x/2x/4x.
        base_refi = 40
        expected = {0: base_refi, 1: base_refi // 2, 2: base_refi // 4}
        for derate, exp_interval in expected.items():
            req_ns, reloads = await tb.run_and_capture(
                refi=base_refi, tcr_en=1, trefi_derate=derate, cycles=300)
            for rv in reloads:
                chk(abs(rv - exp_interval) <= 1,
                    f"derate={derate}: reload {rv} != expected {exp_interval} "
                    f"±1")
            for i in range(1, len(req_ns)):
                spacing = (req_ns[i] - req_ns[i - 1]) // 10
                chk(abs(spacing - exp_interval) <= 1,
                    f"derate={derate}: request spacing {spacing} != expected "
                    f"{exp_interval} ±1")

    elif tt == "tcr_derate_illegal_clamps":
        # Mode B: trefi_derate=3 must clamp to the legal 2x/4x ceiling (=2).
        base_refi = 40
        req2, reloads2 = await tb.run_and_capture(
            refi=base_refi, tcr_en=1, trefi_derate=2, cycles=300)
        req3, reloads3 = await tb.run_and_capture(
            refi=base_refi, tcr_en=1, trefi_derate=3, cycles=300)
        chk(req2 == req3,
            f"derate=2/3 request cycles differ: {req2} vs {req3}")
        chk(reloads2 == reloads3,
            f"derate=2/3 reload sequences differ: {reloads2} vs {reloads3}")

    elif tt == "tcr_derate_small_interval_bounded":
        # Mode B: a very short derated interval must still obey the JEDEC
        # pending ceiling and drain cleanly.
        await tb.setup(refi=8, tcr_en=1, trefi_derate=2)
        max_pending = 0
        for _ in range(100):
            await RisingEdge(dut.mc_clk)
            p = int(dut.pending_refreshes_o.value)
            if p > max_pending:
                max_pending = p
            chk(p <= 8,
                f"pending {p} exceeds JEDEC 8-postponed ceiling")
        chk(max_pending > 0, "pending never grew")
        # Drain with one-cycle grants spaced one cycle apart so we outrun the
        # 2-cycle reload interval; using tb.grant()'s settle window would let
        # expiries arrive faster than grants and the drain would stall.
        drained = False
        grants = 0
        for _ in range(50):
            if int(dut.pending_refreshes_o.value) == 0:
                drained = True
                break
            if int(dut.refresh_req_o.value):
                dut.grant_was_pb_i.value = 0
                dut.refresh_grant_i.value = 1
                await RisingEdge(dut.mc_clk)
                dut.refresh_grant_i.value = 0
                grants += 1
            await RisingEdge(dut.mc_clk)
        chk(drained,
            f"pending did not drain; stuck at "
            f"{int(dut.pending_refreshes_o.value)}")
        chk(grants >= max_pending,
            f"only {grants} grants to drain max pending {max_pending}")

    elif tt == "tcr_disabled_bitidentical":
        # Mode B disabled: the derate input is ignored and timing matches the
        # smoke case exactly.
        req0, reloads0 = await tb.run_and_capture(
            refi=30, tcr_en=0, trefi_derate=0, cycles=250)
        reqx, reloadsx = await tb.run_and_capture(
            refi=30, tcr_en=0, trefi_derate=2, cycles=250)
        chk(req0 == reqx,
            f"request cycles differ with TCR disabled: {req0} vs {reqx}")
        chk(reloads0 == reloadsx,
            f"reload values differ with TCR disabled: {reloads0} vs {reloadsx}")

    elif tt == "fgr_interval_scales_per_factor":
        # DDR4 FGR: the factor divides the tREFI reload 1x/2x/4x (MAS 06
        # fence), exactly the shape the Mode B derate test proves for the
        # derate. Factor encoding 0=1x, 1=2x, 2=4x.
        base_refi = 40
        expected = {0: base_refi, 1: base_refi // 2, 2: base_refi // 4}
        for factor, exp_interval in expected.items():
            req_ns, reloads = await tb.run_and_capture(
                refi=base_refi, fgr_factor=factor, cycles=300)
            for rv in reloads:
                chk(abs(rv - exp_interval) <= 1,
                    f"fgr={factor}: reload {rv} != expected {exp_interval} "
                    f"±1")
            for i in range(1, len(req_ns)):
                spacing = (req_ns[i] - req_ns[i - 1]) // 10
                chk(abs(spacing - exp_interval) <= 1,
                    f"fgr={factor}: request spacing {spacing} != expected "
                    f"{exp_interval} ±1")

    elif tt == "fgr_illegal_factor_clamps":
        # FGR: an illegal factor encoding (3) clamps to the 1x row per the
        # kmap FGR select table -- deliberately NOT the Mode B 3->2 clamp.
        base_refi = 40
        req0, reloads0 = await tb.run_and_capture(
            refi=base_refi, fgr_factor=0, cycles=300)
        req3, reloads3 = await tb.run_and_capture(
            refi=base_refi, fgr_factor=3, cycles=300)
        chk(req0 == req3,
            f"fgr 0/3 request cycles differ: {req0} vs {req3}")
        chk(reloads0 == reloads3,
            f"fgr 0/3 reload sequences differ: {reloads0} vs {reloads3}")
        chk(all(rv == base_refi for rv in reloads3),
            f"fgr=3 reloads are not the 1x row: {reloads3}")

    elif tt == "fgr_trfc_select_per_density":
        # tRFC_active = tRFC(fgr): the factor selects among the per-density
        # tRFC CSRs on refresh_trfc_o; illegal clamps to the 1x CSR.
        await tb.setup(fgr_factor=0, t_rfc_1x=30, t_rfc_2x=20, t_rfc_4x=14)
        for factor, exp in ((0, 30), (1, 20), (2, 14), (3, 30)):
            dut.fgr_factor_i.value = factor
            await RisingEdge(dut.mc_clk)
            got = int(dut.refresh_trfc_o.value)
            chk(got == exp,
                f"fgr={factor}: refresh_trfc_o {got} != tRFC select {exp}")

    elif tt == "fgr_credit_window_scales":
        # The +-8 credit ceiling is unchanged; measured in time the window
        # scales by 1/factor because the interval does. Hold demand so the
        # busy-side postpone path gates the request at pending > postpone_limit.
        async def cycles_to_request(factor):
            await tb.setup(refi=40, fgr_factor=factor, demand=1,
                           postpone=4, enable=1)
            for i in range(2000):
                await RisingEdge(dut.mc_clk)
                if int(dut.refresh_req_o.value):
                    return i
            return None
        c1 = await cycles_to_request(0)
        c2 = await cycles_to_request(1)
        chk(c1 is not None and c2 is not None,
            f"request never asserted: c1={c1} c2={c2}")
        # Five expiries (pending 0->5 crosses postpone_limit=4). The shared
        # setup+pipeline offset K (reset waits + registered request) appears
        # once in each count, so 2*c2 - c1 == K, not 0; K is small (<=6).
        chk(abs(c2 * 2 - c1) <= 6,
            f"credit window did not scale: 1x {c1} cycles, 2x {c2} "
            f"cycles, 2*c2-c1={c2*2-c1}")

    elif tt == "fgr_reload_only_mid_run":
        # Reload-only rule (carried from the Mode B posture): a factor change
        # mid-interval takes effect on the NEXT reload, not the running
        # counter -- the armed interval completes at the old factor.
        await tb.setup(refi=40, fgr_factor=0)
        reloads = []
        prev_refi = int(dut.obs_refi_cnt_o.value)
        flipped = False
        for _ in range(300):
            await RisingEdge(dut.mc_clk)
            cur_refi = int(dut.obs_refi_cnt_o.value)
            if cur_refi > prev_refi:
                reloads.append(cur_refi)
                if not flipped:
                    dut.fgr_factor_i.value = 2   # 4x: next reload must be 10
                    flipped = True
            prev_refi = cur_refi
            if int(dut.refresh_req_o.value):
                await tb.grant()
        chk(flipped, "first reload never happened")
        chk(reloads[0] == 40,
            f"first reload {reloads[0]} != 40 (1x armed at reset)")
        chk(all(rv == 10 for rv in reloads[1:]),
            f"post-change reloads are not the 4x row: {reloads[1:]}")
        # Modes-still-clean: with the factor held at 1x, the elastic/TCR
        # modes behave exactly as the inherited suite proves -- re-run the
        # elastic postpone case shape here with FGR wired but at 1x. The
        # original check asserted presence only (review M-8); it now pins the
        # TCR rate (derate=1 halves tREFI: 30 -> 15, so 250 cycles must
        # produce well more than the plain rate) and the run's determinism
        # (an identical rerun must reproduce the cadence bit-for-bit). An
        # exact cross-mode cadence equality is spec-impossible -- TCR and
        # elastic change the rate by design -- so those are the strongest
        # honest bounds.
        req_fgr1x, _ = await tb.run_and_capture(
            refi=30, fgr_factor=0, tcr_en=1, trefi_derate=1,
            elastic_en=1, demand=1, postpone=2, cycles=250)
        chk(len(req_fgr1x) > 0, "modes-still-clean run never requested")
        chk(len(req_fgr1x) >= 8,
            f"TCR derate=1 must roughly double the rate: only "
            f"{len(req_fgr1x)} requests in 250 cycles at refi=30 (the "
            f"derated interval is ~15 cycles, so >= 8 even with elastic "
            f"postponement slack)")
        req_repeat, _ = await tb.run_and_capture(
            refi=30, fgr_factor=0, tcr_en=1, trefi_derate=1,
            elastic_en=1, demand=1, postpone=2, cycles=250)
        chk(req_fgr1x == req_repeat,
            "an identical modes rerun produced a different request cadence "
            "-- the FGR-1x/modes path is not deterministic")

    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('mc_clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["smoke", "disabled_never_requests", "refab_kind_and_bank"]
_FUNC = _GATE + ["refpb_rotor_advances_only_on_pb_grant",
                 "refpb_rotor_wraps_at_num_banks",
                 "refpb_rotor_holds_across_mode_change",
                 "postpone_withholds_under_demand",
                 "pending_accumulates_and_drains", "random_soak",
                 "elastic_pullin_idle_streak",
                 "elastic_postpone_sustained_demand",
                 "elastic_disabled_ignores_thresholds",
                 "tcr_derate_intervals",
                 "tcr_derate_illegal_clamps",
                 "tcr_derate_small_interval_bounded",
                 "tcr_disabled_bitidentical",
                 "fgr_interval_scales_per_factor",
                 "fgr_illegal_factor_clamps",
                 "fgr_trfc_select_per_density",
                 "fgr_credit_window_scales",
                 "fgr_reload_only_mid_run"]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_andesite_refresh_ctrl(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "andesite_refresh_ctrl"
    test_name = f"test_andesite_refresh_ctrl_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/"
                       "rtl/filelists/fub/andesite_refresh_ctrl.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_refresh_ctrl",
        sim_build=sim_build, simulator="verilator",
        parameters={"NUM_BANKS": str(NUM_BANKS)},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")

# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `scoria_wrlvl_ifc` -- DDR3 write leveling, host-driven.

No pumice equivalent: DDR2 has no write leveling, so this module has never
executed. Written from its contract.

Design decision D2 puts the delay SEARCH in the host, so this module is an
interface: it sequences tWLDQSEN -> tWLMRD -> armed, emits one DQS edge per
host strobe, and reports the sampled prime DQ after tWLO. The properties that
matter are therefore about sequencing and reporting, not about converging.

The four outcomes must stay distinguishable -- never attempted, converged,
timed out, and swept-with-no-flip. That last one is the trap: a host that
sweeps every tap and sees the same answer throughout has NOT converged, and a
"did it finish" check reports it as success.
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

WL_OFF, WL_DQSEN, WL_MRD, WL_READY, WL_WAIT_WLO, WL_TIMEOUT = range(6)


class WlTB(TBBase):
    async def setup(self, *, dqsen=4, mrd=6, mrd_max=0, wlo=5, prime=0):
        await self.start_clock('mc_clk', 10, 'ns')
        self.dut.wrlvl_en_i.value = 0
        self.dut.strobe_i.value = 0
        self.dut.cs_sel_i.value = 0
        self.dut.t_wldqsen_i.value = dqsen
        self.dut.t_wlmrd_i.value = mrd
        self.dut.t_wlmrd_max_i.value = mrd_max
        self.dut.t_wlo_i.value = wlo
        self.dut.t_wloe_i.value = 2
        self.dut.prime_dq_i.value = prime
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
            'state':    int(self.dut.obs_state_o.value),
            'attempts': int(self.dut.obs_attempts_o.value),
            'flips':    int(self.dut.obs_flips_o.value),
            'timeout':  int(self.dut.obs_timeout_o.value),
            'done':     int(self.dut.obs_ever_done_o.value),
            'rvalid':   int(self.dut.result_valid_o.value),
            'result':   int(self.dut.result_o.value),
            'strobe':   int(self.dut.dfi_wrlvl_strobe_o.value),
        }

    async def enter(self):
        self.dut.wrlvl_en_i.value = 1

    async def wait_state(self, want, limit=500):
        for i in range(limit):
            await RisingEdge(self.dut.mc_clk)
            if int(self.dut.obs_state_o.value) == want:
                return i
        return None

    async def pulse_strobe(self):
        self.dut.strobe_i.value = 1
        await RisingEdge(self.dut.mc_clk)
        self.dut.strobe_i.value = 0

    async def strobe_and_settle(self, limit=200):
        """Pulse, then wait for the attempt to COMPLETE.

        obs_state_o is Q of a flop, so it lags r_state by a cycle. A naive
        "pulse then wait for READY" returns immediately on the STALE READY --
        before the FSM has even left it -- and every downstream assertion then
        reads pre-strobe counters. That is what made four of these cases fail
        against correct RTL on the first run.

        So: leave READY first (proving the strobe was taken), then come back.
        """
        before = int(self.dut.obs_attempts_o.value)
        await self.pulse_strobe()
        left = False
        for _ in range(limit):
            await RisingEdge(self.dut.mc_clk)
            if int(self.dut.obs_state_o.value) != WL_READY:
                left = True
                break
        if not left:
            return False
        for _ in range(limit):
            await RisingEdge(self.dut.mc_clk)
            if int(self.dut.obs_state_o.value) == WL_READY:
                return int(self.dut.obs_attempts_o.value) == before + 1
            if int(self.dut.obs_state_o.value) == WL_TIMEOUT:
                return False
        return False


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_scoria_wrlvl_ifc(dut):
    tt = os.environ.get("TEST_TYPE", "smoke")
    tb = WlTB(dut)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    if tt == "smoke_sequence":
        # tWLDQSEN -> tWLMRD -> armed, in that order.
        await tb.setup(dqsen=4, mrd=6, wlo=5)
        chk(tb.obs()['state'] == WL_OFF, "not in WL_OFF before enable")
        await tb.enter()
        chk(await tb.wait_state(WL_DQSEN, 20) is not None, "never reached DQSEN")
        chk(await tb.wait_state(WL_MRD, 40) is not None, "never reached MRD")
        chk(await tb.wait_state(WL_READY, 40) is not None, "never armed")

    elif tt == "strobe_gives_result":
        await tb.setup(dqsen=2, mrd=2, wlo=5, prime=1)
        await tb.enter()
        chk(await tb.wait_state(WL_READY, 60) is not None, "never armed")
        chk(await tb.strobe_and_settle(), "the strobe did not complete")
        o = tb.obs()
        chk(o['attempts'] == 1, f"attempts {o['attempts']} != 1")
        chk(o['rvalid'] == 1, "result_valid not set after tWLO")
        chk(o['result'] == 1, f"result {o['result']} != prime_dq 1")
        chk(o['done'] == 1, "obs_ever_done not set")

    elif tt == "early_strobe_dropped":
        # A strobe before READY must be DROPPED, not queued. A deferred strobe
        # would fire a DQS edge at an unknown time relative to tWLMRD, which is
        # the window the JEDEC sequence exists to establish.
        await tb.setup(dqsen=20, mrd=20, wlo=4)
        await tb.enter()
        await tb.wait_clocks('mc_clk', 3)          # inside DQSEN
        chk(tb.obs()['state'] in (WL_DQSEN, WL_MRD), "not in a wait window")
        # Watch the DQS OUTPUT PIN, not just the counter. The counter alone
        # misses the defect that actually matters: dropping the WL_READY gate
        # on dfi_wrlvl_strobe_o emits a DQS edge during tWLDQSEN, which is the
        # window JESD79-3F requires BEFORE DQS may be driven at all. A
        # mutation doing exactly that passed an attempts-only check.
        dut.strobe_i.value = 1
        edge_seen = False
        for _ in range(8):
            await RisingEdge(dut.mc_clk)
            if int(dut.dfi_wrlvl_strobe_o.value):
                edge_seen = True
        dut.strobe_i.value = 0
        chk(not edge_seen,
            "dfi_wrlvl_strobe_o pulsed during the tWLDQSEN/tWLMRD windows -- "
            "DQS must not be driven before those windows elapse")
        chk(tb.obs()['attempts'] == 0,
            f"early strobe counted: attempts {tb.obs()['attempts']}")
        chk(await tb.wait_state(WL_READY, 200) is not None, "never armed")
        await tb.wait_clocks('mc_clk', 10)
        chk(tb.obs()['attempts'] == 0,
            "early strobe was DEFERRED and fired on arming -- it must be dropped")

    elif tt == "timeout_when_never_strobed":
        await tb.setup(dqsen=2, mrd=2, mrd_max=40, wlo=4)
        await tb.enter()
        chk(await tb.wait_state(WL_TIMEOUT, 300) is not None,
            "never timed out despite t_wlmrd_max armed and no strobe")
        o = tb.obs()
        chk(o['timeout'] == 1, "obs_timeout not set")
        chk(o['done'] == 0, "obs_ever_done set without a completed pass")

    elif tt == "timeout_disabled_by_zero":
        await tb.setup(dqsen=2, mrd=2, mrd_max=0, wlo=4)
        await tb.enter()
        chk(await tb.wait_state(WL_READY, 60) is not None, "never armed")
        await tb.wait_clocks('mc_clk', 400)
        chk(tb.obs()['state'] == WL_READY,
            f"left READY with the timeout disabled: state {tb.obs()['state']}")
        chk(tb.obs()['timeout'] == 0, "timed out with t_wlmrd_max = 0")

    elif tt == "sweep_does_not_spuriously_timeout":
        # THE CASE THAT MATTERS for a host sweep. The host drives many strobes
        # over a long session; the timeout must mean "the host stopped
        # driving", not "the session has lasted a while". A timeout measured
        # from ENTERING leveling rather than from the last strobe fires
        # mid-sweep while the host is actively working.
        await tb.setup(dqsen=2, mrd=2, mrd_max=60, wlo=4)
        await tb.enter()
        chk(await tb.wait_state(WL_READY, 60) is not None, "never armed")
        for i in range(8):
            ok = await tb.strobe_and_settle()
            st = tb.obs()
            chk(ok and st['state'] != WL_TIMEOUT,
                f"TIMED OUT on strobe {i + 1} of 8 while the host was still "
                f"driving -- state {st['state']}, attempts {st['attempts']}. "
                f"The timeout is measured from entering leveling, not from the "
                f"last strobe.")
            if st['state'] == WL_TIMEOUT:
                break
        chk(tb.obs()['attempts'] == 8,
            f"only {tb.obs()['attempts']} of 8 strobes counted")

    elif tt == "flips_counted":
        # obs_flips is how "swept with no flip" is told from "converged".
        await tb.setup(dqsen=2, mrd=2, wlo=4, prime=0)
        await tb.enter()
        chk(await tb.wait_state(WL_READY, 60) is not None, "never armed")
        seq = [0, 0, 1, 1, 0, 1]          # 3 transitions after the first sample
        for v in seq:
            dut.prime_dq_i.value = v
            chk(await tb.strobe_and_settle(), f"strobe with prime={v} stalled")
        chk(tb.obs()['attempts'] == len(seq),
            f"attempts {tb.obs()['attempts']} != {len(seq)}")
        chk(tb.obs()['flips'] == 3,
            f"flips {tb.obs()['flips']} != 3 for prime sequence {seq}")

    elif tt == "no_flip_is_distinguishable":
        # Swept, every answer identical: NOT converged, and it must be visible.
        await tb.setup(dqsen=2, mrd=2, wlo=4, prime=1)
        await tb.enter()
        chk(await tb.wait_state(WL_READY, 60) is not None, "never armed")
        for _ in range(6):
            chk(await tb.strobe_and_settle(), "strobe stalled")
        o = tb.obs()
        chk(o['attempts'] == 6, f"attempts {o['attempts']} != 6")
        chk(o['flips'] == 0, f"flips {o['flips']} != 0 for a constant prime")
        chk(o['done'] == 1, "ever_done not set")
        chk(o['timeout'] == 0, "spurious timeout")

    elif tt == "counters_survive_mode_exit":
        # Leaving leveling must NOT erase the record of the pass just finished
        # -- that is exactly what the host reads afterwards.
        await tb.setup(dqsen=2, mrd=2, wlo=4, prime=1)
        await tb.enter()
        await tb.wait_state(WL_READY, 60)
        chk(await tb.strobe_and_settle(), "strobe did not complete")
        before = tb.obs()
        dut.wrlvl_en_i.value = 0
        await tb.wait_clocks('mc_clk', 10)
        after = tb.obs()
        chk(after['state'] == WL_OFF, "not in WL_OFF after leaving leveling")
        chk(after['attempts'] == before['attempts'],
            f"attempts cleared on mode exit: {before['attempts']} -> "
            f"{after['attempts']}")
        chk(after['done'] == 1, "obs_ever_done cleared on mode exit")
        chk(after['rvalid'] == 0, "result_valid still set after mode exit")

    elif tt == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '11')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 30, "FUNC": 120, "FULL": 400}.get(lvl, 120)
        await tb.setup(dqsen=2, mrd=2, mrd_max=0, wlo=3)
        await tb.enter()
        for _ in range(n):
            dut.prime_dq_i.value = rng.randint(0, 1)
            if rng.random() < 0.4:
                await tb.pulse_strobe()
            if rng.random() < 0.05:
                dut.wrlvl_en_i.value = 0
                await tb.wait_clocks('mc_clk', 2)
                dut.wrlvl_en_i.value = 1
            await tb.wait_clocks('mc_clk', rng.randint(1, 5))
            chk(tb.obs()['state'] <= WL_TIMEOUT,
                f"illegal state {tb.obs()['state']}")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('mc_clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["smoke_sequence", "strobe_gives_result", "timeout_when_never_strobed"]
_FUNC = _GATE + ["early_strobe_dropped", "timeout_disabled_by_zero",
                 "sweep_does_not_spuriously_timeout", "flips_counted",
                 "no_flip_is_distinguishable", "counters_survive_mode_exit",
                 "random_soak"]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_scoria_wrlvl_ifc(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "scoria_wrlvl_ifc"
    test_name = f"test_scoria_wrlvl_ifc_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/"
                       "rtl/filelists/fub/scoria_wrlvl_ifc.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_scoria_wrlvl_ifc",
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")

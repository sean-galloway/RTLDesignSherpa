# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""TASK-006 CA-parity recovery FSM -- unit cases for `andesite_init_sequencer`.

Per andesite_mas ch02_blocks/02_init_sequencer.md: the recovery FSM sits
beside the init FSM and never enters the bank machine. The formatter's
logged alert pulse is the entry event: ALERT_SEEN drops the suspect
command and raises a maintenance-class retract request (request-and-wait,
like the init FSM's own cmd_req/cmd_ack pair); RESENDING holds the
JEDEC-named recovery interval (runtime CSR), then releases the scheduler
to re-issue from its request queue. Telemetry: alerts seen, commands
dropped, commands re-issued -- saturating, cleared only by controller
reset or an explicit firmware clear.
"""

import os
import random

import cocotb
import pytest
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path

CSRS = dict(tinit1=3, tinit3=4, tinit4=2, tmrd=2, tmod=3, tdllk=5, tzqinit=4)


class RecoveryTB(TBBase):
    async def setup(self, *, interval=5):
        await self.start_clock('clk', 10, 'ns')
        d = self.dut
        d.csr_init_trigger.value = 0
        d.csr_memtype.value = 0b010       # MEMTYPE_DDR4
        d.csr_geardown_en.value = 0
        d.csr_parity_en.value = 1
        d.tinit1_csr.value = CSRS['tinit1']
        d.tinit3_csr.value = CSRS['tinit3']
        d.tinit4_csr.value = CSRS['tinit4']
        d.tdllk_csr.value = CSRS['tdllk']
        d.tzqinit_csr.value = CSRS['tzqinit']
        d.tmrd_csr.value = CSRS['tmrd']
        d.tmod_csr.value = CSRS['tmod']
        for i in range(7):
            getattr(d, f"csr_mr{i}_image").value = 0x10 + i
        d.cmd_ack.value = 0
        # TASK-006 recovery interface
        d.parity_alert_i.value = 0
        d.recovery_interval_i.value = interval
        d.csr_telem_clear_i.value = 0
        d.retract_ack_i.value = 0
        await self.assert_reset()
        await self.wait_clocks('clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('clk', 3)

    async def assert_reset(self):
        self.dut.reset_n.value = 0

    async def deassert_reset(self):
        self.dut.reset_n.value = 1

    async def setup_clocks_and_reset(self):
        await self.setup()

    def state(self):
        return int(self.dut.obs_recovery_state_o.value)

    def alerts(self):
        return int(self.dut.obs_alerts_seen_o.value)

    def dropped(self):
        return int(self.dut.obs_cmds_dropped_o.value)

    def resent(self):
        return int(self.dut.obs_cmds_resent_o.value)

    def retract(self):
        return int(self.dut.retract_req_o.value)


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_andesite_init_recovery(dut):
    tt = os.environ.get("TEST_TYPE", "smoke")
    tb = RecoveryTB(dut)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    async def pulse_alert():
        dut.parity_alert_i.value = 1
        await RisingEdge(dut.clk)
        await Timer(1, 'ns')
        dut.parity_alert_i.value = 0

    async def grant_retract():
        # the scheduler grants the retract like any maintenance request
        for _ in range(50):
            await RisingEdge(dut.clk)
            await Timer(1, 'ns')
            if tb.retract():
                dut.retract_ack_i.value = 1
                await RisingEdge(dut.clk)
                await Timer(1, 'ns')
                dut.retract_ack_i.value = 0
                return True
        return False

    if tt == "smoke":
        await tb.setup()
        chk(tb.state() == 0, f"recovery state {tb.state()} != IDLE(0)")
        chk(tb.alerts() == 0 and tb.dropped() == 0 and tb.resent() == 0,
            "recovery counters not reset-clean")
        chk(tb.retract() == 0, "retract raised with no alert")

    elif tt == "alert_walks_the_fence":
        await tb.setup(interval=5)
        await pulse_alert()
        chk(tb.alerts() == 1, f"alerts {tb.alerts()} != 1")
        chk(tb.dropped() == 1, f"dropped {tb.dropped()} != 1 in ALERT_SEEN")
        chk(tb.state() == 1, f"state {tb.state()} != ALERT_SEEN(1)")
        chk(tb.retract() == 1, "retract not raised in ALERT_SEEN")
        granted = await grant_retract()
        chk(granted, "retract never granted")
        chk(tb.state() == 2, f"state {tb.state()} != RESENDING(2)")
        # recovery interval elapses, then the release + telemetry
        for _ in range(20):
            await RisingEdge(dut.clk)
            await Timer(1, 'ns')
            if tb.state() == 0:
                break
        chk(tb.state() == 0, "recovery FSM did not return to IDLE")
        chk(tb.resent() == 1, f"resent {tb.resent()} != 1")

    elif tt == "interval_is_a_runtime_csr":
        await tb.setup(interval=9)
        await pulse_alert()
        granted = await grant_retract()
        chk(granted, "retract never granted")
        # count RESENDING residency; it must reflect the CSR, not a constant
        cycles = 0
        while tb.state() == 2 and cycles < 40:
            await RisingEdge(dut.clk)
            await Timer(1, 'ns')
            cycles += 1
        chk(tb.state() == 0, "never left RESENDING")
        chk(8 <= cycles <= 11, f"RESENDING residency {cycles} != interval 9 ±")

    elif tt == "alerts_during_init_are_recovered":
        # the recovery FSM is beside the init FSM: an alert mid-sequence
        # must run its sequence and the init must still reach READY.
        await tb.setup(interval=4)
        dut.csr_init_trigger.value = 1
        await RisingEdge(dut.clk)
        await Timer(1, 'ns')
        dut.csr_init_trigger.value = 0
        # let the init FSM get underway, then alert while it works
        for _ in range(12):
            await RisingEdge(dut.clk)
        await pulse_alert()
        granted = await grant_retract()
        chk(granted, "retract never granted during init")
        for _ in range(30):
            await RisingEdge(dut.clk)
            await Timer(1, 'ns')
            if tb.state() == 0:
                break
        chk(tb.state() == 0, "recovery did not settle during init")
        chk(tb.alerts() == 1 and tb.resent() == 1,
            f"telemetry {tb.alerts()}/{tb.resent()} != 1/1")
        # run the init to completion through the normal request path
        completed = False
        for _ in range(400):
            await RisingEdge(dut.clk)
            await Timer(1, 'ns')
            if int(dut.cmd_req.value):
                dut.cmd_ack.value = 1
                await RisingEdge(dut.clk)
                await Timer(1, 'ns')
                dut.cmd_ack.value = 0
            if int(dut.init_done.value):
                completed = True
                break
        chk(completed, "init never completed after a mid-sequence alert")

    elif tt == "telemetry_clear_is_explicit":
        await tb.setup()
        await pulse_alert()
        granted = await grant_retract()
        chk(granted, "retract never granted")
        for _ in range(20):
            await RisingEdge(dut.clk)
            await Timer(1, 'ns')
            if tb.state() == 0:
                break
        chk(tb.alerts() == 1, "precondition: an alert recorded")
        chk(tb.resent() == 1, "precondition: a re-issue recorded")
        dut.csr_telem_clear_i.value = 1
        await RisingEdge(dut.clk)
        await Timer(1, 'ns')
        dut.csr_telem_clear_i.value = 0
        await RisingEdge(dut.clk)
        await Timer(1, 'ns')
        chk(tb.alerts() == 0 and tb.dropped() == 0 and tb.resent() == 0,
            "explicit clear did not zero the counters")

    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)



_GATE = ["smoke", "alert_walks_the_fence"]
_FUNC = _GATE + ["interval_is_a_runtime_csr",
                 "alerts_during_init_are_recovered",
                 "telemetry_clear_is_explicit"]
_FULL = _FUNC
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_andesite_init_recovery(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "andesite_init_sequencer"
    test_name = f"test_andesite_init_recovery_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/mem-ctrl-research-ip/andesite-ddr4-lpddr4/"
                       "rtl/filelists/fub/andesite_init_sequencer.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_init_recovery",
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")

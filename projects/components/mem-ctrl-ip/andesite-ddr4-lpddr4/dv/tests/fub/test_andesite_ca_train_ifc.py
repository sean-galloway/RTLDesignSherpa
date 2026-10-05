# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `andesite_ca_train_ifc` -- LPDDR4 CA/WDQ training, NEW.

Per andesite_mas ch02_blocks/09_training.md: both flows ride MPC opcodes
through the formatter's LPDDR4 CA path (the issuer is reused with
`zq_ctrl`'s submodule); the opcode encodings are CSR images, TBC(JESD209-4)
-- driven, never decoded. State is per channel; the four-state telemetry
and three counters match the family page.
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


class CaTB(TBBase):
    async def setup(self, *, ca_win=4, wdq_win=3, tout=6):
        await self.start_clock('mc_clk', 10, 'ns')
        d = self.dut
        d.ca_train_en_i.value = 0
        d.wdq_cal_en_i.value = 0
        d.chan_sel_i.value = 0
        d.csr_mpc_ca_enter_i.value = 0x09
        d.csr_mpc_ca_exit_i.value = 0x19
        d.csr_mpc_wdq_enter_i.value = 0x0A
        d.csr_mpc_wdq_exit_i.value = 0x1A
        d.t_ca_train_i.value = ca_win
        d.t_wdq_cal_i.value = wdq_win
        d.t_ca_timeout_i.value = tout
        d.ca_sample_i.value = 0
        d.wdq_sample_i.value = 0
        d.cmd_ack_i.value = 0
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

    def status(self):
        return int(self.dut.status_o.value)

    def attempts(self):
        return int(self.dut.obs_attempts_o.value)

    def results(self):
        return int(self.dut.obs_results_o.value)

    def timeouts(self):
        return int(self.dut.obs_timeouts_o.value)


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_andesite_ca_train_ifc(dut):
    tt = os.environ.get("TEST_TYPE", "smoke")
    tb = CaTB(dut)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    async def run_once(flow="ca", chan=0, sample=1, hang=False):
        """One training sweep. Returns (reported, images_seen)."""
        images = []
        if flow == "ca":
            dut.ca_train_en_i.value = 1
        else:
            dut.wdq_cal_en_i.value = 1
        dut.chan_sel_i.value = chan
        await RisingEdge(dut.mc_clk)
        await Timer(1, 'ns')
        dut.ca_train_en_i.value = 0
        dut.wdq_cal_en_i.value = 0
        presented = False
        for _ in range(400):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ns')
            if int(dut.cmd_req_o.value):
                images.append(int(dut.mpc_op_o.value))
                if not hang:
                    dut.cmd_ack_i.value = 1
                    await RisingEdge(dut.mc_clk)
                    await Timer(1, 'ns')
                    dut.cmd_ack_i.value = 0
            elif int(dut.obs_state_o.value) == 2 and not presented and not hang:
                # SAMPLE state: present the observation for this channel
                if flow == "ca":
                    dut.ca_sample_i.value = sample
                else:
                    dut.wdq_sample_i.value = sample
                presented = True
            if int(dut.result_valid_o.value):
                break
        return tb.status() != 0, images

    if tt == "smoke":
        await tb.setup()
        chk(tb.status() == 0, f"status {tb.status()} != never-attempted(0)")
        chk(tb.attempts() == 0 and tb.results() == 0 and tb.timeouts() == 0,
            "counters not reset-clean")

    elif tt == "ca_flow_walks_the_fence":
        await tb.setup()
        rep, imgs = await run_once(flow="ca", chan=0, sample=1)
        chk(rep, "CA sweep never reported")
        chk(tb.status() == 1, f"status {tb.status()} != converged(1)")
        chk(imgs == [0x09, 0x19],
            f"CA flow opcodes {imgs} != [enter, exit] images")
        chk(int(dut.cmd_op_o.value) == 0x10, "command op is not OP_MPC")
        chk(tb.attempts() == 1 and tb.results() == 1,
            f"attempts/results {tb.attempts()}/{tb.results()} != 1/1")
        chk(int(dut.result_o.value) & 0x1, "CA sample bit lost")

    elif tt == "wdq_flow_uses_its_own_images":
        await tb.setup()
        rep, imgs = await run_once(flow="wdq", chan=1, sample=1)
        chk(rep, "WDQ sweep never reported")
        chk(imgs == [0x0A, 0x1A],
            f"WDQ opcodes {imgs} != [enter, exit] images")
        chk(tb.attempts() == 1, f"attempts {tb.attempts()} != 1")
        chk(int(dut.result_o.value) & 0x2, "WDQ sample bit lost on chan 1")

    elif tt == "opcode_images_are_not_decoded":
        # The encodings are CSR images; flipping them must flow to the pin
        await tb.setup()
        dut.csr_mpc_ca_enter_i.value = 0x2B
        rep, imgs = await run_once(flow="ca", sample=1)
        chk(rep, "sweep never reported")
        chk(imgs[0] == 0x2B, f"flipped image not driven: {imgs}")

    elif tt == "timeout_is_a_distinct_status":
        await tb.setup(tout=5)
        rep, _ = await run_once(flow="ca", hang=True)
        chk(rep, "hung sweep never reported")
        chk(tb.status() == 2, f"status {tb.status()} != timed-out(2)")
        chk(tb.timeouts() == 1 and tb.results() == 0,
            f"timeouts/results {tb.timeouts()}/{tb.results()} != 1/0")

    elif tt == "attempts_count_both_flows":
        await tb.setup()
        for flow in ("ca", "wdq", "ca"):
            rep, _ = await run_once(flow=flow, sample=1)
            chk(rep, f"{flow} sweep never reported")
        chk(tb.attempts() == 3, f"attempts {tb.attempts()} != 3")

    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('mc_clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["smoke", "ca_flow_walks_the_fence"]
_FUNC = _GATE + ["wdq_flow_uses_its_own_images",
                 "opcode_images_are_not_decoded",
                 "timeout_is_a_distinct_status",
                 "attempts_count_both_flows"]
_FULL = _FUNC
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_andesite_ca_train_ifc(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "andesite_ca_train_ifc"
    test_name = f"test_andesite_ca_train_ifc_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/"
                       "rtl/filelists/fub/andesite_ca_train_ifc.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_ca_train_ifc",
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")

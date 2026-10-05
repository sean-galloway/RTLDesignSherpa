# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `andesite_rdlvl_ifc` -- DDR4 MPR read leveling, NEW.

Per andesite_mas ch02_blocks/09_training.md: the block sequences MPR entry
(MRW of the CSR MR3 image), the DFI read-leveling handshake, pattern capture
per chip select, MPR exit, and the four-state telemetry. No search states:
the host re-asserts enable with a new delay setting. Ordering checks live in
DV (this file), not the RTL.
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

NUM_CS = 2


class RdTB(TBBase):
    async def setup(self, *, enter=4, exit=3, readout=5, tmod=2, tout=6):
        await self.start_clock('mc_clk', 10, 'ns')
        d = self.dut
        d.rdlvl_en_i.value = 0
        d.cs_sel_i.value = 0
        d.csr_mr3_mpr_enter_i.value = 0x3101
        d.csr_mr3_mpr_exit_i.value = 0x3001
        d.t_mpr_enter_i.value = enter
        d.t_mpr_exit_i.value = exit
        d.t_mpr_readout_i.value = readout
        d.tmod_i.value = tmod
        d.t_rdlvl_timeout_i.value = tout
        d.mpr_pattern_i.value = 0
        d.cmd_ack_i.value = 0
        d.dfi_phylvl_req_cs_n_i.value = 0x3   # no PHY request (idle-high)
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
async def cocotb_test_andesite_rdlvl_ifc(dut):
    tt = os.environ.get("TEST_TYPE", "smoke")
    tb = RdTB(dut)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    async def run_once(cs=0, pattern=0x1, ack_every=1, timeout=False):
        """One leveling sweep: enable, service MRWs, ack the handshake,
        present the pattern during CAPTURE. Returns (converged, events)."""
        events = []
        dut.cs_sel_i.value = cs
        dut.rdlvl_en_i.value = 1
        await RisingEdge(dut.mc_clk)
        await Timer(1, 'ns')
        dut.rdlvl_en_i.value = 0
        granted = 0
        for _ in range(400):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ns')
            op = int(dut.cmd_op_o.value)
            if int(dut.cmd_req_o.value):
                events.append(op)
                if op == 0x0A:                    # OP_MRS
                    dut.cmd_ack_i.value = 1
                    await RisingEdge(dut.mc_clk)
                    await Timer(1, 'ns')
                    dut.cmd_ack_i.value = 0
            elif (int(dut.dfi_phylvl_ack_cs_n_o.value) == (0x3 & ~(1 << cs))) \
                    and not timeout:
                # controller acked; PHY grants by dropping req for this CS
                bit = (pattern >> granted) & 1
                dut.dfi_phylvl_req_cs_n_i.value = 0x3 & ~(1 << cs)
                dut.mpr_pattern_i.value = bit
                await RisingEdge(dut.mc_clk)
                await Timer(1, 'ns')
                dut.dfi_phylvl_req_cs_n_i.value = 0x3
                granted += 1
            # result_valid pulses once per sweep -- status persists across
            # sweeps, so only the pulse is a fresh-report signal
            if int(dut.result_valid_o.value):
                break
        return tb.status() != 0, events

    if tt == "smoke":
        await tb.setup()
        chk(tb.status() == 0, f"status {tb.status()} != never-attempted(0)")
        chk(tb.attempts() == 0 and tb.results() == 0 and tb.timeouts() == 0,
            "counters not reset-clean")

    elif tt == "fsm_walks_the_fence":
        await tb.setup()
        conv, ev = await run_once(cs=0, pattern=0x1)
        chk(conv, "never converged")
        chk(tb.status() == 1, f"status {tb.status()} != converged(1)")
        # two MRWs: MPR entry then MPR exit (MR3 both, images differ)
        chk(ev.count(0x0A) == 2, f"expected 2 MRW ops, got {ev}")
        chk(int(dut.csr_mr3_mpr_enter_i.value) != int(dut.csr_mr3_mpr_exit_i.value),
            "test misconfigured: enter/exit images must differ")
        chk(int(dut.cmd_addr_o.value) in
            (int(dut.csr_mr3_mpr_enter_i.value), int(dut.csr_mr3_mpr_exit_i.value)),
            "last MRW did not carry an MR3 image on cmd_addr")
        chk(tb.attempts() == 1, f"attempts {tb.attempts()} != 1")
        chk(tb.results() == 1, f"results {tb.results()} != 1")
        chk(int(dut.result_o.value) & 0x1, "captured pattern bit lost")

    elif tt == "capture_is_per_chip_select":
        await tb.setup()
        conv0, _ = await run_once(cs=0, pattern=0x1)
        chk(conv0, "cs0 sweep did not converge")
        r0 = int(dut.result_o.value) & 0x3
        conv1, _ = await run_once(cs=1, pattern=0x0)
        chk(conv1, "cs1 sweep did not converge")
        r1 = int(dut.result_o.value) & 0x3
        chk((r0 & 0x1) == 0x1, f"cs0 result bit {r0 & 1} != 1")
        chk((r1 & 0x2) == 0x0, f"cs1 result bit {(r1 >> 1) & 1} != 0")

    elif tt == "timeout_is_a_distinct_status":
        await tb.setup(tout=5)
        conv, _ = await run_once(timeout=True)
        chk(conv, "never reported")
        chk(tb.status() == 2, f"status {tb.status()} != timed-out(2)")
        chk(tb.timeouts() == 1, f"timeouts {tb.timeouts()} != 1")
        chk(tb.results() == 0, "a timeout must not count a result")

    elif tt == "attempts_count_enable_assertions":
        await tb.setup()
        for _ in range(3):
            conv, _ = await run_once(pattern=0x1)
            chk(conv, "a sweep did not converge")
        chk(tb.attempts() == 3, f"attempts {tb.attempts()} != 3")
        chk(tb.status() == 1, "status not converged after 3 sweeps")

    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('mc_clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["smoke", "fsm_walks_the_fence"]
_FUNC = _GATE + ["capture_is_per_chip_select", "timeout_is_a_distinct_status",
                 "attempts_count_enable_assertions"]
_FULL = _FUNC
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_andesite_rdlvl_ifc(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "andesite_rdlvl_ifc"
    test_name = f"test_andesite_rdlvl_ifc_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/"
                       "rtl/filelists/fub/andesite_rdlvl_ifc.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_rdlvl_ifc",
        sim_build=sim_build, simulator="verilator",
        parameters={"NUM_CS": str(NUM_CS)},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")

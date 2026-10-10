# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `scoria_init_sequencer` -- the JEDEC DDR3 power-up sequence.

pumice's equivalent exists but checks the DDR2 sequence, which this does not
share: scoria drops seven DDR2 states (no PREA, no double REF, no OCD pair, no
second MR0 -- DDR3's DLL-reset bit is self-clearing per JESD79-3F 3.4.2.4) and
adds RESET_n, tXPR and ZQCL. So this is written from the sequence, not ported.

The whole module is a command GENERATOR, so the test captures the command
stream and asserts on it rather than poking at state encodings. What the stream
must show:

  RESET_n held low across reset, DFI init and the RSTN state, released after.
  It is a real DRAM pin, and getting it wrong does not degrade init -- it
  prevents the device from ever initialising.

  MR2, MR3, MR1, MR0 in that order. DDR3's order is not DDR2's, and an MRS
  chain in the wrong order can leave CWL or ODT applied after the register
  that depends on them.

  exactly ONE ZQCL, after MR0. Two would be harmless; zero means the device
  never calibrates its output drivers and the board hunt that follows looks
  like a PHY problem.

  MR0's COMMAND carries the DLL-reset bit while the SHADOW does not, so the
  controller's CL/CWL/BL decode tracks the steady-state value rather than the
  reset pulse.
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

MEMTYPE_DDR3, MEMTYPE_LPDDR3 = 0, 1
DDR3_DLL_RESET = 1 << 8          # MR0 A8, JESD79-3F 3.4.2.4


class InitTB(TBBase):
    async def setup(self, memtype=MEMTYPE_DDR3, *, mr0=0x0620, mr1=0x0044,
                    mr2=0x0008, mr3=0x0000, init=4, dll=6, xpr=5,
                    zqinit=9, mrd=3, rp=3, rfc=4):
        await self.start_clock('mc_clk', 10, 'ns')
        d = self.dut
        d.memtype_i.value = memtype
        d.t_init_wait_i.value = init
        d.t_dll_wait_i.value = dll
        d.t_xpr_wait_i.value = xpr
        d.t_zqinit_wait_i.value = zqinit
        d.t_mrd_wait_i.value = mrd
        d.t_rp_wait_i.value = rp
        d.t_rfc_wait_i.value = rfc
        d.mr0_i.value = mr0
        d.mr1_i.value = mr1
        d.mr2_i.value = mr2
        d.mr3_i.value = mr3
        d.init_restart_i.value = 0
        d.dfi_init_complete_i.value = 0
        d.zqcl_grant_i.value = 1
        await self.assert_reset()
        await self.wait_clocks('mc_clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('mc_clk', 2)

    async def assert_reset(self):
        self.dut.mc_rst_n.value = 0

    async def deassert_reset(self):
        self.dut.mc_rst_n.value = 1

    async def setup_clocks_and_reset(self):
        await self.setup()

    async def run_init(self, limit=600, complete_after=3):
        """Drive init to completion, capturing the command stream.

        Returns (cmds, trace) where cmds is a list of
        (op, bank, row, shadow_we, shadow_idx, shadow_data) and trace records
        dram_reset_n per cycle so the pin can be checked over the whole run.
        """
        cmds, trace = [], []
        for i in range(limit):
            await RisingEdge(self.dut.mc_clk)
            if i == complete_after:
                self.dut.dfi_init_complete_i.value = 1
            trace.append({
                'rstn': int(self.dut.dram_reset_n_o.value),
                'start': int(self.dut.dfi_init_start_o.value),
                'busy': int(self.dut.init_busy_o.value),
                'done': int(self.dut.init_done_o.value),
            })
            if int(self.dut.init_cmd_valid_o.value):
                cmds.append({
                    'op':   int(self.dut.init_cmd_op_o.value),
                    'bank': int(self.dut.init_cmd_bank_o.value),
                    'row':  int(self.dut.init_cmd_row_o.value),
                    'we':   int(self.dut.mr_seq_we_o.value),
                    'idx':  int(self.dut.mr_seq_index_o.value),
                    'data': int(self.dut.mr_seq_data_o.value),
                    'cyc':  i,
                })
            if int(self.dut.init_done_o.value):
                return cmds, trace
        return cmds, trace


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_scoria_init_sequencer(dut):
    tt = os.environ.get("TEST_TYPE", "ddr3_sequence")
    tb = InitTB(dut)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    # dram_op_e, scoria_pkg: OP_MRS = 4'hA, OP_ZQCL = 4'hC. Taken from the
    # package rather than guessed -- the first draft used 8 for OP_MRS and
    # would have classified every MRS as "not an MRS".
    OP_MRS = int(os.environ.get("OP_MRS", "10"))
    OP_ZQCL = int(os.environ.get("OP_ZQCL", "12"))

    if tt == "ddr3_sequence":
        await tb.setup(MEMTYPE_DDR3)
        cmds, trace = await tb.run_init()
        chk(trace and trace[-1]['done'] == 1, "init never completed")
        # MRS commands, in order, by shadow index
        mrs = [c for c in cmds if c['we']]
        idxs = [c['idx'] for c in mrs]
        chk(idxs == [2, 3, 1, 0],
            f"MRS order {idxs} != [2, 3, 1, 0] (JESD79-3F DDR3 order)")
        zq = [c for c in cmds if not c['we'] and c['op'] == OP_ZQCL]
        chk(len(zq) == 1, f"{len(zq)} ZQCL issued, expected exactly 1")
        if zq and mrs:
            chk(zq[0]['cyc'] > mrs[-1]['cyc'],
                "ZQCL issued BEFORE the last MRS -- the DRAM calibrates "
                "against un-programmed mode registers")

    elif tt == "reset_n_pin":
        # RESET_n low through reset + DFI init + RSTN, then released and STAYS
        # released. It is a device pin; a glitch here re-initialises the DRAM
        # mid-sequence.
        await tb.setup(MEMTYPE_DDR3)
        cmds, trace = await tb.run_init()
        chk(trace[0]['rstn'] == 0, "dram_reset_n high at the very start")
        rel = next((i for i, t in enumerate(trace) if t['rstn']), None)
        chk(rel is not None, "dram_reset_n never released")
        if rel is not None:
            chk(all(t['rstn'] for t in trace[rel:]),
                "dram_reset_n went LOW again after being released")
            chk(not any(c['cyc'] < rel for c in cmds),
                "a command was issued while dram_reset_n was still asserted")

    elif tt == "mr0_dll_reset_bit":
        # The COMMAND carries A8; the SHADOW must not.
        mr0 = 0x0620
        await tb.setup(MEMTYPE_DDR3, mr0=mr0)
        cmds, _ = await tb.run_init()
        m0 = [c for c in cmds if c['we'] and c['idx'] == 0]
        chk(len(m0) == 1, f"{len(m0)} MR0 writes, expected 1")
        if m0:
            chk(m0[0]['row'] & DDR3_DLL_RESET != 0,
                f"MR0 COMMAND row 0x{m0[0]['row']:04X} lacks the DLL-reset bit "
                f"(A8) -- the DLL is never reset")
            chk(m0[0]['data'] == mr0,
                f"MR0 SHADOW 0x{m0[0]['data']:04X} != mr0_i 0x{mr0:04X} -- the "
                f"shadow must hold the steady-state value, not the reset pulse")

    elif tt == "zqcl_wait_takes_the_longer":
        # Step 11 waits BOTH tDLLK and tZQinit, which means the larger.
        await tb.setup(MEMTYPE_DDR3, dll=4, zqinit=40)
        c1, t1 = await tb.run_init(limit=900)
        n_big_zq = len(t1)
        await tb.setup(MEMTYPE_DDR3, dll=40, zqinit=4)
        c2, t2 = await tb.run_init(limit=900)
        n_big_dll = len(t2)
        await tb.setup(MEMTYPE_DDR3, dll=4, zqinit=4)
        c3, t3 = await tb.run_init(limit=900)
        n_small = len(t3)
        chk(n_big_zq > n_small,
            f"a large tZQinit ({n_big_zq}) did not lengthen init vs small "
            f"({n_small}) -- tZQinit is being ignored")
        chk(n_big_dll > n_small,
            f"a large tDLLK ({n_big_dll}) did not lengthen init vs small "
            f"({n_small}) -- tDLLK is being ignored")

    elif tt == "done_is_terminal":
        await tb.setup(MEMTYPE_DDR3)
        cmds, trace = await tb.run_init()
        chk(trace[-1]['done'] == 1, "never done")
        n = len(cmds)
        await tb.wait_clocks('mc_clk', 60)
        chk(int(dut.init_done_o.value) == 1, "done de-asserted after completing")
        chk(int(dut.init_busy_o.value) == 0, "still busy after done")
        chk(int(dut.init_cmd_valid_o.value) == 0,
            "issuing commands after init_done -- the sequencer must be quiet")

    elif tt == "restart_reruns":
        await tb.setup(MEMTYPE_DDR3)
        c1, _ = await tb.run_init()
        chk(len(c1) > 0, "no commands on the first pass")
        dut.init_restart_i.value = 1
        await tb.wait_clocks('mc_clk', 2)
        dut.init_restart_i.value = 0
        dut.dfi_init_complete_i.value = 0
        c2, t2 = await tb.run_init(limit=900)
        chk(t2[-1]['done'] == 1, "did not complete after restart")
        chk(len(c2) == len(c1),
            f"restart issued {len(c2)} commands, first pass {len(c1)}")

    elif tt == "lpddr3_path_differs":
        # LPDDR3 has no ZQCL bus command -- ZQ init is an MRW(MR10).
        await tb.setup(MEMTYPE_LPDDR3)
        cmds, trace = await tb.run_init(limit=900)
        chk(trace[-1]['done'] == 1, "LPDDR3 init never completed")
        zq = [c for c in cmds if c['op'] == OP_ZQCL]
        chk(len(zq) == 0,
            f"LPDDR3 issued {len(zq)} ZQCL bus command(s) -- LPDDR3 does ZQ "
            f"init via MRW(MR10), not a ZQCL command")
        chk(all(int(t['rstn']) == 1 for t in trace),
            "dram_reset_n driven low on LPDDR3 -- it has no RESET_n pin")

    elif tt == "random_timings":
        rng = random.Random(int(os.environ.get('SEED', '5')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 3, "FUNC": 8, "FULL": 20}.get(lvl, 8)
        for _ in range(n):
            await tb.setup(MEMTYPE_DDR3,
                           init=rng.randint(1, 10), dll=rng.randint(1, 12),
                           xpr=rng.randint(1, 10), zqinit=rng.randint(1, 12),
                           mrd=rng.randint(1, 6))
            cmds, trace = await tb.run_init(limit=900)
            chk(trace[-1]['done'] == 1, "init did not complete")
            idxs = [c['idx'] for c in cmds if c['we']]
            chk(idxs == [2, 3, 1, 0],
                f"MRS order {idxs} != [2,3,1,0] under random timings")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('mc_clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["ddr3_sequence", "reset_n_pin", "mr0_dll_reset_bit"]
_FUNC = _GATE + ["zqcl_wait_takes_the_longer", "done_is_terminal",
                 "restart_reruns", "lpddr3_path_differs", "random_timings"]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_scoria_init_sequencer(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "scoria_init_sequencer"
    test_name = f"test_scoria_init_sequencer_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/"
                       "rtl/filelists/fub/scoria_init_sequencer.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_scoria_init_sequencer",
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")

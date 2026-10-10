# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""Macro tests for `andesite_training_layer` (TASK-016 t4).

The layer owns the three training FUBs, the DFI pin mux, the one-active
policy, the maintenance command channel into the scheduler, and the CDC to
the DFI PHY. These cases exercise each flow in isolation, the one-active
serialization, the timeout paths, and a random soak.
"""

import os
import random
import subprocess
import sys

import cocotb
import pytest
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)
_BIN = os.path.join(_repo_root, "bin")
if _BIN not in sys.path:
    sys.path.insert(0, _BIN)

_DV = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _DV not in sys.path:
    sys.path.insert(0, _DV)

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, sim_build_path
from tbclasses.andesite_training_layer_tb import AndesiteTrainingLayerTB

OP_MRS = 0xA
OP_MPC = 0x10


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_andesite_training_layer(dut):
    tt = os.environ.get("TEST_TYPE", "wrlvl_path_still_works")
    tb = AndesiteTrainingLayerTB(dut)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m)
            tb.log.error(m)

    await tb.setup()
    num_cs = int(os.environ.get('NUM_CS', '1'))
    all_cs_high = (1 << num_cs) - 1

    if tt == "wrlvl_path_still_works":
        dut.wrlvl_en_i.value = 1
        # Wait for READY (obs_state_o == 3).
        ready = False
        for _ in range(200):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ps')
            if int(dut.wrlvl_state_o.value) == 3:
                ready = True
                break
        chk(ready, "wrlvl never reached READY")
        dut.wrlvl_prime_dq_i.value = 1
        await tb.pulse('wrlvl_strobe_i')
        # Wait for result_valid.
        got = False
        for _ in range(200):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ps')
            if int(dut.wrlvl_result_valid_o.value):
                got = True
                break
        chk(got, "wrlvl result_valid never asserted")
        chk(int(dut.wrlvl_result_o.value) == 1, "wrlvl result != prime_dq")
        chk(int(dut.wrlvl_attempts_o.value) == 1, "wrlvl attempts != 1")
        chk(int(dut.wrlvl_ever_done_o.value) == 1, "wrlvl ever_done not set")
        # DFI pins should show wrlvl request active-low for cs0.
        chk(int(dut.dfi_phylvl_req_cs_n_o.value) == (all_cs_high & ~1),
            "wrlvl did not drive dfi_phylvl_req_cs_n_o active-low")

    elif tt == "rdlvl_issues_mrs_pair":
        dut.rdlvl_cs_sel_i.value = 0
        dut.csr_mr3_mpr_enter_i.value = 0x3101
        dut.csr_mr3_mpr_exit_i.value = 0x3001
        await tb.pulse('rdlvl_en_i')
        # Collect both MRS requests as they appear and mock the PHY handshake.
        addrs = []
        prev_req = 0
        done = False
        for _ in range(400):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ps')
            req = int(dut.trn_cmd_req_o.value)
            if req and not prev_req:
                addrs.append(int(dut.trn_cmd_addr_o.value))
                chk(int(dut.trn_cmd_op_o.value) == OP_MRS, "rdlvl cmd op != MRS")
                chk(int(dut.trn_cmd_bank_o.value) == 3, "rdlvl cmd bank != 3")
            prev_req = req
            # Mock PHY handshake: when controller ack is active-low for cs0,
            # grant by dropping PHY req for one cycle.
            if int(dut.dfi_phylvl_ack_cs_n_o.value) == (all_cs_high & ~1):
                dut.dfi_phylvl_req_cs_n_i.value = all_cs_high & ~1
                await RisingEdge(dut.mc_clk)
                await Timer(1, 'ps')
                dut.dfi_phylvl_req_cs_n_i.value = all_cs_high
            if int(dut.rdlvl_result_valid_o.value):
                done = True
                break
        chk(done, "rdlvl never finished")
        chk(len(addrs) >= 2, f"rdlvl issued {len(addrs)} MRS, expected 2")
        chk(addrs[0] == 0x3101, f"rdlvl enter image {addrs[0]} != 0x3101")
        chk(addrs[1] == 0x3001, f"rdlvl exit image {addrs[1]} != 0x3001")

    elif tt == "ca_train_uses_mpc_opcodes":
        dut.csr_mpc_ca_enter_i.value = 0x2B
        dut.csr_mpc_ca_exit_i.value = 0x3B
        await tb.pulse('ca_train_en_i')
        seen = []
        prev_req = 0
        done = False
        for _ in range(300):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ps')
            req = int(dut.trn_cmd_req_o.value)
            if req and not prev_req:
                seen.append((int(dut.trn_cmd_op_o.value),
                             int(dut.trn_cmd_addr_o.value) & 0x3F))
            prev_req = req
            if int(dut.ca_train_state_o.value) == 2 and not done:
                dut.ca_sample_i.value = 1
                done = True
            if int(dut.ca_train_result_valid_o.value):
                break
        chk(len(seen) >= 2, f"CA flow issued {len(seen)} commands, expected >=2")
        chk(seen[0][0] == OP_MPC, "CA first cmd op != OP_MPC")
        chk(seen[0][1] == 0x2B, f"CA enter opcode {seen[0][1]} != 0x2B")
        chk(seen[1][0] == OP_MPC, "CA second cmd op != OP_MPC")
        chk(seen[1][1] == 0x3B, f"CA exit opcode {seen[1][1]} != 0x3B")

    elif tt == "one_active_lockout":
        # Enter wrlvl mode and pulse rdlvl. rdlvl must not issue until wrlvl
        # clears and the mux has gone idle.
        dut.wrlvl_en_i.value = 1
        # DFI outputs cross a 3-flop CDC; give them time to settle.
        for _ in range(12):
            await RisingEdge(dut.dfi_clk)
        await Timer(1, 'ps')
        chk(int(dut.dfi_phylvl_req_cs_n_o.value) == (all_cs_high & ~1),
            "wrlvl did not own DFI request pins")
        await tb.pulse('rdlvl_en_i')
        # Give it some cycles; no rdlvl cmd_req should appear.
        bad = False
        for _ in range(30):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ps')
            if int(dut.trn_cmd_req_o.value) and int(dut.trn_cmd_op_o.value) == OP_MRS:
                bad = True
                break
        chk(not bad, "rdlvl issued MRS while wrlvl mode was active")
        # Clear wrlvl; rdlvl should now proceed.
        dut.wrlvl_en_i.value = 0
        saw = False
        for _ in range(200):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ps')
            if int(dut.trn_cmd_req_o.value) and int(dut.trn_cmd_op_o.value) == OP_MRS:
                saw = True
                break
        chk(saw, "rdlvl did not proceed after wrlvl cleared")

    elif tt == "timeout_paths_report":
        # rdlvl: ack the MRS commands but never grant the PHY handshake.
        dut.t_rdlvl_timeout_i.value = 4
        await tb.pulse('rdlvl_en_i')
        done = False
        for _ in range(300):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ps')
            if int(dut.rdlvl_result_valid_o.value):
                done = True
                break
        chk(done, "rdlvl timeout never reported")
        chk(int(dut.rdlvl_status_o.value) == 2,
            f"rdlvl status {int(dut.rdlvl_status_o.value)} != TIMEOUT(2)")
        chk(int(dut.rdlvl_timeouts_o.value) == 1,
            f"rdlvl timeouts {int(dut.rdlvl_timeouts_o.value)} != 1")
        # ca_train timeout path: do not ack the MPC command.
        tb.cmd_ack_enable = False
        dut.t_ca_timeout_i.value = 4
        await tb.pulse('ca_train_en_i')
        done = False
        for _ in range(300):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ps')
            if int(dut.ca_train_result_valid_o.value):
                done = True
                break
        chk(done, "ca_train timeout never reported")
        chk(int(dut.ca_train_status_o.value) == 2,
            f"ca_train status {int(dut.ca_train_status_o.value)} != TIMEOUT(2)")
        chk(int(dut.ca_train_timeouts_o.value) == 1,
            f"ca_train timeouts {int(dut.ca_train_timeouts_o.value)} != 1")

    elif tt == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '11')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 40, "FUNC": 200, "FULL": 600}.get(lvl, 200)
        for _ in range(n):
            # Randomly assert one flow at a time.
            flow = rng.choice(['wrlvl', 'rdlvl', 'ca', 'wdq'])
            if flow == 'wrlvl':
                dut.wrlvl_en_i.value = 1
                dut.wrlvl_prime_dq_i.value = rng.randint(0, 1)
                for _ in range(rng.randint(1, 6)):
                    await RisingEdge(dut.mc_clk)
                    await Timer(1, 'ps')
                    if rng.random() < 0.5 and int(dut.wrlvl_state_o.value) == 3:
                        await tb.pulse('wrlvl_strobe_i')
                dut.wrlvl_en_i.value = 0
            elif flow == 'rdlvl':
                dut.rdlvl_cs_sel_i.value = rng.randint(0, max(0, num_cs - 1))
                await tb.pulse('rdlvl_en_i')
                # Maybe grant, maybe timeout.
                for _ in range(rng.randint(5, 60)):
                    await RisingEdge(dut.mc_clk)
                    await Timer(1, 'ps')
                    if (int(dut.dfi_phylvl_ack_cs_n_o.value) != all_cs_high
                            and rng.random() < 0.8):
                        cs = int(dut.rdlvl_cs_sel_i.value)
                        dut.dfi_phylvl_req_cs_n_i.value = all_cs_high & ~(1 << cs)
                        await RisingEdge(dut.mc_clk)
                        await Timer(1, 'ps')
                        dut.dfi_phylvl_req_cs_n_i.value = all_cs_high
            elif flow == 'ca':
                await tb.pulse('ca_train_en_i')
                for _ in range(rng.randint(5, 40)):
                    await RisingEdge(dut.mc_clk)
                    await Timer(1, 'ps')
                    if int(dut.ca_train_state_o.value) == 2:
                        dut.ca_sample_i.value = rng.randint(0, 1)
            else:
                await tb.pulse('wdq_cal_en_i')
                for _ in range(rng.randint(5, 40)):
                    await RisingEdge(dut.mc_clk)
                    await Timer(1, 'ps')
                    if int(dut.ca_train_state_o.value) == 2:
                        dut.wdq_sample_i.value = rng.randint(0, 1)
            # At most one flow's result_valid should be outstanding at a time.
            v_wl = int(dut.wrlvl_result_valid_o.value)
            v_rd = int(dut.rdlvl_result_valid_o.value)
            v_ca = int(dut.ca_train_result_valid_o.value)
            chk((v_wl + v_rd + v_ca) <= 1,
                f"multiple result_valids high: wl={v_wl} rd={v_rd} ca={v_ca}")
            # DFI pins must never be X.
            try:
                int(dut.dfi_phylvl_req_cs_n_o.value)
                int(dut.dfi_phy_wrlvl_cs_n_o.value)
                int(dut.dfi_phy_rdlvl_cs_n_o.value)
                int(dut.dfi_wrlvl_strobe_o.value)
            except Exception:
                chk(False, "DFI training pins went X during random soak")
        # Drain any pending one-shot.
        for _ in range(200):
            await RisingEdge(dut.mc_clk)

    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('mc_clk', 4)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["wrlvl_path_still_works"]
_FUNC = _GATE + [
    "rdlvl_issues_mrs_pair",
    "ca_train_uses_mpc_opcodes",
    "one_active_lockout",
    "timeout_paths_report",
    "random_soak",
]
_FULL = _FUNC
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_andesite_training_layer(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "andesite_training_layer"
    test_name = f"test_andesite_training_layer_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/mem-ctrl-research-ip/andesite-ddr4-lpddr4/"
                       "rtl/filelists/macro/andesite_training_layer.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_training_layer",
        sim_build=sim_build, simulator="verilator",
        parameters={"NUM_CS": os.environ.get('NUM_CS', '1')},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "NUM_CS": os.environ.get('NUM_CS', '1'),
                   "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")

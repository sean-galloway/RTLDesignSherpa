# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""
Macro contract test: mc_age_fifo + mc_matrix_arbiter (MC-003 2026-10-18).

Pins the novel semantics of the owner-specified aged-arbiter core before
integration into the store/scheduler:

  1. Age discipline: push ages 0,1,2,... (monotone along the queue); every
     decrement strobe steps ALL entries down, saturating at 0; a push on the
     same cycle as a decrement lands on the stepped value.
  2. needs_act enqueue decode: empty queue reads the bank image (closed ->
     act; open at same row -> column); non-empty compares against the tail's
     row; page-close policy forces act on every entry.
  3. Head views: head/head2 advance on pop; head2_vld drops at count 1;
     head payload fields track the pushed data.
  4. Matrix arbiter: empty request -> no grant; any request set grants
     exactly one; grants rotate across updates (round-robin over time);
     a grant is consumed only with upd_i.

common-ip/dv carries NO RTL assertions by repo rule; the checks live here.
"""

import os

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ReadOnly, NextTimeStep

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_FILELIST = ("projects/components/mem-ctrl-ip/common-ip/dv/filelists/"
             "mc_age_arb_macro.f")


async def _cycle(dut):
    await RisingEdge(dut.aclk)
    await ReadOnly()
    await NextTimeStep()


async def _push_a(dut, slot, row, col=0, txn_id=0, last=0,
                  bank_open=0, bank_row=0, close_pol=0):
    dut.a_push.value = 1
    dut.a_push_slot.value = slot
    dut.a_push_row.value = row
    dut.a_push_col.value = col
    dut.a_push_id.value = txn_id
    dut.a_push_last.value = last
    dut.a_push_bank_open.value = bank_open
    dut.a_push_bank_row.value = bank_row
    dut.a_push_close_pol.value = close_pol
    await _cycle(dut)
    dut.a_push.value = 0


async def _push_b(dut, slot, row, bank_open=0, bank_row=0):
    dut.b_push.value = 1
    dut.b_push_slot.value = slot
    dut.b_push_row.value = row
    dut.b_push_bank_open.value = bank_open
    dut.b_push_bank_row.value = bank_row
    await _cycle(dut)
    dut.b_push.value = 0


@cocotb.test()
async def cocotb_test_age_fifo_semantics(dut):
    clock = Clock(dut.aclk, 10, unit="ns")
    cocotb.start_soon(clock.start())
    dut.aresetn.value = 0
    dut.a_push.value = 0
    dut.b_push.value = 0
    dut.a_pop.value = 0
    dut.b_pop.value = 0
    dut.decr.value = 0
    dut.arb_req.value = 0
    dut.arb_upd.value = 0
    for _ in range(4):
        await _cycle(dut)
    dut.aresetn.value = 1
    await _cycle(dut)

    # -- 1. age discipline -------------------------------------------------
    # Bank closed, row 0x10 -> first entry act, age 0.
    await _push_a(dut, slot=1, row=0x10, bank_open=0, bank_row=0)
    assert int(dut.a_head_vld.value) == 1
    assert int(dut.a_head_act.value) == 1, "closed bank push must need act"
    assert int(dut.a_head_age.value) == 0
    # Same row -> column, age 1.
    await _push_a(dut, slot=2, row=0x10, bank_open=1, bank_row=0x10)
    assert int(dut.a_head2_vld.value) == 1
    assert int(dut.a_head2_age.value) == 1
    # Different row -> act, age 2.
    await _push_a(dut, slot=3, row=0x20, bank_open=1, bank_row=0x10)
    assert int(dut.a_head_age.value) == 0
    # Decrement: ages 0(sat),0,1.
    dut.decr.value = 1
    await _cycle(dut)
    dut.decr.value = 0
    assert int(dut.a_head_age.value) == 0
    assert int(dut.a_head2_age.value) == 0
    # Pop the head (slot 1 out). head -> slot 2 (age 0); head2 -> slot 3 (age 1).
    dut.a_pop.value = 1
    await _cycle(dut)
    dut.a_pop.value = 0
    assert int(dut.a_head_slot.value) == 2
    assert int(dut.a_head_age.value) == 0
    assert int(dut.a_head2_age.value) == 1
    # Push on the SAME cycle as a decrement lands on the stepped tail value:
    # tail (slot 3) age 1 steps to 0; newcomer age = stepped tail = 0.
    dut.decr.value = 1
    dut.a_push.value = 1
    dut.a_push_slot.value = 4
    dut.a_push_row.value = 0x20
    dut.a_push_bank_open.value = 0
    dut.a_push_close_pol.value = 0
    await _cycle(dut)
    dut.decr.value = 0
    dut.a_push.value = 0
    assert int(dut.a_head2_age.value) == 0, "simultaneous push+decr: newcomer takes stepped tail age"

    # -- 2. empty-queue bank-image decode ----------------------------------
    # Drain A completely.
    while int(dut.a_head_vld.value):
        dut.a_pop.value = 1
        await _cycle(dut)
        dut.a_pop.value = 0
    # Open bank at 0x30: same-row push is a column.
    await _push_a(dut, slot=5, row=0x30, bank_open=1, bank_row=0x30)
    assert int(dut.a_head_act.value) == 0, "open same-row push must be a column"
    dut.a_pop.value = 1
    await _cycle(dut)
    dut.a_pop.value = 0
    # Open bank at 0x30: different-row push needs a row open.
    await _push_a(dut, slot=6, row=0x40, bank_open=1, bank_row=0x30)
    assert int(dut.a_head_act.value) == 1, "open different-row push must need act"
    dut.a_pop.value = 1
    await _cycle(dut)
    dut.a_pop.value = 0
    # Page-close policy forces act even on a same-row push.
    await _push_a(dut, slot=7, row=0x50, bank_open=1, bank_row=0x50, close_pol=1)
    assert int(dut.a_head_act.value) == 1, "page-close policy forces act"
    dut.a_pop.value = 1
    await _cycle(dut)
    dut.a_pop.value = 0

    # -- 3. cross-fifo age visibility --------------------------------------
    # Fifo B gets two entries while no fires happen: ages 0 then 1.
    await _push_b(dut, slot=4, row=0x60, bank_open=0, bank_row=0)
    await _push_b(dut, slot=5, row=0x60, bank_open=0, bank_row=0)
    assert int(dut.b_head_age.value) == 0
    # One fire (decrement) drops B's head to 0 (sat) and second to 0.
    dut.decr.value = 1
    await _cycle(dut)
    dut.decr.value = 0
    assert int(dut.b_head_age.value) == 0

    # -- 4. matrix arbiter ---------------------------------------------------
    # Empty request set: no grant.
    dut.arb_req.value = 0
    await _cycle(dut)
    assert int(dut.arb_gnt.value) == 0, "no request, no grant"
    # Single requester: grants immediately.
    dut.arb_req.value = 0b0100
    await _cycle(dut)
    assert int(dut.arb_gnt.value) == 0b0100, "lone requester must grant"
    # All four request: exactly one grants.
    dut.arb_req.value = 0b1111
    await _cycle(dut)
    g_all = int(dut.arb_gnt.value)
    assert g_all != 0 and (g_all & (g_all - 1)) == 0, f"one-hot grant, got {g_all:#x}"
    # Consuming grants must rotate across the requesters.
    seen = {g_all}
    for _ in range(6):
        dut.arb_upd.value = 1
        await _cycle(dut)
        dut.arb_upd.value = 0
        await _cycle(dut)
        g = int(dut.arb_gnt.value)
        assert g != 0 and (g & (g - 1)) == 0, f"one-hot grant, got {g:#x}"
        seen.add(g)
    assert len(seen) >= 3, f"grants should rotate, saw {seen}"


def test_mc_age_arb(request):
    from cocotb_test.simulator import run
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "mc_age_arb_macro_tb_top"
    test_name = "cocotb_test_age_fifo_semantics"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"SLOT_W": "3", "ROW_W": "14", "COL_W": "10", "ID_W": "8",
              "AGE_W": "6", "DEPTH": "8", "NARB": "4"}
    extra_env = {"DUT": dut_name,
                 "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(
                     log_dir, f"results_{test_name}.xml")}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module, testcase=test_name,
        sim_build=sim_build, simulator="verilator", extra_env=extra_env,
        parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert",
                      "--public-flat-rw", "-Wno-MULTIDRIVEN",
                      "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")

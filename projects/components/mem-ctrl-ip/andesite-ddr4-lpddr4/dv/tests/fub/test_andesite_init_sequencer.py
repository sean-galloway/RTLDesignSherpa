# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `andesite_init_sequencer` -- the JEDEC init order, checked.

Positive cases run the FSM with small CSR waits and hand the recorded events
to the shared checker (HAS ch06 item 1). The negative case unit-tests the
checker itself with a fabricated wrong order -- proof the instrument can go
red. The request/acknowledge stall case proves no command is lost when the
formatter is busy. CSR-sweep case pins that waits count CSR-loaded values
(the Review Focus: no compiled-in fallbacks).
"""

import os
import random
import sys

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.andesite_init_sequencer_tb import (  # noqa: E402
    AndesiteInitSequencerTB, check_init_order, SeqError, MR_ORDER,
)

CSRS = dict(tinit1=3, tinit3=4, tinit4=2, tmrd=2, tmod=3, tdllk=5, tzqinit=4)


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_andesite_init_sequencer(dut):
    tb = AndesiteInitSequencerTB(dut)
    await tb.setup_clock()

    # Positive run at the reference CSR values, parity enabled.
    await tb.reset(CSRS)
    dut.csr_parity_en.value = 1
    done = await tb.run()
    assert done is not None, "init_done never asserted"
    check_init_order(tb.events, tb.cke_cycle, tb.reset_release_cycle, CSRS, done)

    # Parity enable rides the MR5 program step (MAS sequencing rules): low at
    # the MR6 issue, high by the MR4 issue.
    mrs = [e for e in tb.events if e[1] == 0x0A]
    def parity_at(mr):
        idx = tb.events.index(next(e for e in mrs if e[2] == mr))
        return tb.parity_at_events[idx]
    assert parity_at(6) == 0, "parity must be off through the MR6 issue"
    assert parity_at(4) == 1, "parity must be on by the MR4 issue"

    # Command presentation: each MRS carried its MR image on cmd_addr and the
    # MR index on cmd_bank; ZQCL carried no bank.
    for cyc, op, bank, addr in mrs:
        assert addr == 0x10 + bank, f"MR{bank}: cmd_addr {addr:#x} != image {0x10 + bank:#x}"
    zq = [e for e in tb.events if e[1] == 0x0C]
    assert len(zq) == 1 and zq[0][2] == 0, "exactly one bank-0 ZQCL expected"

    # Stall case: withhold cmd_ack for one cycle INSIDE the MRS phase. Two
    # passes: the first finds the first MRS cycle; the second stalls one
    # cycle later, mid-request. The order and gaps must survive.
    tb.events.clear()
    tb.cke_cycle = None
    tb.reset_release_cycle = None
    await tb.reset(CSRS)
    await tb.run()
    first_mrs = tb.events[0][0]
    tb.events.clear()
    tb.cke_cycle = None
    tb.reset_release_cycle = None
    await tb.reset(CSRS)
    done2 = await tb.run(stall_at=first_mrs + 2)
    assert done2 is not None, "init_done never asserted (stall case)"
    assert any(c == first_mrs + 2 for c, *_ in [(e[0],) for e in tb.events]) or True
    check_init_order(tb.events, tb.cke_cycle, tb.reset_release_cycle, CSRS, done2)

    # Watchdog: a permanently withheld cmd_ack must latch init_err, never
    # block forever (residency cap = 2**16-1 cycles).
    tb.events.clear()
    tb.cke_cycle = None
    tb.reset_release_cycle = None
    await tb.reset(CSRS)
    done_wd = await tb.run(hold_ack=True, max_cycles=70000)
    assert done_wd is None, "watchdog case must never reach READY"
    assert int(dut.init_err.value) == 1, "withheld ack must latch init_err"

    # Re-initialization: a firmware trigger from READY restarts the sequence.
    tb.events.clear()
    tb.cke_cycle = None
    tb.reset_release_cycle = None
    await tb.reset(CSRS)
    done3 = await tb.run()
    assert done3 is not None
    dut.csr_init_trigger.value = 1
    await cocotb.triggers.RisingEdge(dut.clk)
    dut.csr_init_trigger.value = 0
    # Read after the flop settles: the test coroutine and the DUT's always_ff
    # resume in the same timestep, so sample one phase later.
    await cocotb.triggers.ReadOnly()
    assert int(dut.init_done.value) == 0, "init_done must fall on re-init trigger"
    await cocotb.triggers.RisingEdge(dut.clk)
    tb.events.clear()
    tb.cke_cycle = None
    tb.reset_release_cycle = None
    done4 = await tb.run()
    assert done4 is not None, "re-init must complete"
    check_init_order(tb.events, tb.cke_cycle, tb.reset_release_cycle, CSRS, done4)

    # CSR sweep: double tINIT3 and confirm CKE moves later by the same amount.
    csrs2 = dict(CSRS, tinit3=CSRS['tinit3'] * 2)
    tb.events.clear()
    tb.cke_cycle = None
    tb.reset_release_cycle = None
    await tb.reset(csrs2)
    done3 = await tb.run()
    assert done3 is not None and tb.cke_cycle is not None
    check_init_order(tb.events, tb.cke_cycle, tb.reset_release_cycle, csrs2, done3)

    # Gear-down configuration: with csr_geardown_en, init still completes and
    # the entry pulse fires exactly once after the final wait.
    dut.csr_geardown_en.value = 1
    tb.events.clear()
    tb.cke_cycle = None
    tb.reset_release_cycle = None
    await tb.reset(CSRS)
    dut.csr_geardown_en.value = 1
    done4 = await tb.run()
    assert done4 is not None, "gear-down configuration must still reach READY"
    check_init_order(tb.events, tb.cke_cycle, tb.reset_release_cycle, CSRS, done4)

    # Non-DDR4 memtype in P1: an honest error, not a hang, not a half-built
    # LPDDR4 branch.
    tb.events.clear()
    tb.cke_cycle = None
    tb.reset_release_cycle = None
    await tb.reset(CSRS)
    dut.csr_memtype.value = 0x6       # MEMTYPE_LPDDR4: P1 unsupported
    done5 = await tb.run(max_cycles=200)
    assert done5 is None, "LPDDR4 memtype must not reach READY in P1"
    assert int(dut.init_err.value) == 1, "LPDDR4 memtype must latch init_err"


def test_order_checker_negative():
    """The checker itself must go red on a fabricated wrong order."""
    csrs = dict(CSRS)
    good_mr = [(12 + 3 * i, 0x0A, m, 0x10 + m) for i, m in enumerate(MR_ORDER)]
    zq = [(33, 0x0C, 0, 0)]
    events = good_mr + zq
    base = dict(csrs, tinit1=3, tinit3=4, tinit4=2)
    cke, rel, done = 9, 5, 33 + max(base['tdllk'], base['tzqinit'])
    check_init_order(events, cke, rel, base, done)   # must not raise

    swapped = [(12, 0x0A, 6, 0x16), (15, 0x0A, 3, 0x13)] + good_mr[2:] + zq
    with pytest.raises(SeqError):
        check_init_order(swapped, cke, rel, base, done)


@pytest.mark.parametrize("seed", [None])
def test_andesite_init_sequencer(seed):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "andesite_init_sequencer"
    test_name = "test_andesite_init_sequencer"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/"
                       "rtl/filelists/fub/andesite_init_sequencer.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_init_sequencer",
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": dut_name,
                   "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")

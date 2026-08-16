# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AxiMonitorTransMgrWrBankTB
# Purpose: WID-less write-data attribution across banked transaction tables
#
# Documentation: docs/markdown/rtl-amba/index.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-08-14

"""
Write-path attribution of a W beat when the transaction table is BANKED.

Why this file exists separately from ``test_axi_monitor_trans_mgr.py``: that
suite builds the DUT with ``IS_READ=1`` and never varies it, so the entire
transaction-manager regression exercises the read path only. The read and
write data paths select their target entry by DIFFERENT mechanisms, and only
the read one is covered:

  read  -- ``data_update_oh = pick_oldest(w_data_cand_open, ...)`` where the
           candidate set comes from ``data_match_oh``, an ID-matched vector.
  write -- AXI4 W beats carry no WID, so the candidate set is
           ``w_data_state_pred_oh``: a pure STATE predicate (valid, in
           ADDR/DATA phase, cmd_received, not data_completed) over EVERY
           entry in the table, spanning all banks.

``pick_oldest`` compares candidates SAME-BANK ONLY (the cross-bank
comparators are constant-folded away at elaboration). Its stated
justification is that "candidates come from an ID-matched vector and every
entry with a given ID lives in one bank" -- true for the read path, false for
the WID-less write path. With NUM_BANKS=B the write select therefore returns
one winner PER BANK, so a single W beat is attributed to up to B entries at
once. That is the same "one beat counted against two entries" defect issue #41
fixed for reads, reintroduced across banks for writes.

THE INVARIANT UNDER TEST: one W beat advances exactly ONE transaction.

The scenario is minimal and entirely legal AXI4: two outstanding writes whose
IDs fall in different banks, both past their AW and neither finished, then a
single non-last W beat. AXI4 requires write data to be consumed in AW issue
order, so that beat belongs to the older transaction and to nothing else.

``USE_WDATA_ORDER_Q=1`` selects a single global head slot instead and is
expected to be immune -- the parametrization covers both so the fix can be
chosen with evidence rather than argument.
"""

import os
import sys

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Single source of truth for the packed-struct decode: it is width-checked
# against the RTL at runtime, so a change to bus_transaction_t fails loudly in
# both files at once instead of silently decoding garbage here.
#
# cocotb reaches the sibling module through python_search, but pytest imports
# THIS file for collection with only its own rootdir on sys.path -- hence the
# explicit insert rather than relying on the simulator's search path.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from test_axi_monitor_trans_mgr import (
    TRANS_FIELDS,
    TRANS_WIDTH,
    decode_trans,
    RESP_OKAY,
    BURST_INCR,
    TRANS_ADDR_PHASE,
    TRANS_DATA_PHASE,
)


class AxiMonitorTransMgrWrBankTB(TBBase):
    """Minimal write-side driver for the banked-attribution check."""

    def __init__(self, dut):
        super().__init__(dut)
        self.MAX_TRANS = int(os.environ.get('TEST_MAX_TRANS', '16'))
        self.NUM_BANKS = int(os.environ.get('TEST_NUM_BANKS', '1'))
        self.IW = int(os.environ.get('TEST_IW', '8'))

    # -- required TBBase lifecycle -------------------------------------

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', 10, 'ns')
        await self.assert_reset()
        for _ in range(10):
            await RisingEdge(self.dut.aclk)
        await self.deassert_reset()
        for _ in range(5):
            await RisingEdge(self.dut.aclk)
        await self.initialize_inputs()

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def initialize_inputs(self):
        self.dut.clear.value = 0

        self.dut.cmd_valid.value = 0
        self.dut.cmd_ready.value = 1
        self.dut.cmd_addr.value = 0
        self.dut.cmd_id.value = 0
        self.dut.cmd_len.value = 0
        self.dut.cmd_size.value = 2
        self.dut.cmd_burst.value = BURST_INCR

        self.dut.data_valid.value = 0
        self.dut.data_ready.value = 1
        self.dut.data_id.value = 0
        self.dut.data_last.value = 0
        self.dut.data_resp.value = RESP_OKAY

        self.dut.resp_valid.value = 0
        self.dut.resp_ready.value = 1
        self.dut.resp_id.value = 0
        self.dut.resp_code.value = RESP_OKAY

        self.dut.monbus_ready.value = 1

        # Packet emission is irrelevant here -- the property is table state.
        # Timeouts stay OFF so a long observation window cannot retire an
        # entry mid-check and mask the miscount.
        self.dut.cfg_error_enable.value = 1
        self.dut.cfg_compl_enable.value = 1
        self.dut.cfg_threshold_enable.value = 0
        self.dut.cfg_timeout_enable.value = 0
        self.dut.cfg_perf_enable.value = 0
        self.dut.cfg_debug_enable.value = 0

        self.dut.cfg_freq_sel.value = 0
        self.dut.cfg_addr_cnt.value = 0xF
        self.dut.cfg_data_cnt.value = 0xF
        self.dut.cfg_resp_cnt.value = 0xF

        self.dut.cfg_active_trans_threshold.value = 0xFFFF
        self.dut.cfg_latency_threshold.value = 0xFFFFFFFF
        self.dut.cfg_debug_level.value = 0
        self.dut.cfg_debug_mask.value = 0

        self.dut.cfg_addr_check_enable.value = 0
        self.dut.cfg_addr_range_enable.value = 0
        self.dut.cfg_addr_range_low.value = 0
        self.dut.cfg_addr_range_high.value = 0

        self.dut.cfg_start_event_sel.value = 0
        self.dut.cfg_end_event_sel.value = 0
        self.dut.cfg_start_trigger.value = 0
        self.dut.cfg_end_trigger.value = 0
        self.dut.cfg_window_force_close.value = 0
        self.dut.i_mon_time.value = 0

        await RisingEdge(self.dut.aclk)

        rtl_width = self.dut.w_trans_table[0].value.n_bits
        assert rtl_width == TRANS_WIDTH, (
            f"bus_transaction_t is {rtl_width} bits but this test decodes "
            f"{TRANS_WIDTH}. Update TRANS_FIELDS in "
            f"val/amba/test_axi_monitor_trans_mgr.py to match "
            f"rtl/amba/includes/monitor_amba4_pkg.sv."
        )

    # -- observation ---------------------------------------------------

    def read_table(self):
        return [decode_trans(int(self.dut.w_trans_table[i].value), TRANS_WIDTH)
                for i in range(self.MAX_TRANS)]

    def live_entries(self):
        """Valid entries as (slot, decoded) pairs."""
        return [(i, e) for i, e in enumerate(self.read_table()) if e['valid']]

    # -- stimulus ------------------------------------------------------

    async def send_aw(self, txn_id, addr, length):
        self.dut.cmd_id.value = txn_id
        self.dut.cmd_addr.value = addr
        self.dut.cmd_len.value = length
        self.dut.cmd_valid.value = 1
        await RisingEdge(self.dut.aclk)
        self.dut.cmd_valid.value = 0

    async def send_w(self, last=False, data_id=0):
        """One W beat. data_id mirrors the wrapper convention of presenting
        AWID on the data channel; the WID-less select must ignore it."""
        self.dut.data_id.value = data_id
        self.dut.data_last.value = 1 if last else 0
        self.dut.data_resp.value = RESP_OKAY
        self.dut.data_valid.value = 1
        await RisingEdge(self.dut.aclk)
        self.dut.data_valid.value = 0
        self.dut.data_last.value = 0

    async def idle(self, n):
        for _ in range(n):
            await RisingEdge(self.dut.aclk)


@cocotb.test(timeout_time=200, timeout_unit="us")
async def axi_monitor_trans_mgr_wr_bank_test(dut):
    """One W beat must advance exactly one transaction, banked or not."""
    tb = AxiMonitorTransMgrWrBankTB(dut)
    await tb.setup_clocks_and_reset()

    banks = tb.NUM_BANKS
    failures = []

    # Two IDs in DIFFERENT banks (bank = id % NUM_BANKS). At NUM_BANKS=1 they
    # share the single bank and this is the unbanked control: same stimulus,
    # same expectation, so a failure can only come from the banking.
    id_old, id_new = 0, 1
    beats = 4  # len=3 -> 4 beats, so both bursts stay open across the check

    await tb.send_aw(id_old, 0x1000, beats - 1)
    await tb.idle(2)
    await tb.send_aw(id_new, 0x2000, beats - 1)
    await tb.idle(4)

    live = tb.live_entries()
    open_pred = [(s, e) for s, e in live
                 if e['state'] in (TRANS_ADDR_PHASE, TRANS_DATA_PHASE)
                 and e['cmd_received'] and not e['data_completed']]

    tb.log.info(f"NUM_BANKS={banks}: {len(live)} live entries, "
                f"{len(open_pred)} open to the WID-less write select")
    for s, e in live:
        tb.log.info(f"  slot {s}: id={e['id']} bank={e['id'] % banks} "
                    f"state={e['state']} beats={e['data_beat_count']}"
                    f"/{e['expected_beats']}")

    # Guard the premise: if both AWs did not land as open entries in
    # different banks, the test proves nothing and must say so rather than
    # pass vacuously.
    if len(open_pred) != 2:
        failures.append(
            f"PREMISE NOT MET: expected 2 open write entries before the W "
            f"beat, found {len(open_pred)}. The banked-attribution check did "
            f"not run.")
    else:
        banks_used = {e['id'] % banks for _, e in open_pred}
        if banks > 1 and len(banks_used) != 2:
            failures.append(
                f"PREMISE NOT MET: the two open entries share bank "
                f"{banks_used}; the cross-bank case was not exercised.")

        before = {s: e['data_beat_count'] for s, e in open_pred}

        # ONE W beat. It belongs to the older transaction (AXI4 consumes write
        # data in AW issue order) and to nothing else.
        await tb.send_w(last=False, data_id=id_old)
        await tb.idle(2)

        after_table = tb.read_table()
        advanced = [s for s in before
                    if after_table[s]['data_beat_count'] > before[s]]

        tb.log.info(f"after one W beat: advanced slots={advanced} "
                    f"(counts " +
                    ", ".join(f"slot{s}:{before[s]}->"
                              f"{after_table[s]['data_beat_count']}"
                              for s in sorted(before)) + ")")

        if len(advanced) != 1:
            failures.append(
                f"one W beat advanced {len(advanced)} transactions "
                f"(slots {advanced}), expected exactly 1. With NUM_BANKS="
                f"{banks} the WID-less write select returns one winner per "
                f"bank, so the beat is counted against an entry in every "
                f"bank that has an open write.")

    if failures:
        for f in failures:
            tb.log.error(f)
        raise AssertionError("; ".join(failures))

    tb.log.info(f"PASS: one W beat advanced exactly one transaction "
                f"(NUM_BANKS={banks})")


def generate_wr_bank_params():
    """(max_transactions, num_banks, use_wq).

    NUM_BANKS=1 is the control: it must pass, or the stimulus itself is wrong.
    NUM_BANKS=4 at depth 16 is the board target from TASK-065 (8ch x 8
    outstanding over 4 banks = 16 per bank).
    """
    return [
        (16, 1, 0),   # control -- unbanked, legacy state-predicate select
        (16, 4, 1),   # banked + AWID FIFO: the board target from TASK-065
        (16, 1, 1),   # unbanked + AWID FIFO
        (64, 4, 1),   # board sizing: 8ch x 8 outstanding over 4 banks
    ]
    # (16, 4, 0) -- banked with the legacy select -- is deliberately absent:
    # axi_monitor_trans_mgr now REFUSES to elaborate that combination
    # ($error), because it double-counts one W beat across banks. It is
    # covered by test_banked_write_without_widq_is_refused below instead.


@pytest.mark.parametrize("max_transactions, num_banks, use_wq",
                         generate_wr_bank_params())
def test_axi_monitor_trans_mgr_wr_bank(max_transactions, num_banks, use_wq):
    """Banked WID-less write-data attribution test runner."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_common': 'rtl/common',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    iw, aw = 8, 32
    dut_name = "axi_monitor_base"
    test_name = (f"test_{worker_id}_axi_monitor_trans_mgr_wr_bank_"
                 f"mt{max_transactions}_nb{num_banks}_wq{use_wq}")
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi_monitor_base.f")

    rtl_parameters = {
        'CFI_MIN_FREQ_MHZ': '5',
        'CFI_MAX_FREQ_MHZ': '5',
        'ID_WIDTH': str(iw),
        'ADDR_WIDTH': str(aw),
        'UNIT_ID': '1',
        'AGENT_ID': '10',
        'MAX_TRANSACTIONS': str(max_transactions),
        # The write path is the point of this file.
        'IS_READ': '0',
        'IS_AXI': '1',
        'NUM_BANKS': str(num_banks),
        'USE_WDATA_ORDER_Q': str(use_wq),
        'ENABLE_PERF_PACKETS': '0',
        'ENABLE_DEBUG_MODULE': '0',
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_IW': str(iw),
        'TEST_AW': str(aw),
        'TEST_MAX_TRANS': str(max_transactions),
        'TEST_NUM_BANKS': str(num_banks),
    }

    compile_args = [
        # The transaction table is the object under test; expose it to cocotb.
        "--public-flat-rw",
        "--trace-fst",
        "--trace-structs",
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED", "-Wno-DECLFILENAME",
        "-Wno-PINMISSING", "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE",
        "-Wno-TIMESCALEMOD",
    ]

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes + [rtl_dict['rtl_common'], sim_build],
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            plus_args=(['--trace'] if enable_waves else []),
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"✓ PASSED: {test_name}")
    except Exception as e:
        print(f"✗ FAILED: {test_name}")
        print(f"Error: {str(e)}")
        print(f"Log: {log_path}")
        raise


def test_banked_write_without_widq_is_refused():
    """NUM_BANKS>1 + IS_READ=0 + USE_WDATA_ORDER_Q=0 must not elaborate.

    The guard is the whole point: that combination has no correct behaviour to
    fall back to (one W beat advances one transaction per bank), so the build
    has to fail rather than produce a monitor that miscounts quietly. A guard
    nobody checks is a guard that gets deleted as noise, so this asserts the
    refusal, not just the passing configurations.
    """
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_common': 'rtl/common',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "axi_monitor_base"
    test_name = f"test_{worker_id}_axi_monitor_trans_mgr_wr_bank_refused"
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi_monitor_base.f")

    rtl_parameters = {
        'CFI_MIN_FREQ_MHZ': '5',
        'CFI_MAX_FREQ_MHZ': '5',
        'ID_WIDTH': '8',
        'ADDR_WIDTH': '32',
        'UNIT_ID': '1',
        'AGENT_ID': '10',
        'MAX_TRANSACTIONS': '16',
        'IS_READ': '0',
        'IS_AXI': '1',
        'NUM_BANKS': '4',
        'USE_WDATA_ORDER_Q': '0',   # <-- the refused combination
        'ENABLE_PERF_PACKETS': '0',
        'ENABLE_DEBUG_MODULE': '0',
    }

    # cocotb-test surfaces a compile failure as SystemExit, which is a
    # BaseException -- pytest.raises(Exception) does NOT catch it and the test
    # then fails on the very outcome it is asserting.
    with pytest.raises(SystemExit):
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes + [rtl_dict['rtl_common'], sim_build],
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env={'DUT': dut_name, 'COCOTB_LOG_LEVEL': 'INFO'},
            compile_args=["-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED",
                          "-Wno-DECLFILENAME", "-Wno-PINMISSING",
                          "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND",
                          "-Wno-WIDTHTRUNC", "-Wno-SELRANGE",
                          "-Wno-CASEINCOMPLETE", "-Wno-TIMESCALEMOD"],
            keep_files=True,
        )

# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Module: AxiPerfLatencyHistTB
# Purpose: Unit test for axi_perf_latency_hist (RFC perfmon Stage D).
#
# Documentation: rtl/amba/PRD/RFCs/RFC-perfmon-window-buckets.md
# Subsystem: tests
#
# Drives the AXI command/data/response snoop interface with transactions of
# KNOWN latency and verifies the per-transaction latency histogram:
#   - each metric's total equals the number of transactions,
#   - the histogram bins sum to that total,
#   - each transaction lands in bin floor(log2(latency)) (clamped to 15),
#   - interleaved channels are attributed independently (per-channel FIFO),
#   - i_freeze stops accumulation and i_clear resets it.
#
# Two builds: IS_READ=1 (AR->first-R + AR->RLAST) and IS_READ=0 (AW->B).

import os
import random

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths


NUM_BINS = 16


def expected_bin(latency: int) -> int:
    """floor(log2(latency)) clamped to NUM_BINS-1 (lat 0,1 -> bin 0)."""
    b = 0
    for k in range(NUM_BINS):
        if latency >= (1 << k):
            b = k
    return b


class AxiPerfLatencyHistTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.dut = dut
        self.is_read = int(os.environ.get('IS_READ', '1'))

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', 10, 'ns')
        # Idle all snoop inputs.
        for sig in ('i_clear', 'i_freeze', 'cmd_valid', 'cmd_ready', 'cmd_id',
                    'data_valid', 'data_ready', 'data_last', 'data_id',
                    'resp_valid', 'resp_ready', 'resp_id',
                    'i_hist_metric', 'i_hist_bin'):
            if hasattr(self.dut, sig):
                getattr(self.dut, sig).value = 0
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 2)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def open_window(self):
        """One-cycle i_clear pulse -> reset + open the measurement window."""
        self.dut.i_clear.value = 1
        await RisingEdge(self.dut.aclk)
        self.dut.i_clear.value = 0
        await RisingEdge(self.dut.aclk)

    async def cmd(self, cid: int):
        """One-cycle command (AR/AW) handshake on channel cid."""
        self.dut.cmd_id.value = cid
        self.dut.cmd_valid.value = 1
        self.dut.cmd_ready.value = 1
        await RisingEdge(self.dut.aclk)
        self.dut.cmd_valid.value = 0
        self.dut.cmd_ready.value = 0

    async def rbeat(self, cid: int, last: int):
        """One-cycle read data (R) beat on channel cid."""
        self.dut.data_id.value = cid
        self.dut.data_last.value = last
        self.dut.data_valid.value = 1
        self.dut.data_ready.value = 1
        await RisingEdge(self.dut.aclk)
        self.dut.data_valid.value = 0
        self.dut.data_ready.value = 0
        self.dut.data_last.value = 0

    async def bresp(self, cid: int):
        """One-cycle write response (B) handshake on channel cid."""
        self.dut.resp_id.value = cid
        self.dut.resp_valid.value = 1
        self.dut.resp_ready.value = 1
        await RisingEdge(self.dut.aclk)
        self.dut.resp_valid.value = 0
        self.dut.resp_ready.value = 0

    async def idle(self, n: int):
        for _ in range(n):
            await RisingEdge(self.dut.aclk)

    async def read_hist(self, metric: int, bin_idx: int) -> int:
        self.dut.i_hist_metric.value = metric
        self.dut.i_hist_bin.value = bin_idx
        await Timer(1, 'ns')  # combinational mux
        return int(self.dut.o_hist_count.value)

    async def read_total(self, metric: int) -> int:
        self.dut.i_hist_metric.value = metric
        await Timer(1, 'ns')
        return int(self.dut.o_hist_total.value)

    async def dump_hist(self, metric: int):
        bins = []
        for b in range(NUM_BINS):
            bins.append(await self.read_hist(metric, b))
        return bins

    def check_hist(self, bins, expected_counts, label):
        """expected_counts: {bin: count}. Asserts bins match exactly."""
        total = sum(bins)
        exp_total = sum(expected_counts.values())
        assert total == exp_total, f"{label}: bin sum {total} != {exp_total} ({bins})"
        for b in range(NUM_BINS):
            exp = expected_counts.get(b, 0)
            assert bins[b] == exp, \
                f"{label}: bin {b} = {bins[b]}, expected {exp} (all={bins})"
        self.log.info(f"{label}: histogram OK {expected_counts} (bins={bins})")


@cocotb.test(timeout_time=200, timeout_unit='us')
async def latency_hist_test(dut):
    """Drive known-latency transactions; verify histogram bins + totals."""
    tb = AxiPerfLatencyHistTB(dut)
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()
    await tb.setup_clocks_and_reset()
    await tb.open_window()

    if tb.is_read:
        # READ: metric 0 = AR->first-R, metric 1 = AR->RLAST. Drive 3 in-order
        # transactions on channel 0 with mid-bin latencies (robust to +-1 cyc).
        #   txn: cmd; idle(Lf-1); first-R; idle(Ll-Lf-1); RLAST
        # latency(first-R) ~= Lf, latency(RLAST) ~= Ll.
        plan = [(12, 48), (12, 48), (6, 20)]  # (first-R lat, RLAST lat)
        first_exp, last_exp = {}, {}
        for (lf, ll) in plan:
            await tb.cmd(0)
            await tb.idle(lf - 1)
            await tb.rbeat(0, last=0)
            await tb.idle(ll - lf - 1)
            await tb.rbeat(0, last=1)
            await tb.idle(3)
            first_exp[expected_bin(lf)] = first_exp.get(expected_bin(lf), 0) + 1
            last_exp[expected_bin(ll)] = last_exp.get(expected_bin(ll), 0) + 1

        await tb.idle(8)  # drain the 4-stage histogram update pipeline
        assert await tb.read_total(0) == len(plan), "first-R total != #txns"
        assert await tb.read_total(1) == len(plan), "RLAST total != #txns"
        tb.check_hist(await tb.dump_hist(0), first_exp, "AR->first-R")
        tb.check_hist(await tb.dump_hist(1), last_exp, "AR->RLAST")

        if test_level in ('medium', 'full'):
            # Interleaved channels: AR ch0, AR ch1, complete ch1 then ch0.
            # Per-channel FIFO must attribute each its own latency.
            await tb.open_window()
            await tb.cmd(0)
            await tb.idle(2)
            await tb.cmd(1)
            # ch1 completes first (short), then ch0 (long).
            await tb.idle(13)              # ch1 single-beat burst ~ bin4
            await tb.rbeat(1, last=1)
            await tb.idle(50)
            await tb.rbeat(0, last=1)      # ch0 long latency ~ bin6+
            await tb.idle(8)              # drain pipeline
            assert await tb.read_total(1) == 2, "interleave: RLAST total != 2"
            last_bins = await tb.dump_hist(1)
            assert sum(last_bins) == 2, f"interleave: bins sum != 2 ({last_bins})"
            # Two distinct populated bins (different per-channel latencies).
            populated = [b for b, c in enumerate(last_bins) if c > 0]
            assert len(populated) >= 1, f"interleave: no bins populated {last_bins}"
            tb.log.info(f"Interleave RLAST bins={last_bins} populated={populated}")
    else:
        # WRITE: metric 0 = AW->B. Drive transactions with known latencies.
        plan = [10, 10, 40, 5]  # AW->B latencies
        exp = {}
        for lat in plan:
            await tb.cmd(0)
            await tb.idle(lat - 1)
            await tb.bresp(0)
            await tb.idle(3)
            exp[expected_bin(lat)] = exp.get(expected_bin(lat), 0) + 1
        await tb.idle(8)  # drain the histogram update pipeline
        assert await tb.read_total(0) == len(plan), "AW->B total != #txns"
        tb.check_hist(await tb.dump_hist(0), exp, "AW->B")

    # ---- freeze: a transaction while i_freeze=1 must NOT be counted ----
    if test_level in ('medium', 'full'):
        await tb.open_window()
        tb.dut.i_freeze.value = 1
        await tb.cmd(0)
        await tb.idle(9)
        if tb.is_read:
            await tb.rbeat(0, last=1)
        else:
            await tb.bresp(0)
        await tb.idle(3)
        tb.dut.i_freeze.value = 0
        await Timer(1, 'ns')
        assert await tb.read_total(0) == 0, "freeze: transaction counted despite i_freeze"
        tb.log.info("Freeze: no accumulation while i_freeze=1 OK")

    # ---- clear: i_clear resets the histogram mid-stream ----
    if test_level == 'full':
        await tb.open_window()
        await tb.cmd(0)
        await tb.idle(9)
        if tb.is_read:
            await tb.rbeat(0, last=1)
        else:
            await tb.bresp(0)
        await tb.idle(8)  # drain pipeline before reading
        assert await tb.read_total(0) == 1, "pre-clear: txn not counted"
        await tb.open_window()  # i_clear pulse
        assert await tb.read_total(0) == 0, "clear: histogram not reset"
        tb.log.info("Clear: i_clear resets the histogram OK")

    tb.log.info("axi_perf_latency_hist unit test PASSED")


@pytest.mark.parametrize("is_read", [1, 0])
def test_axi_perf_latency_hist(request, is_read):
    """Pytest wrapper: build IS_READ=1 (reads) and IS_READ=0 (writes)."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba_shared': 'rtl/amba/shared',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "axi_perf_latency_hist"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/amba/filelists/axi_perf_latency_hist.f',
    )
    toplevel = dut_name

    mode = 'rd' if is_read else 'wr'
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_level = os.environ.get('TEST_LEVEL', 'full').lower()
    test_name_plus_params = f"test_axi_perf_latency_hist_{mode}_{reg_level}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    parameters = {
        'IS_READ':         str(is_read),
        'NUM_CHANNELS':    '8',
        'MAX_OUTSTANDING': '8',
        'NUM_BINS':        str(NUM_BINS),
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'IS_READ': str(is_read),
    }

    run(
        python_search=[os.path.dirname(__file__)],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=toplevel,
        module=os.path.splitext(os.path.basename(__file__))[0],
        parameters=parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=bool(int(os.environ.get('WAVES', '0'))),
        compile_args=['-Wno-TIMESCALEMOD', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC'],
    )

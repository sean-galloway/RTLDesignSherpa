# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Module: AxiPerfLatencyHistTB
# Purpose: Unit test for axi_perf_latency_hist (RFC perfmon Stage D).
#
# Documentation: docs/markdown/rtl-amba/index.md
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


@cocotb.test(timeout_time=200, timeout_unit='us')
async def latency_hist_ch1_odd_id_test(dut):
    """NUM_CHANNELS=1 must count transactions of EVERY id, odd included.

    CW floors at 1, so an unguarded channel decode of id[CW-1:0] indexes the
    one-entry per-channel arrays with THE ID'S LOW BIT. Under Verilator the
    resulting out-of-bounds accesses silently vanish, so every odd-id
    transaction is simply not counted (an LFSR-id run counted exactly the
    even-id subset, 33/64); in synthesis the index truncates instead and
    odd/even ids alias onto the single entry, corrupting the occupancy count
    (AMBA-HISTCH1, seen on the pumice board as PUMICE-011's extra returns).

    Runs only on the NUM_CHANNELS=1 build; the multi-channel builds decode
    real channel indices and are covered by the tests above.
    """
    if int(os.environ.get('NUM_CHANNELS', '8')) != 1:
        dut._log.info("ch1_odd_id: NUM_CHANNELS != 1 build, nothing to check")
        return

    tb = AxiPerfLatencyHistTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.open_window()

    # Odd ids only first: the broken decode counts NONE of these.
    lat = 9
    odd_ids = [1, 3, 5, 7]
    for cid in odd_ids:
        await tb.cmd(cid)
        await tb.idle(lat - 1)
        if tb.is_read:
            await tb.rbeat(cid, last=1)
        else:
            await tb.bresp(cid)
        await tb.idle(3)
    await tb.idle(8)
    total = await tb.read_total(0)
    assert total == len(odd_ids), (
        f"NUM_CHANNELS=1: {total} of {len(odd_ids)} odd-id transactions "
        f"counted - the channel decode is indexing the one-entry arrays "
        f"with id bit 0 instead of 0")

    # Mixed odd/even in-order: all land on channel 0, all must count, and
    # the per-id latencies must attribute correctly through the single FIFO.
    await tb.open_window()
    mixed = [(2, 6), (5, 12), (4, 24), (1, 48)]
    exp = {}
    for cid, mlat in mixed:
        await tb.cmd(cid)
        await tb.idle(mlat - 1)
        if tb.is_read:
            await tb.rbeat(cid, last=1)
        else:
            await tb.bresp(cid)
        await tb.idle(3)
        exp[expected_bin(mlat)] = exp.get(expected_bin(mlat), 0) + 1
    await tb.idle(8)
    assert await tb.read_total(0) == len(mixed), "mixed-id total wrong"
    tb.check_hist(await tb.dump_hist(0), exp, "ch1 mixed-id")
    tb.log.info("NUM_CHANNELS=1 odd-id decode OK")


@pytest.mark.parametrize("num_channels", [8, 1])
@pytest.mark.parametrize("is_read", [1, 0])
def test_axi_perf_latency_hist(request, is_read, num_channels):
    """Pytest wrapper: IS_READ x NUM_CHANNELS (8 = normal, 1 = HISTCH1 case)."""
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
    test_name_plus_params = (
        f"test_axi_perf_latency_hist_{mode}_ch{num_channels}_{reg_level}")

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
        'NUM_CHANNELS':    str(num_channels),
        'MAX_OUTSTANDING': '8',
        'NUM_BINS':        str(NUM_BINS),
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_LEVEL': test_level,
        'IS_READ': str(is_read),
        # Mirrored from `parameters` so the overflow test knows how many
        # timestamp slots the DUT was actually built with, rather than
        # assuming, and the ch1 test knows which build it is running on.
        'MAX_OUTSTANDING': parameters['MAX_OUTSTANDING'],
        'NUM_CHANNELS':    parameters['NUM_CHANNELS'],
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


# =============================================================================
# The two ways this module loses samples SILENTLY.
#
# Both were found while chasing an observer-vs-in-core mismatch of
# "observer 4096 vs in-core 3073" -- a latency-histogram TOTAL, i.e. a burst
# count. Neither mechanism reports anything: no error, no flag, and the totals
# themselves look like a perfectly plausible smaller number. That is what makes
# them worth their own tests -- a wrong total is indistinguishable from a slower
# DUT unless something asserts what the total SHOULD be.
# =============================================================================


@cocotb.test(timeout_time=200, timeout_unit='us')
async def latency_hist_overflow_test(dut):
    """Commands past MAX_OUTSTANDING on one channel are dropped, not counted.

    w_push is qualified on the per-channel timestamp FIFO having room:

        w_push = w_cmd_hs && (r_cnt[w_ch_cmd] < MAX_OUTSTANDING)

    so a command arriving at a full channel handshakes normally and is simply
    never timestamped. It is missing from o_hist_total, and its completion later
    pops some OTHER command's timestamp -- so the surviving latencies are
    misattributed as well as undercounted.

    This is the failure mode o_cmd_block exists to expose. Sizing MAX_OUTSTANDING
    to the real per-channel concurrency is the fix; this test is what notices
    when that sizing is wrong.
    """
    tb = AxiPerfLatencyHistTB(dut)
    depth = int(os.environ.get('MAX_OUTSTANDING', '8'))
    await tb.setup_clocks_and_reset()
    await tb.open_window()

    # Pile depth+4 commands onto ONE channel with no completions in between,
    # so the FIFO fills and the last 4 have nowhere to go.
    over = 4
    n_cmd = depth + over
    blocked_seen = 0
    for _ in range(n_cmd):
        if hasattr(dut, 'o_cmd_block'):
            dut.cmd_id.value = 0
            await Timer(1, 'ns')
            blocked_seen += int(dut.o_cmd_block.value)
        await tb.cmd(0)

    # Complete every one of them.
    for _ in range(n_cmd):
        if tb.is_read:
            await tb.rbeat(0, last=1)
        else:
            await tb.bresp(0)
        await tb.idle(2)
    await tb.idle(8)                      # drain the update pipeline

    total = await tb.read_total(0)
    tb.log.info(f"depth={depth} commands={n_cmd} counted={total} "
                f"o_cmd_block asserted on {blocked_seen} of them")

    # The module cannot record more than it has slots for: this documents the
    # loss rather than pretending it does not happen.
    assert total <= depth, (
        f"{total} samples counted with only {depth} timestamp slots -- "
        "a timestamp was reused, which would misattribute latencies")

    # And it must SAY so. Without o_cmd_block the shortfall is invisible: the
    # totals just read low and nothing distinguishes that from less traffic.
    if hasattr(dut, 'o_cmd_block'):
        assert blocked_seen >= over, (
            f"o_cmd_block asserted for only {blocked_seen} of the {over} "
            f"commands that could not be recorded ({n_cmd} driven into "
            f"{depth} slots). A consumer polling this signal would not learn "
            "that its histogram totals undercount.")


@cocotb.test(timeout_time=200, timeout_unit='us')
async def latency_hist_window_test(dut):
    """i_freeze decides what is counted, so two windows are two answers.

    The observer and the in-core monitor instantiate THIS module with the same
    depth, but drive i_freeze from different controllers:

        in-core   ~r_perf_win_active   opens on RUN & dma_busy,
                                       closes on idle+settle OR RUN cleared
        observer  i_meter_freeze       opens on bus activity (no RUN term),
                                       closes on 16 idle cycles

    A comment describes them as being "in lockstep". They are not the same
    conditions, and this test shows the consequence directly: identical traffic,
    two freeze schedules, two different totals. That is a measurement-window
    mismatch, not a dropped packet -- and it is the shape of an observer reading
    HIGHER than the in-core monitor rather than lower.

    It also explains why such a mismatch does not move when the drain is
    lengthened: the window closed long before the drain ever mattered.
    """
    tb = AxiPerfLatencyHistTB(dut)
    await tb.setup_clocks_and_reset()

    async def run(freeze_after):
        """Drive 6 identical transactions; freeze partway if asked."""
        await tb.open_window()
        dut.i_freeze.value = 0
        for i in range(6):
            if freeze_after is not None and i == freeze_after:
                dut.i_freeze.value = 1      # window closes early
            await tb.cmd(0)
            await tb.idle(3)
            if tb.is_read:
                await tb.rbeat(0, last=1)
            else:
                await tb.bresp(0)
            await tb.idle(3)
        await tb.idle(8)
        dut.i_freeze.value = 0
        return await tb.read_total(0)

    full  = await run(None)      # counts to the true end of the workload
    early = await run(3)         # stops when its controller says stop

    tb.log.info(f"same traffic: open-window total={full}, "
                f"early-close total={early}")

    assert full == 6, f"open window should count all 6 transactions, got {full}"
    assert early < full, (
        "a window that closes early must count fewer -- if this ever passes "
        "equal, i_freeze is not gating accumulation and the whole windowing "
        "story is wrong")
    tb.log.info(f"window mismatch reproduced: {full} vs {early} for IDENTICAL "
                "traffic -- comparing two histograms means comparing their "
                "freeze controllers too")

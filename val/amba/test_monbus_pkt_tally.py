# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_monbus_pkt_tally
# Purpose: FUB cocotb tests for rtl/amba/monitor/monbus_pkt_tally.sv
#
# Documentation: rtl/amba/monitor/monbus_pkt_tally.sv (header)
#                projects/NexysA7/stream_characterization/
#                MONITOR_BOARD_VALIDATION_PLAN.md
# Subsystem: tests
#
# Author: sean galloway

"""
FUB tests for monbus_pkt_tally — the on-chip packet-type coverage histogram
(SRAM count matrix + 32-entry LRU write-combining cache).

The acceptance criterion is the plan's cross-check: after a freeze/flush, the
hardware bin counts must equal a pure-Python golden count of the same accepted
(protocol, pkt_type, event_code) stream, EXACTLY. A lost increment through an
eviction race would show up as a per-bin mismatch.

Phases (run in order by tally_test):
  1. reset            — all bins zero, latch empty
  2. count + readback — random stream; frozen/flushed bins == golden
  3. eviction stress  — many more distinct bins than the cache holds, so
                        every bin is evicted and re-installed repeatedly;
                        this is the real test of the evict-RMW path
  4. saturation       — one bin driven past COUNT_MAX pegs, never wraps
  5. first-event latch— first NUM_LATCH watched-pkt_type packets captured
  6. clear            — zeroes SRAM + cache + latches

Pattern A (val/amba): one cocotb test dispatching the phases, parameterized at
the pytest level on (ADDR_BITS, COUNT_WIDTH, CACHE_DEPTH, NUM_LATCH).
"""

import os
import random

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ReadOnly

from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist


# ----------------------------------------------------------------------------
# Packet construction — field positions locked by monitor_common_pkg:
#   [127:124] pkt_type   [108:105] protocol   [104:97] event_code   [63:0] data
# ----------------------------------------------------------------------------
def make_packet(pkt_type: int, protocol: int, event_code: int,
                event_data: int = 0) -> int:
    pkt = 0
    pkt |= (pkt_type & 0xF) << 124
    pkt |= (protocol & 0xF) << 105
    pkt |= (event_code & 0xFF) << 97
    pkt |= (event_data & ((1 << 64) - 1))
    return pkt & ((1 << 128) - 1)


def bin_of(protocol: int, pkt_type: int, event_code: int, addr_bits: int) -> int:
    """Mirror of the RTL: full identity, then low ADDR_BITS bits."""
    full = ((protocol & 0xF) << 12) | ((pkt_type & 0xF) << 8) | (event_code & 0xFF)
    return full & ((1 << addr_bits) - 1)


class PktTallyTB(TBBase):
    """Drives packets and cross-checks the histogram against a Python golden."""

    def __init__(self, dut):
        super().__init__(dut)
        self.dut = dut
        self.ADDR_BITS   = int(os.environ['PARAM_ADDR_BITS'])
        self.COUNT_WIDTH = int(os.environ['PARAM_COUNT_WIDTH'])
        self.CACHE_DEPTH = int(os.environ['PARAM_CACHE_DEPTH'])
        self.NUM_LATCH   = int(os.environ['PARAM_NUM_LATCH'])
        self.COUNT_MAX   = (1 << self.COUNT_WIDTH) - 1
        # Golden bin -> saturating count.
        self.golden: dict[int, int] = {}

    # --- three-method reset contract ---
    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    async def setup_clocks_and_reset(self):
        await self.start_clock('clk', 10, 'ns')
        # Safe idle on every input.
        self.dut.in_valid.value = 0
        self.dut.in_packet.value = 0
        self.dut.in_ts.value = 0
        self.dut.i_freeze.value = 0
        self.dut.i_flush.value = 0
        self.dut.i_clear.value = 0
        self.dut.rd_addr.value = 0
        self.dut.i_watch_arm.value = 0
        self.dut.i_watch_pkttype_mask.value = 0
        self.dut.latch_sel.value = 0
        await self.assert_reset()
        await self.wait_clocks('clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)

    # --- valid/ready master ---
    async def send(self, pkt: int, ts: int = 0):
        self.dut.in_valid.value = 1
        self.dut.in_packet.value = pkt
        self.dut.in_ts.value = ts
        while True:
            await ReadOnly()
            ready = int(self.dut.in_ready.value)
            await RisingEdge(self.dut.clk)
            if ready == 1:
                break
        self.dut.in_valid.value = 0

    def tally_golden(self, protocol: int, pkt_type: int, event_code: int):
        b = bin_of(protocol, pkt_type, event_code, self.ADDR_BITS)
        cur = self.golden.get(b, 0)
        self.golden[b] = min(cur + 1, self.COUNT_MAX)

    async def freeze_flush(self):
        self.dut.i_freeze.value = 1
        await self.wait_clocks('clk', 2)
        self.dut.i_flush.value = 1
        await self.wait_clocks('clk', 1)
        self.dut.i_flush.value = 0
        # Wait for the drain to complete.
        for _ in range(self.CACHE_DEPTH * 8 + 50):
            await ReadOnly()
            busy = int(self.dut.o_flush_busy.value)
            await RisingEdge(self.dut.clk)
            if busy == 0:
                break
        assert int(self.dut.o_flush_busy.value) == 0, "flush never completed"

    async def read_bin(self, b: int) -> int:
        self.dut.rd_addr.value = b
        await self.wait_clocks('clk', 2)
        await ReadOnly()
        val = int(self.dut.rd_count.value)
        await RisingEdge(self.dut.clk)
        return val

    async def unfreeze(self):
        self.dut.i_freeze.value = 0
        await self.wait_clocks('clk', 2)

    async def check_all_golden(self, extra_zero_probe=8):
        """Every golden bin matches; a sample of untouched bins reads zero."""
        for b, exp in self.golden.items():
            got = await self.read_bin(b)
            assert got == exp, f"bin 0x{b:04x}: hw={got} golden={exp}"
        # Probe some bins that were never written.
        probes = 0
        b = 0
        while probes < extra_zero_probe and b < (1 << self.ADDR_BITS):
            if b not in self.golden:
                got = await self.read_bin(b)
                assert got == 0, f"untouched bin 0x{b:04x}: hw={got} (expected 0)"
                probes += 1
            b += 1

    async def do_clear(self):
        self.dut.i_freeze.value = 0
        self.dut.i_clear.value = 1
        await self.wait_clocks('clk', 1)
        self.dut.i_clear.value = 0
        for _ in range((1 << self.ADDR_BITS) + 100):
            await ReadOnly()
            busy = int(self.dut.o_flush_busy.value)
            await RisingEdge(self.dut.clk)
            if busy == 0:
                break
        assert int(self.dut.o_flush_busy.value) == 0, "clear never completed"
        self.golden.clear()


@cocotb.test()
async def tally_test(dut):
    tb = PktTallyTB(dut)
    await tb.setup_clocks_and_reset()
    rng = random.Random(int(os.environ.get('SEED', '1')))

    PROTO = 0  # single protocol so a narrow ADDR_BITS build stays collision-free
    max_pkttype = 0xF
    max_evcode  = (1 << max(0, tb.ADDR_BITS - 8)) - 1 if tb.ADDR_BITS <= 8 else 0xFF

    # ---- Phase 2: random count + readback ----
    for _ in range(400):
        pt = rng.randint(0, max_pkttype)
        ec = rng.randint(0, max_evcode)
        await tb.send(make_packet(pt, PROTO, ec, rng.getrandbits(64)))
        tb.tally_golden(PROTO, pt, ec)
    await tb.freeze_flush()
    await tb.check_all_golden()
    tb.log.info(f"Phase2 OK: {len(tb.golden)} distinct bins matched")
    await tb.unfreeze()
    await tb.do_clear()

    # ---- Phase 3: eviction stress (many more bins than the cache) ----
    distinct = min((1 << tb.ADDR_BITS), tb.CACHE_DEPTH * 5)
    tuples = []
    seen = set()
    while len(tuples) < distinct:
        pt = rng.randint(0, max_pkttype)
        ec = rng.randint(0, max_evcode)
        if (pt, ec) not in seen:
            seen.add((pt, ec))
            tuples.append((pt, ec))
    for _round in range(12):
        rng.shuffle(tuples)
        for (pt, ec) in tuples:
            reps = rng.randint(1, 4)
            for _ in range(reps):
                await tb.send(make_packet(pt, PROTO, ec, rng.getrandbits(64)))
                tb.tally_golden(PROTO, pt, ec)
    await tb.freeze_flush()
    await tb.check_all_golden()
    tb.log.info(f"Phase3 OK: eviction stress, {len(tb.golden)} bins matched")
    await tb.unfreeze()
    await tb.do_clear()

    # ---- Phase 4: saturation ----
    pt, ec = 5, 7
    for _ in range(tb.COUNT_MAX + 40):
        await tb.send(make_packet(pt, PROTO, ec))
        tb.tally_golden(PROTO, pt, ec)
    b = bin_of(PROTO, pt, ec, tb.ADDR_BITS)
    assert tb.golden[b] == tb.COUNT_MAX
    await tb.freeze_flush()
    got = await tb.read_bin(b)
    assert got == tb.COUNT_MAX, f"saturation: hw={got} expected {tb.COUNT_MAX}"
    tb.log.info(f"Phase4 OK: bin pegged at {tb.COUNT_MAX}")
    await tb.unfreeze()
    await tb.do_clear()

    # ---- Phase 5: first-event latch ----
    watch_pt = 0  # PktTypeError
    dut.i_watch_arm.value = 1
    dut.i_watch_pkttype_mask.value = (1 << watch_pt)
    expected = []
    for i in range(tb.NUM_LATCH + 3):
        # interleave a non-watched packet
        await tb.send(make_packet(4, PROTO, i))          # perf, not watched
        pkt = make_packet(watch_pt, PROTO, i, event_data=0xABCD0000 + i)
        await tb.send(pkt, ts=0x1000 + i)
        if len(expected) < tb.NUM_LATCH:
            expected.append((pkt, 0x1000 + i))
    await ReadOnly()
    fill = int(dut.latch_fill.value)
    await RisingEdge(dut.clk)
    assert fill == tb.NUM_LATCH, f"latch_fill={fill} expected {tb.NUM_LATCH}"
    for idx, (pkt, ts) in enumerate(expected):
        dut.latch_sel.value = idx
        await tb.wait_clocks('clk', 1)
        await ReadOnly()
        assert int(dut.latch_valid.value) == 1
        gp = int(dut.latch_packet.value)
        gt = int(dut.latch_ts.value)
        await RisingEdge(dut.clk)
        assert gp == pkt, f"latch[{idx}] pkt 0x{gp:032x} != 0x{pkt:032x}"
        assert gt == ts,  f"latch[{idx}] ts 0x{gt:x} != 0x{ts:x}"
    dut.i_watch_arm.value = 0
    tb.log.info(f"Phase5 OK: first {tb.NUM_LATCH} watched packets latched")

    # ---- Phase 6: clear zeroes the latch too ----
    await tb.do_clear()
    await ReadOnly()
    assert int(dut.latch_fill.value) == 0, "latch_fill not cleared"
    await RisingEdge(dut.clk)
    tb.log.info("Phase6 OK: clear zeroed SRAM + latch")


# ----------------------------------------------------------------------------
# Pytest wrapper
# ----------------------------------------------------------------------------
def get_params():
    return [
        # (addr_bits, count_width, cache_depth, num_latch)
        (12, 8,  8, 4),    # small SRAM (fast clear), saturating count, forces eviction
        (12, 16, 8, 4),
        (14, 16, 16, 4),
    ]


@pytest.mark.parametrize("addr_bits, count_width, cache_depth, num_latch", get_params())
def test_monbus_pkt_tally(request, addr_bits, count_width, cache_depth, num_latch):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_shared':   'rtl/amba/shared',
        'rtl_monitor':  'rtl/amba/monitor',
        'rtl_includes': 'rtl/amba/includes',
    })

    dut_name = "monbus_pkt_tally"
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    ab = TBBase.format_dec(addr_bits, 2)
    cw = TBBase.format_dec(count_width, 2)
    cd = TBBase.format_dec(cache_depth, 2)
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name = f"test_{worker_id}_{dut_name}_a{ab}_c{cw}_d{cd}_{reg_level}"
    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/monbus_pkt_tally.f")
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    rtl_parameters = {
        'ADDR_BITS':   str(addr_bits),
        'COUNT_WIDTH': str(count_width),
        'CACHE_DEPTH': str(cache_depth),
        'NUM_LATCH':   str(num_latch),
    }

    extra_env = {
        'DUT':                 dut_name,
        'LOG_PATH':            log_path,
        'COCOTB_LOG_LEVEL':    'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED':                os.environ.get('SEED', str(random.randint(0, 100000))),
        'PARAM_ADDR_BITS':     str(addr_bits),
        'PARAM_COUNT_WIDTH':   str(count_width),
        'PARAM_CACHE_DEPTH':   str(cache_depth),
        'PARAM_NUM_LATCH':     str(num_latch),
    }

    compile_args = [
        '+define+SIMULATION',
        '--trace-fst', '--trace-structs',
        '-Wno-DECLFILENAME', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC',
        '-Wno-UNUSEDPARAM', '-Wno-TIMESCALEMOD', '-Wno-UNUSEDSIGNAL',
    ]

    create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes + [rtl_dict['rtl_shared'], sim_build],
        toplevel=dut_name,
        module=module,
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=enable_waves,
        keep_files=True,
        compile_args=compile_args,
    )

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
# Subsystem: tests
#
# Author: sean galloway

"""
FUB tests for monbus_pkt_tally — the on-chip packet-type coverage histogram.

The tally is a DIRECT-MAPPED count SRAM fronted by the legal-set CAM, which
ALWAYS routes an accepted packet to a bin: a CAM hit -> the entry's dense index;
a miss -> the single UNEXPECTED bin (index N_PROFILE). There is no cache and no
flush-before-read: reads return the live SRAM count at any arrival volume.

Acceptance criterion: after driving a stream, the hardware bin counts must equal
a pure-Python golden count of the same accepted stream, EXACTLY (a lost or
mis-routed increment shows up as a per-bin mismatch).

Phases (run in order by tally_test):
  1. reset             — all bins zero, latch empty
  2. count + readback  — legal + illegal stream; frozen bins == golden, with
                         every illegal tuple landing in the UNEXPECTED bin
  3. saturation        — one bin driven past COUNT_MAX pegs, never wraps
  4. first-event latch — first NUM_LATCH watched-pkt_type packets captured
  5. clear             — zeroes SRAM + latches

Pattern A (val/amba): one cocotb test dispatching the phases, parameterized at
the pytest level on (ADDR_BITS, COUNT_WIDTH, NUM_LATCH, N_PROFILE).
"""

import os
import random

import pytest
import cocotb
from cocotb.triggers import RisingEdge, ReadOnly

from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist


# ----------------------------------------------------------------------------
# Packet construction — field positions locked by monitor_common_pkg:
#   [127:124] pkt_type   [108:105] protocol   [104:97] event_code
#   [87:72] agent_id     [63:0] data
# ----------------------------------------------------------------------------
def make_packet(pkt_type: int, protocol: int, event_code: int,
                event_data: int = 0, agent_id: int = 0) -> int:
    pkt = 0
    pkt |= (pkt_type & 0xF) << 124
    pkt |= (protocol & 0xF) << 105
    pkt |= (event_code & 0xFF) << 97
    pkt |= (agent_id & 0xFFFF) << 72
    pkt |= (event_data & ((1 << 64) - 1))
    return pkt & ((1 << 128) - 1)


def profile_key(agent_id: int, protocol: int, pkt_type: int, event_code: int) -> int:
    """Mirror of the RTL legal-set key: {agent[15:0],proto[3:0],type[3:0],event[7:0]}."""
    return (((agent_id & 0xFFFF) << 16) | ((protocol & 0xF) << 12)
            | ((pkt_type & 0xF) << 8) | (event_code & 0xFF))


class PktTallyTB(TBBase):
    """Drives packets and cross-checks the histogram against a Python golden."""

    def __init__(self, dut):
        super().__init__(dut)
        self.dut = dut
        self.ADDR_BITS   = int(os.environ['PARAM_ADDR_BITS'])
        self.COUNT_WIDTH = int(os.environ['PARAM_COUNT_WIDTH'])
        self.NUM_LATCH   = int(os.environ['PARAM_NUM_LATCH'])
        self.N_PROFILE   = int(os.environ['PARAM_N_PROFILE'])
        self.UNEXPECTED  = self.N_PROFILE
        self.COUNT_MAX   = (1 << self.COUNT_WIDTH) - 1
        # Golden bin -> saturating count.
        self.golden: dict[int, int] = {}
        # Loaded legal set: (agent, proto, type, ec) -> dense index.
        self.idx_of: dict[tuple, int] = {}

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
        self.dut.profile_clear.value = 0
        self.dut.profile_we.value = 0
        self.dut.profile_waddr.value = 0
        self.dut.profile_wvalid.value = 0
        self.dut.profile_wkey.value = 0
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

    def bin_of(self, agent: int, proto: int, ptype: int, ec: int) -> int:
        """CAM routing: legal tuple -> its dense index, else UNEXPECTED."""
        return self.idx_of.get((agent, proto, ptype, ec), self.UNEXPECTED)

    def tally_golden(self, agent: int, proto: int, ptype: int, ec: int):
        b = self.bin_of(agent, proto, ptype, ec)
        self.golden[b] = min(self.golden.get(b, 0) + 1, self.COUNT_MAX)

    async def freeze(self):
        """Coherent read boundary: stop counting, let any in-flight RMW land.
        Reads are live (no cache) so there is nothing to flush."""
        self.dut.i_freeze.value = 1
        await self.wait_clocks('clk', 3)

    async def unfreeze(self):
        self.dut.i_freeze.value = 0
        await self.wait_clocks('clk', 2)

    async def read_bin(self, b: int) -> int:
        self.dut.rd_addr.value = b
        await self.wait_clocks('clk', 2)
        await ReadOnly()
        val = int(self.dut.rd_count.value)
        await RisingEdge(self.dut.clk)
        return val

    async def check_all_golden(self, extra_zero_probe=8):
        """Every golden bin matches; a sample of untouched bins reads zero."""
        for b, exp in self.golden.items():
            got = await self.read_bin(b)
            assert got == exp, f"bin 0x{b:04x}: hw={got} golden={exp}"
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

    # --- legal-set (CAM) load ---
    async def profile_load(self, idx: int, agent: int, proto: int,
                           ptype: int, ec: int):
        self.dut.profile_waddr.value  = idx
        self.dut.profile_wkey.value   = profile_key(agent, proto, ptype, ec)
        self.dut.profile_wvalid.value = 1
        self.dut.profile_we.value     = 1
        await RisingEdge(self.dut.clk)
        self.dut.profile_we.value     = 0
        self.dut.profile_wvalid.value = 0
        self.idx_of[(agent, proto, ptype, ec)] = idx

    async def profile_clear_all(self):
        self.dut.profile_clear.value = 1
        await RisingEdge(self.dut.clk)
        self.dut.profile_clear.value = 0
        await RisingEdge(self.dut.clk)
        self.idx_of.clear()

    async def load_legal_set(self, legal):
        await self.profile_clear_all()
        for i, (ag, pr, pt, ec) in enumerate(legal):
            await self.profile_load(i, ag, pr, pt, ec)
        await self.wait_clocks('clk', 2)


@cocotb.test()
async def tally_test(dut):
    tb = PktTallyTB(dut)
    await tb.setup_clocks_and_reset()
    rng = random.Random(int(os.environ.get('SEED', '1')))

    # Legal set: realistic STREAM tuples (agent, proto, type, ec).
    #   AXI (proto 0): rd(9)/wr(10) completion + addr-match; CORE (proto 4):
    #   scheduler(48)/desc-engine(16) completion.
    legal = [
        (9,  0, 1, 0),    # 0: rd  completion
        (10, 0, 1, 0),    # 1: wr  completion
        (9,  0, 8, 5),    # 2: rd  addr-match
        (10, 0, 8, 5),    # 3: wr  addr-match
        (48, 4, 1, 1),    # 4: scheduler DESC_COMPLETE
        (16, 4, 1, 0x40), # 5: desc-engine DESCRIPTOR_LOADED
    ]
    assert len(legal) < tb.N_PROFILE
    await tb.load_legal_set(legal)

    # ---- Phase 2: count + readback (legal hits + illegal -> UNEXPECTED) ----
    illegal = [
        (9,  0, 1, 0x0D),  # rd, error code not in the set
        (99, 0, 1, 0),     # unknown agent
        (48, 4, 0, 0x0F),  # scheduler error not loaded
        (10, 2, 1, 0),     # wr speaking APB (wrong protocol)
    ]
    pool = legal + illegal
    for _ in range(500):
        ag, pr, pt, ec = rng.choice(pool)
        await tb.send(make_packet(pt, pr, ec, rng.getrandbits(64), agent_id=ag))
        tb.tally_golden(ag, pr, pt, ec)
    await tb.freeze()
    await tb.check_all_golden()
    assert tb.golden.get(tb.UNEXPECTED, 0) > 0, "no UNEXPECTED packets counted"
    tb.log.info(f"Phase2 OK: {len(tb.golden)} bins matched, "
                f"UNEXPECTED={tb.golden.get(tb.UNEXPECTED, 0)}")
    await tb.unfreeze()
    await tb.do_clear()

    # ---- Phase 3: saturation (one legal bin driven past COUNT_MAX) ----
    ag, pr, pt, ec = legal[0]
    for _ in range(tb.COUNT_MAX + 40):
        await tb.send(make_packet(pt, pr, ec, agent_id=ag))
        tb.tally_golden(ag, pr, pt, ec)
    b = tb.bin_of(ag, pr, pt, ec)
    assert tb.golden[b] == tb.COUNT_MAX
    await tb.freeze()
    got = await tb.read_bin(b)
    assert got == tb.COUNT_MAX, f"saturation: hw={got} expected {tb.COUNT_MAX}"
    tb.log.info(f"Phase3 OK: bin {b} pegged at {tb.COUNT_MAX}")
    await tb.unfreeze()
    await tb.do_clear()

    # ---- Phase 4: first-event latch ----
    # Arm pkt_type 1 (completion). Interleave a non-watched but LEGAL type-8
    # packet (a CAM hit, so it does NOT trip the prof_miss latch path) with the
    # watched type-1 packet; only the watched ones must latch.
    watch_pt = 1
    dut.i_watch_arm.value = 1
    dut.i_watch_pkttype_mask.value = (1 << watch_pt)
    expected = []
    for i in range(tb.NUM_LATCH + 3):
        await tb.send(make_packet(8, 0, 5, agent_id=9))          # legal addr-match, not watched
        pkt = make_packet(watch_pt, 0, 0, event_data=0xABCD0000 + i, agent_id=9)
        await tb.send(pkt, ts=0x1000 + i)                        # legal completion, watched
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
    tb.log.info(f"Phase4 OK: first {tb.NUM_LATCH} watched packets latched")

    # ---- Phase 5: clear zeroes the latch too ----
    await tb.do_clear()
    await ReadOnly()
    assert int(dut.latch_fill.value) == 0, "latch_fill not cleared"
    await RisingEdge(dut.clk)
    tb.log.info("Phase5 OK: clear zeroed SRAM + latch")

    # ---- Phase 6: clear must survive landing mid-RMW (regression) ----
    # i_clear arrives as a ONE-CYCLE pulse from the CSR block, but counting a
    # packet is a two-cycle read-modify-write. Under sustained monbus traffic
    # the tally sits in the write-back half every other cycle, so ~half of all
    # clear pulses land there. A clear that is only sampled in the accept half
    # is silently dropped and the host sweeps stale counts. Reproduce exactly
    # that: leave the FSM in its write-back cycle, pulse clear there, require
    # zero.
    ag, pr, pt, ec = legal[0]
    b = tb.bin_of(ag, pr, pt, ec)
    for _ in range(4):
        await tb.send(make_packet(pt, pr, ec, agent_id=ag))
    primed = await tb.read_bin(b)
    assert primed == 4, f"phase6 setup: bin {b} = {primed}, expected 4"

    # send() returns immediately after the accepting clock edge, so the FSM is
    # in its write-back cycle right now. Pulse clear exactly there.
    await tb.send(make_packet(pt, pr, ec, agent_id=ag))
    dut.i_clear.value = 1
    await RisingEdge(dut.clk)
    dut.i_clear.value = 0
    # Ride out the whole clear walk (no busy-poll: with the pulse landing
    # mid-RMW, o_flush_busy has not risen yet on the cycle after the pulse).
    await tb.wait_clocks('clk', (1 << tb.ADDR_BITS) + 20)
    assert int(dut.o_flush_busy.value) == 0, "clear walk never finished"
    tb.golden.clear()
    got = await tb.read_bin(b)
    assert got == 0, (
        f"clear pulsed during the read-modify-write write-back cycle was "
        f"DROPPED: bin {b} still reads {got} (expected 0). A one-cycle "
        f"i_clear must be latched, not sampled only in the accept state.")
    tb.log.info("Phase6 OK: mid-RMW clear honoured")

    # ---- Phase 7: a handshake on a clear cycle must not swallow a packet ----
    # in_ready used to be (ST_RUN && !i_freeze) with no clear term, while the
    # ST_RUN branch prioritises the clear over the accept. So if in_valid was
    # high on the cycle a clear arrived, the producer saw valid && ready -- its
    # packet taken -- while the FSM jumped to ST_CLEAR without latching the bin
    # or doing the RMW. The packet vanished with a completed handshake behind
    # it, which is a valid/ready contract violation, not just a lost count.
    #
    # The documented host protocol (freeze, sweep, clear) hides this because
    # i_freeze already drops in_ready. This drives the collision directly, with
    # no freeze, which is exactly the case the contract has to cover.
    await tb.do_clear()
    tb.golden.clear()
    await tb.wait_clocks('clk', (1 << tb.ADDR_BITS) + 20)

    ag, pr, pt, ec = legal[1]
    b7 = tb.bin_of(ag, pr, pt, ec)
    pkt7 = make_packet(pt, pr, ec, agent_id=ag)

    dut.in_packet.value = pkt7
    dut.in_ts.value = 0x1234
    dut.in_valid.value = 1
    dut.i_clear.value = 1
    await ReadOnly()
    took = int(dut.in_valid.value) and int(dut.in_ready.value)
    await RisingEdge(dut.clk)
    dut.i_clear.value = 0
    dut.in_valid.value = 0

    await tb.wait_clocks('clk', (1 << tb.ADDR_BITS) + 20)
    assert int(dut.o_flush_busy.value) == 0, "phase7: clear walk never finished"
    counted = await tb.read_bin(b7)

    tb.log.info(f"Phase7: handshake_on_clear_cycle={took} bin={counted}")
    assert not (took and counted == 0), (
        "in_ready was HIGH on the cycle i_clear arrived, so the producer's "
        "handshake completed -- but the packet was never counted (bin "
        f"{b7} reads {counted}). The FSM takes the clear branch ahead of the "
        "accept, so in_ready must also be gated on !i_clear && !r_clear_pend; "
        "otherwise a packet is silently swallowed behind a completed "
        "handshake.")
    tb.log.info("Phase7 OK: no packet swallowed on a clear collision")


# ----------------------------------------------------------------------------
# Pytest wrapper
# ----------------------------------------------------------------------------
def get_params():
    return [
        # (addr_bits, count_width, num_latch, n_profile)
        # ADDR_BITS must be >= clog2(N_PROFILE+1): dense bins 0..N-1 + UNEXPECTED.
        (7, 16, 4, 64),    # N=64 -> 65 bins, 128-deep SRAM
        (7,  8, 4, 64),    # 8-bit count -> fast saturation
        (8, 16, 4, 100),   # N=100 -> 101 bins, 256-deep SRAM
    ]


@pytest.mark.parametrize(
    "addr_bits, count_width, num_latch, n_profile", get_params())
def test_monbus_pkt_tally(request, addr_bits, count_width, num_latch, n_profile):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_shared':   'rtl/amba/shared',
        'rtl_monitor':  'rtl/amba/monitor',
        'rtl_includes': 'rtl/amba/includes',
    })

    dut_name = "monbus_pkt_tally"
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    ab = TBBase.format_dec(addr_bits, 2)
    cw = TBBase.format_dec(count_width, 2)
    npf = TBBase.format_dec(n_profile, 3)
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name = f"test_{worker_id}_{dut_name}_a{ab}_c{cw}_n{npf}_{reg_level}"
    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
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
        'NUM_LATCH':   str(num_latch),
        'N_PROFILE':   str(n_profile),
    }

    extra_env = {
        'DUT':                 dut_name,
        'LOG_PATH':            log_path,
        'COCOTB_LOG_LEVEL':    'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED':                os.environ.get('SEED', str(random.randint(0, 100000))),
        'PARAM_ADDR_BITS':     str(addr_bits),
        'PARAM_COUNT_WIDTH':   str(count_width),
        'PARAM_NUM_LATCH':     str(num_latch),
        'PARAM_N_PROFILE':     str(n_profile),
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

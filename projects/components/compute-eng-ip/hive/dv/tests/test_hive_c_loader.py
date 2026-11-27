# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_hive_c_loader
# Purpose: hive_c_loader (Block 1: HIVE-C core + two 32 KB banks + the
#          kestrel-pattern AXIL load-then-run window), testplan LDR-01..05
#
# Documentation: projects/components/compute-eng-ip/hive/dv/testplans/hive_c_loader_testplan.yaml
# Subsystem: hive
#
# Author: sean galloway
# Created: 2026-10-13

"""
Test for hive_c_loader

The test drives only the loader contract -- the AXIL window, the CTRL run
bit, and the core's observable memory traffic -- so the same scenarios run
on every CORE_FLAVOR (hive PRD 10.3).

Scenarios:
  LDR-01: reset hold (no core traffic while run = 0) and release (first
          fetch at 0x0000_0000)
  LDR-02: AXIL writes/readback across both banks, byte strobes, BUILD_ID,
          SLVERR for unmapped / unaligned / read-only
  LDR-03: load an RV32I program, run, observe the fetch progression and the
          store on the data port, and that it landed in D-mem
  LDR-04: run mode: memory writes SLVERR and dropped, CTRL still writable,
          loader reads correct while the core contends for port B
  LDR-05: M-extension smoke (mul/mulh/mulhsu/mulhu/div/divu/rem/remu) with
          a Python golden, corner operands always, random operands at
          func/full
"""

import logging
import os
import random
import sys

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, RisingEdge, Timer
from cocotb_test.simulator import run

from CocoTBFramework.components.axil4.axil4_factories import create_axil4_master
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import current_level, level_env, reg_level_grid
from TBClasses.shared.utilities import get_repo_root, sim_build_path
from cov_utils.conftest_coverage import get_coverage_compile_args

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

FILELIST = 'projects/components/compute-eng-ip/hive/rtl/filelists/hive_c_loader.f'

# ---------------------------------------------------------------------------
# Loader address map (hive_c_loader.sv header)
# ---------------------------------------------------------------------------
AXIL_ADDR_WIDTH = 18
IMEM_BASE = 0x0_0000
DMEM_BASE = 0x0_8000
REG_CTRL = 0x2_0000
REG_BUILD_ID = 0x2_0004
CTRL_RUN = 0x1
CTRL_ACTIVE = 0x2                              # read only: the glue's core_active
BUILD_ID = {'vexriscv': 0x4843_5658}          # "HCVX"
CORE_FLAVOR = os.environ.get('HIVE_C_CORE_FLAVOR', 'vexriscv')

RESP_OKAY = 0
RESP_SLVERR = 2
MASK32 = 0xFFFF_FFFF

# ---------------------------------------------------------------------------
# Level-dependent scaling
# ---------------------------------------------------------------------------
_LVL = current_level()
_D = {
    'gate': dict(axil_iters=2,  m_rand_pairs=0,  contention_reads=16, timeout_us=400),
    'func': dict(axil_iters=8,  m_rand_pairs=8,  contention_reads=16, timeout_us=1000),
    'full': dict(axil_iters=32, m_rand_pairs=32, contention_reads=64, timeout_us=4000),
}[_LVL]


# ---------------------------------------------------------------------------
# RV32I/M instruction encoders (no compressed instructions)
# ---------------------------------------------------------------------------
OP_LUI = 0x37
OP_JAL = 0x6F
OP_LOAD = 0x03
OP_STORE = 0x23
OP_IMM = 0x13
OP_REG = 0x33

F3_ADD = 0
F3_SW = 2
F3_LW = 2
F7_ADD = 0b0000000
F7_MULDIV = 0b0000001

# RV32M funct3 (unprivileged spec, "M" chapter)
F3_M = {'mul': 0, 'mulh': 1, 'mulhsu': 2, 'mulhu': 3,
        'div': 4, 'divu': 5, 'rem': 6, 'remu': 7}


def encode_i(rd, rs1, imm12, funct3, opcode):
    return (((imm12 & 0xFFF) << 20) | ((rs1 & 0x1F) << 15) | ((funct3 & 0x7) << 12)
            | ((rd & 0x1F) << 7) | (opcode & 0x7F))


def encode_u(rd, imm20, opcode):
    return ((imm20 & 0xFFFFF) << 12) | ((rd & 0x1F) << 7) | (opcode & 0x7F)


def encode_r(rd, rs1, rs2, funct3, funct7, opcode):
    return (((funct7 & 0x7F) << 25) | ((rs2 & 0x1F) << 20) | ((rs1 & 0x1F) << 15)
            | ((funct3 & 0x7) << 12) | ((rd & 0x1F) << 7) | (opcode & 0x7F))


def encode_s(rs1, rs2, imm12, funct3, opcode):
    imm = imm12 & 0xFFF
    return (((imm >> 5) << 25) | ((rs2 & 0x1F) << 20) | ((rs1 & 0x1F) << 15)
            | ((funct3 & 0x7) << 12) | ((imm & 0x1F) << 7) | (opcode & 0x7F))


def encode_j(rd, imm21, opcode=OP_JAL):
    """J-type; imm21 is a signed byte offset."""
    imm = imm21 & 0x1FFFFF
    inst = ((((imm >> 20) & 1) << 31) | (((imm >> 1) & 0x3FF) << 21) | (((imm >> 11) & 1) << 20)
            | (((imm >> 12) & 0xFF) << 12) | ((rd & 0x1F) << 7) | (opcode & 0x7F))
    return inst & MASK32


def instr_lui(rd, imm20):
    return encode_u(rd, imm20, OP_LUI)


def instr_addi(rd, rs1, imm12):
    return encode_i(rd, rs1, imm12, F3_ADD, OP_IMM)


def instr_add(rd, rs1, rs2):
    return encode_r(rd, rs1, rs2, F3_ADD, F7_ADD, OP_REG)


def instr_m(op, rd, rs1, rs2):
    return encode_r(rd, rs1, rs2, F3_M[op], F7_MULDIV, OP_REG)


def instr_sw(rs1, rs2, imm12):
    return encode_s(rs1, rs2, imm12, F3_SW, OP_STORE)


def instr_lw(rd, rs1, imm12):
    return encode_i(rd, rs1, imm12, F3_LW, OP_LOAD)


def instr_jal(rd, imm21):
    return encode_j(rd, imm21)


def instr_li(rd, value):
    """lui + addi for any 32-bit constant (addi's immediate is signed)."""
    value &= MASK32
    hi = ((value + 0x800) >> 12) & 0xFFFFF
    lo = (value - (hi << 12)) & 0xFFF
    return [instr_lui(rd, hi), instr_addi(rd, rd, lo)]


# ---------------------------------------------------------------------------
# RV32M golden (unprivileged spec semantics, incl. divide by zero / overflow)
# ---------------------------------------------------------------------------
def _s32(v):
    v &= MASK32
    return v - (1 << 32) if v & 0x8000_0000 else v


def rv32m_golden(op, a, b):
    ua, ub = a & MASK32, b & MASK32
    sa, sb = _s32(a), _s32(b)
    if op == 'mul':
        return (sa * sb) & MASK32
    if op == 'mulh':
        return ((sa * sb) >> 32) & MASK32
    if op == 'mulhsu':
        return ((sa * ub) >> 32) & MASK32
    if op == 'mulhu':
        return ((ua * ub) >> 32) & MASK32
    if op == 'div':
        if sb == 0:
            return MASK32
        if sa == -(1 << 31) and sb == -1:
            return ua
        q = abs(sa) // abs(sb)
        return (q if (sa < 0) == (sb < 0) else -q) & MASK32
    if op == 'divu':
        return MASK32 if ub == 0 else ua // ub
    if op == 'rem':
        if sb == 0:
            return ua
        if sa == -(1 << 31) and sb == -1:
            return 0
        r = abs(sa) % abs(sb)
        return (r if sa >= 0 else -r) & MASK32
    if op == 'remu':
        return ua if ub == 0 else ua % ub
    raise ValueError(op)


M_CORNER_PAIRS = [
    (6, 7), (20, 4), (-20, 3), (7, -2),
    (0x8000_0000, 0xFFFF_FFFF),        # signed overflow: div -> 0x8000_0000, rem -> 0
    (12345, 0),                        # divide by zero
    (0xFFFF_FFFF, 0xFFFF_FFFF), (0x7FFF_FFFF, 0x8000_0000),
]


# ---------------------------------------------------------------------------
# Observation of the core's memory traffic (hive_c_loader core_* nets)
# ---------------------------------------------------------------------------
class CoreTrafficLog:
    """Samples the accepted fetch and data requests every cycle.

    Sampled on the falling edge: the requests are accepted in the cycle
    they are presented (the core ports are always ready), so a request seen
    at the falling edge is the one accepted at the next rising edge.
    """

    def __init__(self, dut):
        self.dut = dut
        self.cycle = 0
        self.fetches = []   # (cycle, pc)
        self.data = []      # (cycle, wr, addr, wdata, mask)
        self.ar_waits = 0   # cycles a loader read waited on a core data access

    async def run(self):
        dut = self.dut
        while True:
            await FallingEdge(dut.clk)
            self.cycle += 1
            if int(dut.core_ibus_cmd_valid.value):
                self.fetches.append((self.cycle, int(dut.core_ibus_pc.value)))
            # hive_c_loader's flavor-neutral arbitration point: the loader's
            # AR is pending while the core owns port B this cycle
            if int(dut.fub_arvalid.value) and int(dut.w_core_d_mem.value):
                self.ar_waits += 1
            if int(dut.core_dbus_cmd_valid.value):
                self.data.append((self.cycle, int(dut.core_dbus_wr.value),
                                  int(dut.core_dbus_addr.value),
                                  int(dut.core_dbus_data.value),
                                  int(dut.core_dbus_mask.value)))

    def clear(self):
        self.fetches.clear()
        self.data.clear()
        self.ar_waits = 0

    def stores(self):
        return [(a, d, m) for (_, wr, a, d, m) in self.data if wr]


# ---------------------------------------------------------------------------
# The loader through the framework AXIL4 master
# ---------------------------------------------------------------------------
class LoaderHost:
    """AXIL accesses that return the response code instead of raising."""

    def __init__(self, dut):
        self.dut = dut
        self.master = create_axil4_master(dut=dut, clock=dut.clk, prefix='s_axil_',
                                          addr_width=AXIL_ADDR_WIDTH, data_width=32,
                                          multi_sig=True,
                                          log=logging.getLogger('hive_c_loader.axil'))

    async def write(self, addr, data, strb=0xF):
        try:
            return await self.master['write_register'](addr, data & MASK32, strb)
        except RuntimeError:
            return self.master['write'].last_b_packet.resp

    async def read(self, addr):
        try:
            data = await self.master['read_register'](addr)
            return data, RESP_OKAY
        except RuntimeError:
            pkt = self.master['read'].last_r_packet
            return pkt.data, pkt.resp

    async def write_ok(self, addr, data, strb=0xF, what=''):
        resp = await self.write(addr, data, strb)
        assert resp == RESP_OKAY, f"{what}: write @0x{addr:05X} returned resp={resp}"

    async def read_ok(self, addr, what=''):
        data, resp = await self.read(addr)
        assert resp == RESP_OKAY, f"{what}: read @0x{addr:05X} returned resp={resp}"
        return data

    async def set_run(self, run):
        await self.write_ok(REG_CTRL, 1 if run else 0, what='CTRL')

    async def load(self, base, words, what='load'):
        for i, w in enumerate(words):
            await self.write_ok(base + 4 * i, w, what=what)


async def wait_until(dut, pred, max_cycles, what):
    for _ in range(max_cycles):
        if pred():
            return
        await RisingEdge(dut.clk)
    assert pred(), f"{what}: not seen within {max_cycles} cycles"


# ---------------------------------------------------------------------------
# Cocotb test
# ---------------------------------------------------------------------------
@cocotb.test(timeout_time=_D['timeout_us'], timeout_unit='us')
async def cocotb_test_hive_c_loader(dut):
    """Run all hive_c_loader testplan scenarios."""
    log = dut._log
    seed = int(os.environ.get('SEED', '0'))
    rng = random.Random(seed)
    log.info("=" * 80)
    log.info(f"hive_c_loader  level={_LVL}  flavor={CORE_FLAVOR}  SEED={seed}")
    log.info("=" * 80)

    cocotb.start_soon(Clock(dut.clk, 10, unit="ns").start())
    dut.rst_n.value = 0
    dut.irq_external.value = 0
    dut.irq_timer.value = 0
    dut.irq_software.value = 0
    host = LoaderHost(dut)
    traffic = CoreTrafficLog(dut)
    cocotb.start_soon(traffic.run())

    await Timer(100, unit="ns")
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    await RisingEdge(dut.clk)

    # -----------------------------------------------------------------------
    # LDR-01: reset hold and staged release
    # -----------------------------------------------------------------------
    log.info("=== LDR-01: reset hold and staged release ===")
    for _ in range(20):
        await RisingEdge(dut.clk)
    data, _ = await host.read(REG_CTRL)
    assert data == 0, f"LDR-01: CTRL = 0x{data:X} out of reset, expected run = active = 0"
    assert int(dut.o_run.value) == 0, "LDR-01: o_run high out of reset"
    assert not traffic.fetches, f"LDR-01: fetch while held: {traffic.fetches[:4]}"
    assert not traffic.data, f"LDR-01: data access while held: {traffic.data[:4]}"

    await host.set_run(True)
    await wait_until(dut, lambda: traffic.fetches, 50, "LDR-01: first fetch after run")
    assert int(dut.o_run.value) == 1, "LDR-01: o_run low after run"
    data = await host.read_ok(REG_CTRL, 'LDR-01')
    assert data == CTRL_RUN | CTRL_ACTIVE, f"LDR-01: CTRL = 0x{data:X} while running"
    pc = traffic.fetches[0][1]
    assert pc == 0x0000_0000, f"LDR-01: first fetch pc = 0x{pc:08X}, expected 0x00000000"
    log.info("LDR-01: first fetch at 0x00000000 - PASS")

    await host.set_run(False)
    for _ in range(4):
        await RisingEdge(dut.clk)
    traffic.clear()
    for _ in range(20):
        await RisingEdge(dut.clk)
    assert not traffic.fetches and not traffic.data, "LDR-01: traffic after run cleared"

    # -----------------------------------------------------------------------
    # LDR-02: AXIL window writes/readback both memories
    # -----------------------------------------------------------------------
    log.info("=== LDR-02: AXIL writes and readback ===")
    assert await host.read_ok(REG_BUILD_ID, 'LDR-02') == BUILD_ID[CORE_FLAVOR], \
        "LDR-02: BUILD_ID"
    model = {}
    for i in range(_D['axil_iters']):
        for base, span in ((IMEM_BASE, 0x8000), (DMEM_BASE, 0x8000)):
            addr = base + 4 * rng.randrange(span // 4)
            data = rng.getrandbits(32)
            await host.write_ok(addr, data, what='LDR-02')
            model[addr] = data
            strb = rng.randrange(16)
            data2 = rng.getrandbits(32)
            await host.write_ok(addr, data2, strb, what='LDR-02 strobe')
            for lane in range(4):
                if strb >> lane & 1:
                    m = 0xFF << (8 * lane)
                    model[addr] = (model[addr] & ~m) | (data2 & m)
    for addr, exp in model.items():
        got = await host.read_ok(addr, 'LDR-02')
        assert got == exp, f"LDR-02 readback @0x{addr:05X}: 0x{got:08X} != 0x{exp:08X}"
    # bank ends
    for addr in (0x0_7FFC, 0x0_8000, 0x0_FFFC):
        await host.write_ok(addr, addr ^ 0xA5A5_0000, what='LDR-02 edge')
    for addr in (0x0_7FFC, 0x0_8000, 0x0_FFFC):
        assert await host.read_ok(addr, 'LDR-02 edge') == addr ^ 0xA5A5_0000

    # Fixed sub-word strobes (start from a known word, not power-up content)
    await host.write_ok(0x0_2000, 0x0000_0000, what='LDR-02')
    await host.write_ok(0x0_2000, 0x1234_5678, 0x1, what='LDR-02')
    rdata = await host.read_ok(0x0_2000, 'LDR-02')
    assert rdata == 0x0000_0078, f"LDR-02 byte strobe: expected 0x00000078, got 0x{rdata:08X}"
    await host.write_ok(0x0_2000, 0xAABB_CCDD, 0xC, what='LDR-02')
    rdata = await host.read_ok(0x0_2000, 'LDR-02')
    assert rdata == 0xAABB_0078, f"LDR-02 half strobe: expected 0xAABB0078, got 0x{rdata:08X}"

    # SLVERR: unmapped, unaligned, unmapped register, read-only register
    for addr in (0x1_0000, 0x1_FFFC, 0x0_0001, 0x0_8002, 0x2_0008, 0x3_FFFC):
        assert await host.write(addr, 0) == RESP_SLVERR, f"LDR-02: write @0x{addr:05X} should SLVERR"
        _, rresp = await host.read(addr)
        assert rresp == RESP_SLVERR, f"LDR-02: read @0x{addr:05X} should SLVERR"
    assert await host.write(REG_BUILD_ID, 0) == RESP_SLVERR, "LDR-02: BUILD_ID write should SLVERR"
    assert await host.read_ok(0x0_2000, 'LDR-02') == 0xAABB_0078, "LDR-02: an errored write landed"
    log.info("LDR-02: AXIL window readback and SLVERR - PASS")

    # -----------------------------------------------------------------------
    # LDR-03: Load-then-run handoff
    # -----------------------------------------------------------------------
    log.info("=== LDR-03: load-then-run handoff ===")
    prog = [
        instr_addi(5, 0, 5),      # 0x00 x5 = 5
        instr_addi(6, 0, 7),      # 0x04 x6 = 7
        instr_add(7, 5, 6),       # 0x08 x7 = 12
        instr_lui(10, 0x00008),   # 0x0C x10 = 0x0000_8000
        instr_sw(10, 7, 0),       # 0x10 mem[0x8000] = 12
        instr_jal(0, 0),          # 0x14 loop here
    ]
    loop_pc = 0x14
    await host.load(IMEM_BASE, prog, 'LDR-03')
    await host.write_ok(DMEM_BASE, 0xDEAD_0000, what='LDR-03')
    traffic.clear()
    await host.set_run(True)
    await wait_until(dut, lambda: len(traffic.fetches) >= 24 and traffic.stores(), 400,
                     "LDR-03: fetches and the store")

    pcs = [pc for _, pc in traffic.fetches]
    assert pcs[:6] == [0x00, 0x04, 0x08, 0x0C, 0x10, 0x14], \
        f"LDR-03: straight-line fetches {[hex(p) for p in pcs[:6]]}"
    # After the jal: the loop target again, or a wrong-path fetch that
    # sequentially follows the previous one (a fetch-order observation may
    # show those; they never retire).
    for prev, pc in zip(pcs[5:], pcs[6:]):
        assert pc == loop_pc or (pc == prev + 4 and pc > loop_pc), \
            f"LDR-03: fetch 0x{pc:X} after 0x{prev:X} is outside the loop: {[hex(p) for p in pcs[:24]]}"
    assert pcs[6:].count(loop_pc) >= 4, f"LDR-03: loop not re-fetched: {[hex(p) for p in pcs[:24]]}"
    assert traffic.stores() == [(0x0000_8000, 12, 0xF)], f"LDR-03: stores {traffic.stores()}"
    log.info(f"LDR-03: fetch order {[hex(p) for p in pcs[:12]]}")

    await host.set_run(False)
    got = await host.read_ok(DMEM_BASE, 'LDR-03')
    assert got == 12, f"LDR-03: D-mem[0x8000] = 0x{got:08X} after run, the store did not land"
    for i, w in enumerate(prog):
        assert await host.read_ok(IMEM_BASE + 4 * i, 'LDR-03') == w, f"LDR-03: I-mem word {i} changed"
    log.info("LDR-03: load-then-run handoff - PASS")

    # -----------------------------------------------------------------------
    # LDR-04: run mode -- window closed for writes, reads arbitrated
    # -----------------------------------------------------------------------
    log.info("=== LDR-04: run mode arbitration ===")
    prog4 = [
        instr_lui(10, 0x00008),   # 0x00 x10 = 0x8000
        instr_addi(7, 0, 0x5A),   # 0x04 x7  = 0x5A
        instr_sw(10, 7, 0x100),   # 0x08 loop: mem[0x8100] = x7
        instr_lw(8, 10, 0x100),   # 0x0C       x8 = mem[0x8100] (the core's load path)
        instr_sw(10, 8, 0x104),   # 0x10       mem[0x8104] = x8
        instr_sw(10, 7, 0x108),   # 0x14       more port-B traffic, so loader
        instr_sw(10, 7, 0x10C),   # 0x18       reads of D-mem keep colliding
        instr_sw(10, 7, 0x110),   # 0x1C
        instr_addi(7, 7, 1),      # 0x20       x7++
        instr_jal(0, -28),        # 0x24       -> 0x08
    ]
    await host.load(IMEM_BASE, prog4, 'LDR-04')
    pattern = {DMEM_BASE + 0x1000 + 4 * i: rng.getrandbits(32) for i in range(16)}
    for a, v in pattern.items():
        await host.write_ok(a, v, what='LDR-04 pattern')
    await host.write_ok(DMEM_BASE + 0x200, 0x600D_F00D, what='LDR-04')
    traffic.clear()
    await host.set_run(True)
    await wait_until(dut, lambda: len(traffic.data) >= 4, 200, "LDR-04: core data traffic")

    # Writes are refused while running; CTRL readback says running
    assert await host.write(DMEM_BASE + 0x200, 0xBAD0_BAD0) == RESP_SLVERR, \
        "LDR-04: run-mode D-mem write should SLVERR"
    assert await host.write(IMEM_BASE + 0x08, 0) == RESP_SLVERR, \
        "LDR-04: run-mode I-mem write should SLVERR"
    assert await host.read_ok(REG_CTRL, 'LDR-04') == CTRL_RUN | CTRL_ACTIVE, "LDR-04: CTRL readback"

    # Loader reads while the core is hammering port B.  D-mem is the bank
    # the core's loop uses, so those reads are the collisions; I-mem reads
    # are mixed in (one in four) as the no-contention control.
    first_cycle = traffic.cycle
    waits_before = traffic.ar_waits
    d_items = list(pattern.items())
    i_items = [(IMEM_BASE + 4 * i, w) for i, w in enumerate(prog4)]
    for k in range(_D['contention_reads']):
        a, v = rng.choice(i_items if k % 4 == 3 else d_items)
        got = await host.read_ok(a, 'LDR-04 contention')
        assert got == v, f"LDR-04: run-mode read @0x{a:05X}: 0x{got:08X} != 0x{v:08X}"
    last_cycle = traffic.cycle
    overlap = [c for (c, *_rest) in traffic.data if first_cycle <= c <= last_cycle]
    assert len(overlap) >= _D['contention_reads'], \
        f"LDR-04: only {len(overlap)} core data accesses during the reads; no contention exercised"
    ar_waits = traffic.ar_waits - waits_before
    assert ar_waits >= 1, "LDR-04: no loader read ever waited on the core; arbitration not exercised"

    await host.set_run(False)
    for _ in range(4):
        await RisingEdge(dut.clk)
    # The core's loop: stores 0x5A, 0x5B, ... (each one the previous + 1)
    stores = [d for (_, wr, a, d, m) in traffic.data if wr and a == 0x8100]
    assert stores and stores == list(range(0x5A, 0x5A + len(stores))), \
        f"LDR-04: store sequence {stores[:8]}"
    echoes = [d for (_, wr, a, d, m) in traffic.data if wr and a == 0x8104]
    assert echoes and echoes == stores[:len(echoes)], \
        f"LDR-04: loaded-back values {echoes[:8]} != stored {stores[:8]}"
    assert await host.read_ok(REG_CTRL, 'LDR-04') == 0, "LDR-04: CTRL run/active clear"
    assert await host.read_ok(DMEM_BASE + 0x200, 'LDR-04') == 0x600D_F00D, \
        "LDR-04: a refused run-mode write landed"
    assert await host.read_ok(IMEM_BASE + 0x08, 'LDR-04') == prog4[2], \
        "LDR-04: a refused run-mode I-mem write landed"
    last = await host.read_ok(DMEM_BASE + 0x100, 'LDR-04')
    assert last == stores[-1], \
        f"LDR-04: D-mem[0x8100] = 0x{last:X}, last accepted store 0x{stores[-1]:X}"
    await host.write_ok(DMEM_BASE + 0x200, 0x1111_2222, what='LDR-04 reopened')
    assert await host.read_ok(DMEM_BASE + 0x200, 'LDR-04') == 0x1111_2222, \
        "LDR-04: window not reopened in load mode"
    log.info(f"LDR-04: {_D['contention_reads']} reads under {len(overlap)} core accesses, "
             f"{ar_waits} read-wait cycles - PASS")

    # -----------------------------------------------------------------------
    # LDR-05: M-extension smoke with a Python golden
    # -----------------------------------------------------------------------
    log.info("=== LDR-05: M-extension smoke ===")
    pairs = list(M_CORNER_PAIRS)
    pairs += [(rng.getrandbits(32), rng.getrandbits(32) >> rng.randrange(32))
              for _ in range(_D['m_rand_pairs'])]
    ops = list(F3_M)
    prog5 = [instr_lui(13, 0x00008)]              # x13 = 0x8000 (result base)
    exp_addr = []                                  # (addr, golden, op, a, b), in store order
    for a, b in pairs:
        prog5 += instr_li(5, a) + instr_li(6, b)
        for op in ops:
            slot = len(exp_addr)
            assert 4 * slot < 2048, "LDR-05: result slots exceed the sw immediate"
            prog5.append(instr_m(op, 7, 5, 6))
            prog5.append(instr_sw(13, 7, 4 * slot))
            exp_addr.append((DMEM_BASE + 4 * slot, rv32m_golden(op, a, b), op, a, b))
    prog5.append(instr_jal(0, 0))
    assert len(prog5) * 4 <= 0x8000, "LDR-05 program exceeds I-mem"
    await host.load(IMEM_BASE, prog5, 'LDR-05')
    traffic.clear()
    await host.set_run(True)
    await wait_until(dut, lambda: len(traffic.stores()) >= len(exp_addr), 60 * len(exp_addr) + 500,
                     "LDR-05: all result stores")
    got_stores = traffic.stores()
    for (addr, val, op, a, b), (ga, gd, gm) in zip(exp_addr, got_stores):
        assert (ga, gd, gm) == (addr, val, 0xF), \
            (f"LDR-05: {op}(0x{a & MASK32:08X}, 0x{b & MASK32:08X}) stored 0x{gd:08X} @0x{ga:05X}, "
             f"expected 0x{val:08X} @0x{addr:05X}")
    await host.set_run(False)
    for addr, val, op, a, b in exp_addr[:: max(1, len(exp_addr) // 16)]:
        assert await host.read_ok(addr, 'LDR-05') == val, f"LDR-05: {op} result not in D-mem"
    log.info(f"LDR-05: {len(exp_addr)} M results match the golden - PASS")

    log.info("=" * 80)
    log.info("hive_c_loader test PASSED")
    log.info("=" * 80)


# ---------------------------------------------------------------------------
# Pytest wrapper
# ---------------------------------------------------------------------------
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_hive_c_loader(request, test_level):
    """Pytest wrapper for hive_c_loader."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root,
                                                          filelist_path=FILELIST)

    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
        "--no-timing",
        # vendor/vexriscv/VexRiscv.v is generated upstream code (not linted here)
        "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND", "-Wno-CASEINCOMPLETE",
    ]
    compile_args.extend(get_coverage_compile_args())

    module = os.path.splitext(os.path.basename(__file__))[0]
    tests_dir = os.path.dirname(__file__)
    log_dir = os.path.join(tests_dir, 'logs')
    os.makedirs(log_dir, exist_ok=True)

    test_name = f'test_hive_c_loader_{CORE_FLAVOR}_{test_level}'
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)

    run(
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="hive_c_loader",
        module=module,
        simulator="verilator",
        parameters={'CORE_FLAVOR': f'"{CORE_FLAVOR}"'},
        compile_args=compile_args,
        sim_build=sim_build,
        work_dir=sim_build,
        waves=enable_waves,
        plus_args=['--trace'] if enable_waves else [],
        extra_env={**level_env(test_level), 'HIVE_C_CORE_FLAVOR': CORE_FLAVOR},
    )


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

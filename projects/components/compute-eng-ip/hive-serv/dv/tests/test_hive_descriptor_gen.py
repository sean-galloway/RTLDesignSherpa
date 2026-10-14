# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_hive_descriptor_gen
# Purpose: TDD test for HIVE-C descriptor_gen (Block 1 submodule)
#
# Documentation: projects/components/compute-eng-ip/hive-serv/dv/testplans/hive_descriptor_gen_testplan.yaml
# Subsystem: hive-serv
#
# Author: sean galloway
# Created: 2026-10-13

"""
Test for hive_descriptor_gen

Validates the mailbox-to-CDA descriptor assembly path per the HIVE HAS/MAS
spec: field assembly, flag packing, FIFO ordering, and full-queue stall.
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer, Combine
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import current_level, level_env, reg_level_grid
from cov_utils.conftest_coverage import get_coverage_compile_args

repo_root = get_repo_root()
sys.path.insert(0, repo_root)


# Scenario scaling by level.  The transaction shape is fixed (one 256-bit CDA
# beat per doorbell); only the repetition counts change.
_LVL = current_level()
_S = {
    'gate': dict(dg01=2, dg02=1, dg03=3, dg05=4),
    'func': dict(dg01=4, dg02=2, dg03=6, dg05=16),
    'full': dict(dg01=8, dg02=4, dg03=7, dg05=64),
}[_LVL]
_TIMEOUT_US = {'gate': 40, 'func': 80, 'full': 240}[_LVL]


# -----------------------------------------------------------------------------
# CDA descriptor field helpers (HAS §4.2)
# -----------------------------------------------------------------------------
def pack_desc(src, dst, length, stride, flags, next_ptr):
    """Return a 256-bit descriptor beat from its field values."""
    return ((src & ((1 << 64) - 1)) << 192) | \
           ((dst & ((1 << 64) - 1)) << 128) | \
           ((length & ((1 << 32) - 1)) << 96) | \
           ((stride & ((1 << 32) - 1)) << 64) | \
           ((flags & ((1 << 32) - 1)) << 32) | \
           (next_ptr & ((1 << 32) - 1))


def unpack_desc(desc):
    """Return (src, dst, length, stride, flags, next_ptr) from a 256-bit beat."""
    src = (desc >> 192) & ((1 << 64) - 1)
    dst = (desc >> 128) & ((1 << 64) - 1)
    length = (desc >> 96) & ((1 << 32) - 1)
    stride = (desc >> 64) & ((1 << 32) - 1)
    flags = (desc >> 32) & ((1 << 32) - 1)
    next_ptr = desc & ((1 << 32) - 1)
    return src, dst, length, stride, flags, next_ptr


def pack_flags(burst_size=0, burst_type=0, priority=0, dest_tile=0, src_tile=0,
               irq_vector=0, en_2d=0, en_sg=0, en_irq=0, coherent=0, desc_type=0):
    """Build a 32-bit control-flags word from named subfields (HAS §4.2)."""
    return ((burst_size & 0xF) << 28) | \
           ((burst_type & 0xF) << 24) | \
           ((priority & 0xF) << 20) | \
           ((dest_tile & 0xF) << 16) | \
           ((src_tile & 0xF) << 12) | \
           ((irq_vector & 0xF) << 8) | \
           ((en_2d & 1) << 7) | \
           ((en_sg & 1) << 6) | \
           ((en_irq & 1) << 5) | \
           ((coherent & 1) << 4) | \
           (desc_type & 0xF)


def unpack_flags(flags):
    """Return named subfields from a 32-bit control-flags word."""
    return dict(
        burst_size=(flags >> 28) & 0xF,
        burst_type=(flags >> 24) & 0xF,
        priority=(flags >> 20) & 0xF,
        dest_tile=(flags >> 16) & 0xF,
        src_tile=(flags >> 12) & 0xF,
        irq_vector=(flags >> 8) & 0xF,
        en_2d=(flags >> 7) & 1,
        en_sg=(flags >> 6) & 1,
        en_irq=(flags >> 5) & 1,
        coherent=(flags >> 4) & 1,
        desc_type=flags & 0xF,
    )


@cocotb.test(timeout_time=_TIMEOUT_US, timeout_unit='us')
async def cocotb_test_hive_descriptor_gen(dut):
    """Run all hive_descriptor_gen scenarios from the testplan."""
    log = dut._log
    level = current_level()
    log.info("=" * 80)
    log.info(f"Starting hive_descriptor_gen test  level={level}")
    log.info("=" * 80)

    # Clock and reset
    clock = Clock(dut.clk, 10, units="ns")  # 100 MHz
    cocotb.start_soon(clock.start())

    dut.rst_n.value = 0
    dut.mbox_we.value = 0
    dut.mbox_addr.value = 0
    dut.mbox_wdata.value = 0
    dut.q_ready.value = 0

    await Timer(100, units="ns")
    dut.rst_n.value = 1
    await RisingEdge(dut.clk)
    log.info("Reset complete")

    # -------------------------------------------------------------------------
    # Mailbox helpers
    # -------------------------------------------------------------------------
    async def mbox_write_field(addr, data):
        """Write a 32-bit word to mailbox field address 0..7."""
        assert 0 <= addr <= 7, "field address out of range"
        await RisingEdge(dut.clk)
        dut.mbox_we.value = 1
        dut.mbox_addr.value = addr
        dut.mbox_wdata.value = data & 0xFFFFFFFF
        await RisingEdge(dut.clk)
        dut.mbox_we.value = 0
        dut.mbox_addr.value = 0
        dut.mbox_wdata.value = 0

    async def mbox_write_desc(src, dst, length, stride, flags, next_ptr):
        """Load all eight mailbox field words for one descriptor."""
        await mbox_write_field(0, src & 0xFFFFFFFF)
        await mbox_write_field(1, (src >> 32) & 0xFFFFFFFF)
        await mbox_write_field(2, dst & 0xFFFFFFFF)
        await mbox_write_field(3, (dst >> 32) & 0xFFFFFFFF)
        await mbox_write_field(4, length)
        await mbox_write_field(5, stride)
        await mbox_write_field(6, flags)
        await mbox_write_field(7, next_ptr)

    async def ring_doorbell():
        """Pulse mailbox doorbell (addr == 8)."""
        await RisingEdge(dut.clk)
        dut.mbox_we.value = 1
        dut.mbox_addr.value = 8
        dut.mbox_wdata.value = 0
        await RisingEdge(dut.clk)
        dut.mbox_we.value = 0
        dut.mbox_addr.value = 0

    async def dequeue_desc():
        """Wait for q_valid and return the descriptor beat."""
        dut.q_ready.value = 1
        await RisingEdge(dut.clk)
        while dut.q_valid.value == 0:
            await RisingEdge(dut.clk)
        # Registered-output FIFO: q_desc still holds the beat consumed at this
        # edge, so sample after the handshake.
        desc = int(dut.q_desc.value)
        dut.q_ready.value = 0
        return desc

    # -------------------------------------------------------------------------
    # DG-01: Mailbox write to field-assembled CDA beat (corner values)
    # -------------------------------------------------------------------------
    log.info("=== Scenario DG-01: field assembly with corner values ===")
    corner_banks = [
        (0x0000_0000_0000_0000, 0x0000_0000_0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000),
        (0xFFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF),
        (0x8000_0000_0000_0000, 0x0000_0000_0000_0001, 0x0000_0001, 0x8000_0000, 0x1234_5678, 0xDEAD_BEEF),
        (0x0000_0000_0000_0001, 0x8000_0000_0000_0000, 0xFFFF_FFFE, 0x7FFF_FFFF, 0xA5A5_5A5A, 0xCAFE_BABE),
    ]
    for i in range(_S['dg01']):
        src, dst, length, stride, flags, next_ptr = corner_banks[i % len(corner_banks)]
        # Add a small per-iteration offset so repeated corners still differ.
        src = (src + i) & ((1 << 64) - 1)
        dst = (dst ^ (i * 0x1111_1111_1111_1111)) & ((1 << 64) - 1)
        await mbox_write_desc(src, dst, length, stride, flags, next_ptr)
        await ring_doorbell()
        desc = await dequeue_desc()
        got_src, got_dst, got_len, got_stride, got_flags, got_next = unpack_desc(desc)
        expected = pack_desc(src, dst, length, stride, flags, next_ptr)
        assert desc == expected, (
            f"DG-01 case {i}: descriptor mismatch\n"
            f"  expected 0x{expected:064x}\n"
            f"  got      0x{desc:064x}"
        )
        log.info(f"  DG-01 case {i}: 0x{desc:064x} - PASS")

    # -------------------------------------------------------------------------
    # DG-02: Control-flag bit packing (each subfield survives)
    # -------------------------------------------------------------------------
    log.info("=== Scenario DG-02: control-flag subfield packing ===")
    flag_cases = [
        dict(burst_size=0xF, burst_type=0x2, priority=0xA, dest_tile=0x3,
             src_tile=0xC, irq_vector=0x7, en_2d=1, en_sg=0, en_irq=1, coherent=0, desc_type=0x9),
        dict(burst_size=0x0, burst_type=0x0, priority=0x0, dest_tile=0x0,
             src_tile=0x0, irq_vector=0x0, en_2d=0, en_sg=1, en_irq=0, coherent=1, desc_type=0x0),
        dict(burst_size=0x5, burst_type=0xA, priority=0xF, dest_tile=0x0,
             src_tile=0xF, irq_vector=0xA, en_2d=1, en_sg=1, en_irq=1, coherent=1, desc_type=0xF),
    ]
    for i in range(_S['dg02']):
        case = flag_cases[i % len(flag_cases)]
        flags = pack_flags(**case)
        src = 0xAABB_CCDD_EEFF_0011 + i
        dst = 0x1122_3344_5566_7788 + i * 0x10
        await mbox_write_desc(src, dst, 0x1000 + i, 0x40 + i, flags, 0x8000_0000 + i)
        await ring_doorbell()
        desc = await dequeue_desc()
        got_src, got_dst, got_len, got_stride, got_flags, got_next = unpack_desc(desc)
        assert got_flags == flags, f"DG-02 case {i}: flags mismatch expected 0x{flags:08x} got 0x{got_flags:08x}"
        got_sub = unpack_flags(got_flags)
        for k, v in case.items():
            assert got_sub[k] == v, f"DG-02 case {i}: subfield {k} expected {v} got {got_sub[k]}"
        log.info(f"  DG-02 case {i}: flags 0x{flags:08x} - PASS")

    # -------------------------------------------------------------------------
    # DG-03: Enqueue order preserved at the queue output
    # -------------------------------------------------------------------------
    log.info("=== Scenario DG-03: FIFO ordering ===")
    n = _S['dg03']
    assert n < 8, "ordering count must stay below default QUEUE_DEPTH"
    seq = []
    for i in range(n):
        src = 0x0000_0000_0000_0100 + i
        dst = 0xFFFF_FFFF_FFFF_FE00 - i
        flags = pack_flags(desc_type=i & 0xF)
        await mbox_write_desc(src, dst, 0x80 + i, 0x10 + i, flags, 0x1000_0000 + i)
        await ring_doorbell()
        seq.append((src, dst, 0x80 + i, 0x10 + i, flags, 0x1000_0000 + i))
    for i, expected_tuple in enumerate(seq):
        desc = await dequeue_desc()
        expected = pack_desc(*expected_tuple)
        assert desc == expected, (
            f"DG-03 order {i}: expected 0x{expected:064x} got 0x{desc:064x}"
        )
        log.info(f"  DG-03 order {i}: 0x{desc:064x} - PASS")

    # -------------------------------------------------------------------------
    # DG-04: Full-queue stall flag
    # -------------------------------------------------------------------------
    log.info("=== Scenario DG-04: full-queue stall ===")
    queue_depth = 8  # matches QUEUE_DEPTH parameter default
    # Fill the queue with the consumer idle.  The last legal push takes the
    # FIFO from 7 to 8 entries, so full (and therefore stall) asserts right
    # after fill index queue_depth-1 — that is the policy signal working, not
    # an error.
    for i in range(queue_depth):
        src = 0xBADC_0FEE_0000_0000 + i
        await mbox_write_desc(src, 0, 0, 0, 0, 0)
        await ring_doorbell()
        # Once data propagates, valid should be high; stall rises only once
        # the final entry has actually landed.
        await Timer(1, units="ns")
        expected_stall = 1 if i == queue_depth - 1 else 0
        assert dut.stall.value == expected_stall, (
            f"DG-04 fill {i}: stall expected {expected_stall}"
        )
    await RisingEdge(dut.clk)
    assert dut.q_valid.value == 1, "DG-04: queue should be non-empty after fills"
    # Doorbell while full -> stall stays high, no data lost.
    await ring_doorbell()
    await RisingEdge(dut.clk)
    assert dut.stall.value == 1, "DG-04: stall did not rise on full-queue doorbell"
    # Additional doorbell while full keeps stall high.
    await ring_doorbell()
    await RisingEdge(dut.clk)
    assert dut.stall.value == 1, "DG-04: stall dropped while queue still full"
    # Drain one entry; stall must clear.
    drained = await dequeue_desc()
    assert (drained >> 192) & ((1 << 64) - 1) == 0xBADC_0FEE_0000_0000, "DG-04: drained wrong descriptor"
    await RisingEdge(dut.clk)
    assert dut.stall.value == 0, "DG-04: stall did not clear after draining one entry"
    # The previously rejected doorbell can now be accepted; the accepted push
    # refills the FIFO to full, so stall is high again immediately after.
    await ring_doorbell()
    await RisingEdge(dut.clk)
    assert dut.stall.value == 1, "DG-04: retry doorbell should refill the queue to full"
    # Drain everything that should be queued: the surviving fills 1..7 plus
    # the retried copy of fill 7's record (mailbox regs still hold it).
    seen = []
    for _ in range(queue_depth):
        seen.append((await dequeue_desc() >> 192) & ((1 << 64) - 1))
    expected_srcs = [0xBADC_0FEE_0000_0000 + i for i in range(1, 8)] + \
                    [0xBADC_0FEE_0000_0000 + 7]
    assert seen == expected_srcs, f"DG-04 drain order wrong: {seen!r}"
    await RisingEdge(dut.clk)
    assert dut.stall.value == 0, "DG-04: stall stuck after draining all entries"
    log.info("  DG-04: full-queue stall behavior - PASS")

    # -------------------------------------------------------------------------
    # DG-05: Doorbell coalescing / back-to-back throughput
    # -------------------------------------------------------------------------
    log.info("=== Scenario DG-05: sustained doorbell throughput ===")
    cycles = _S['dg05']
    beats_received = 0
    last_beat_cycle = -1
    mismatch = None

    async def consumer():
        nonlocal beats_received, last_beat_cycle, mismatch
        cycle = 0
        dut.q_ready.value = 1
        while beats_received < cycles:
            while dut.q_valid.value == 0:
                await RisingEdge(dut.clk)
                cycle += 1
            desc = int(dut.q_desc.value)
            await RisingEdge(dut.clk)
            cycle += 1
            expected_src = 0xCAFE_0000_0000_0000 + beats_received
            expected = pack_desc(expected_src, 0, 0, 0, 0, 0)
            if desc != expected and mismatch is None:
                mismatch = f"DG-05 beat {beats_received}: expected 0x{expected:064x} got 0x{desc:064x}"
            beats_received += 1
            last_beat_cycle = cycle
        dut.q_ready.value = 0

    async def producer():
        for i in range(cycles):
            await mbox_write_desc(0xCAFE_0000_0000_0000 + i, 0, 0, 0, 0, 0)
            await ring_doorbell()

    prod = cocotb.start_soon(producer())
    cons = cocotb.start_soon(consumer())
    await Combine(prod, cons)
    assert mismatch is None, mismatch
    assert beats_received == cycles, f"DG-05: expected {cycles} beats, got {beats_received}"
    log.info(f"  DG-05: {beats_received} back-to-back beats - PASS")

    log.info("=" * 80)
    log.info("hive_descriptor_gen test PASSED")
    log.info("=" * 80)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_hive_descriptor_gen(request, test_level):
    """Pytest wrapper for hive_descriptor_gen TDD test."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    # This is a brand-new block; no registered filelist exists yet.  Pull in
    # the common synchronous FIFO and append the new RTL source.
    fifo_sources, fifo_includes = get_sources_from_filelist(
        repo_root=repo_root, module='fifo_sync'
    )
    rtl_path = os.path.join(
        repo_root,
        'projects/components/compute-eng-ip/hive-serv/rtl/hive_c_controller/descriptor_gen.sv'
    )
    verilog_sources = fifo_sources + [rtl_path]
    includes = fifo_includes

    parameters = {
        'QUEUE_DEPTH': 8,
    }

    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
        "--no-timing",
    ]
    compile_args.extend(get_coverage_compile_args())

    module = os.path.splitext(os.path.basename(__file__))[0]
    tests_dir = os.path.dirname(__file__)
    log_dir = os.path.join(tests_dir, 'logs')
    os.makedirs(log_dir, exist_ok=True)

    test_name = f'test_hive_descriptor_gen_{test_level}'
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)

    run(
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="hive_descriptor_gen",
        module=module,
        parameters=parameters,
        simulator="verilator",
        compile_args=compile_args,
        sim_build=sim_build,
        work_dir=sim_build,
        waves=enable_waves,
        plus_args=['--trace'] if enable_waves else [],
        extra_env={**level_env(test_level)},
    )


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axi_gen_addr
# Purpose: Next-address generation for AXI bursts - FIXED / INCR / WRAP,
#          plus the output-width alignment used by the width converters.
#
# Documentation: docs/markdown/rtl-amba/shared/axi_gen_addr.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-08-17

"""
axi_gen_addr — next-address generation for AXI bursts.

This module is combinational and small, but it is depended on by ~38
files across the repo (every splitter, width converter and DMA slave
that walks a burst), and it had no test of its own. A wrong increment
or a wrong wrap boundary here is the kind of defect that shows up far
downstream as corrupted data on one beat in a burst.

The checks are written against the AXI rules rather than against the
implementation:

* **FIXED** (burst=0) never moves.
* **INCR** (burst=1) advances by 1<<size, except that a narrower output
  bus caps the step at the output width in bytes — that cap is what
  lets an upsizer/downsizer reuse this block.
* **WRAP** (burst=2) keeps the high address bits and wraps within a
  block of (1<<size) * (len+1) bytes, which is the container AXI
  defines for a wrapping burst. Wrap bursts are only legal for power-of-
  two lengths of 2/4/8/16, and those are exercised explicitly.
* **next_addr_align** masks off the output-width byte offset.

Reserved burst 2'b11 is checked to behave as INCR, matching the RTL's
documented default arm.
"""

import os
import random

import pytest
import cocotb
from cocotb.triggers import Timer
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist


# --------------------------------------------------------------------------- #
# golden model — the AXI rules, written independently of the RTL
# --------------------------------------------------------------------------- #

FIXED, INCR, WRAP, RESERVED = 0, 1, 2, 3


def _expected(curr_addr, size, burst, length, aw, odw):
    """(next_addr, next_addr_align) per the AXI addressing rules."""
    mask = (1 << aw) - 1
    odw_bytes = odw // 8

    # A narrower output bus cannot advance further than its own width.
    increment = 1 << size
    if increment > odw_bytes:
        increment = odw_bytes

    if burst == FIXED:
        nxt = curr_addr
    elif burst == WRAP:
        # Container is (1<<size) * (len+1) bytes; the address wraps
        # inside it while the bits above stay put.
        wrap_bytes = (1 << size) * (length + 1)
        wrap_mask = (wrap_bytes - 1) & mask
        aligned = ((curr_addr + increment) & ~(increment - 1)) & mask
        nxt = (curr_addr & ~wrap_mask) | (aligned & wrap_mask)
    else:                                   # INCR and the reserved arm
        nxt = (curr_addr + increment) & mask

    nxt &= mask
    return nxt, nxt & ~((odw_bytes - 1) & mask)


# --------------------------------------------------------------------------- #
# testbench
# --------------------------------------------------------------------------- #

class GenAddrTB(TBBase):

    def __init__(self, dut):
        super().__init__(dut)
        self.AW = self.convert_to_int(os.environ.get('TEST_AW', '32'))
        self.DW = self.convert_to_int(os.environ.get('TEST_DW', '32'))
        self.ODW = self.convert_to_int(os.environ.get('TEST_ODW', '32'))
        self.LEN = self.convert_to_int(os.environ.get('TEST_LEN', '8'))
        self.max_size = (self.DW // 8).bit_length() - 1
        self.errors = 0

    async def check(self, addr, size, burst, length, note=""):
        """Drive one combination and compare both outputs."""
        self.dut.curr_addr.value = addr
        self.dut.size.value = size
        self.dut.burst.value = burst
        self.dut.len.value = length
        await Timer(1, units='ns')          # settle combinational logic

        exp_next, exp_align = _expected(addr, size, burst, length,
                                        self.AW, self.ODW)
        got_next = int(self.dut.next_addr.value)
        got_align = int(self.dut.next_addr_align.value)

        ctx = (f"addr=0x{addr:08X} size={size} burst={burst} len={length}"
               f"{(' ' + note) if note else ''}")
        if got_next != exp_next:
            self.log.error(f"next_addr mismatch: {ctx} "
                           f"got 0x{got_next:08X} exp 0x{exp_next:08X}")
            self.errors += 1
        if got_align != exp_align:
            self.log.error(f"next_addr_align mismatch: {ctx} "
                           f"got 0x{got_align:08X} exp 0x{exp_align:08X}")
            self.errors += 1

    async def test_fixed_never_moves(self):
        """FIXED bursts re-address the same location every beat."""
        for size in range(self.max_size + 1):
            for addr in (0x0000_0000, 0x0000_1000, 0x1234_5678, 0xDEAD_BEE0):
                await self.check(addr & ((1 << self.AW) - 1), size, FIXED, 3,
                                 note="fixed")

    async def test_incr_steps_by_size(self):
        """INCR advances one transfer per beat, capped by the output width."""
        for size in range(self.max_size + 1):
            for addr in (0x0000_0000, 0x0000_0004, 0x0000_0FF8, 0x8000_0000):
                await self.check(addr & ((1 << self.AW) - 1), size, INCR, 7,
                                 note="incr")

    async def test_incr_crosses_4k(self):
        """Stepping over a 4 KB boundary is ordinary arithmetic here --
        this block does not split, and pinning that keeps a 'helpful'
        boundary clamp from being added silently."""
        for size in range(self.max_size + 1):
            step = 1 << size
            await self.check(0x0000_1000 - step, size, INCR, 0, note="pre-4k")
            await self.check(0x0000_0FFF, size, INCR, 0, note="unaligned-4k")

    async def test_wrap_containers(self):
        """WRAP stays inside (1<<size)*(len+1) bytes. AXI only permits
        lengths of 2/4/8/16 for wrapping bursts, so walk exactly those,
        from every start offset inside the container."""
        for length in (1, 3, 7, 15):            # len field = beats-1
            for size in range(self.max_size + 1):
                container = (1 << size) * (length + 1)
                base = 0x0002_0000
                for beat in range(length + 1):
                    await self.check(base + beat * (1 << size), size, WRAP,
                                     length, note=f"wrap c={container}")

    async def test_wrap_returns_to_base(self):
        """Walking a full wrap burst returns to where it started -- the
        property that makes it a wrap rather than an increment.

        The number of steps is container/increment, NOT len+1. Those are
        the same thing only while the transfer fits the output bus. When
        a narrower output caps the increment (DW=64, ODW=32, size=3:
        8-byte transfers stepping 4 bytes at a time) the container takes
        twice as many steps to walk, because that is precisely the
        downsizing case -- one input beat becomes two output beats and
        the caller iterates on the output side.

        Stating it as len+1 asserts the caller's beat count rather than
        the addressing rule, and the first version of this test did
        exactly that and flagged correct RTL.
        """
        odw_bytes = self.ODW // 8
        for length in (1, 3, 7, 15):
            for size in range(self.max_size + 1):
                container = (1 << size) * (length + 1)
                increment = min(1 << size, odw_bytes)
                steps = container // increment
                start = 0x0004_0000 + increment * 2      # mid-container
                addr = start
                for _ in range(steps):
                    self.dut.curr_addr.value = addr
                    self.dut.size.value = size
                    self.dut.burst.value = WRAP
                    self.dut.len.value = length
                    await Timer(1, units='ns')
                    addr = int(self.dut.next_addr.value)
                if addr != start:
                    self.log.error(
                        f"wrap did not close: size={size} len={length} "
                        f"increment={increment} steps={steps} "
                        f"start=0x{start:08X} ended=0x{addr:08X}")
                    self.errors += 1

    async def test_reserved_burst_behaves_as_incr(self):
        """2'b11 is reserved; the RTL's default arm treats it as INCR."""
        for size in range(self.max_size + 1):
            await self.check(0x0000_2000, size, RESERVED, 3, note="reserved")

    async def test_random(self, n=400):
        seed = int(os.environ.get('SEED', '0')) or 0x5EED
        rng = random.Random(seed)
        self.log.info(f"random pass: {n} vectors, seed=0x{seed:X}")
        for _ in range(n):
            await self.check(rng.randrange(1 << self.AW),
                             rng.randrange(self.max_size + 1),
                             rng.choice((FIXED, INCR, WRAP, RESERVED)),
                             rng.choice((0, 1, 3, 7, 15, (1 << self.LEN) - 1)),
                             note="random")


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def axi_gen_addr_test(dut):
    tb = GenAddrTB(dut)
    tb.log.info(f"axi_gen_addr: AW={tb.AW} DW={tb.DW} ODW={tb.ODW} LEN={tb.LEN}")

    await tb.test_fixed_never_moves()
    await tb.test_incr_steps_by_size()
    await tb.test_incr_crosses_4k()
    await tb.test_wrap_containers()
    await tb.test_wrap_returns_to_base()
    await tb.test_reserved_burst_behaves_as_incr()
    await tb.test_random()

    assert tb.errors == 0, f"{tb.errors} mismatch(es) against the AXI model"
    tb.log.info("axi_gen_addr: all vectors match the golden model")


# --------------------------------------------------------------------------- #
# runner
# --------------------------------------------------------------------------- #

# ODW == DW is the plain case; ODW < DW exercises the increment cap that
# the width converters rely on.
params = [
    (32,  32,  32,  8),
    (32,  64,  64,  8),
    (32,  64,  32,  8),     # downsized output: increment must cap
    (32, 128,  32,  8),     # heavier cap
    (40,  64,  64,  8),     # non-32 address width
    (32,  32,  32,  4),     # narrower len field
]


@pytest.mark.parametrize("aw, dw, odw, len_w", params)
def test_axi_gen_addr(request, aw, dw, odw, len_w):
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba_shared': 'rtl/amba/shared',
    })

    dut_name = "axi_gen_addr"
    toplevel = dut_name
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi_gen_addr.f")

    test_name_plus_params = (f"test_{worker_id}_{dut_name}_aw{aw:03d}"
                             f"_dw{dw:03d}_odw{odw:03d}_len{len_w:02d}")
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    rtl_parameters = {
        'AW': str(aw), 'DW': str(dw), 'ODW': str(odw), 'LEN': str(len_w),
    }
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_AW': str(aw), 'TEST_DW': str(dw),
        'TEST_ODW': str(odw), 'TEST_LEN': str(len_w),
        'SEED': str(random.randint(0, 100000)),
    }

    compile_args = ["-Wall", "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"]
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module,
                                   test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
        )
    except Exception as e:
        print(f"axi_gen_addr test failed: {e}")
        print(f"Logs at: {log_path}")
        print(f"View waveforms: {cmd_filename}")
        raise

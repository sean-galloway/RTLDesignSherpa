# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_rlb_top_bringup
# Purpose: Prove the rlb_top MAS programming chapter alone can bring the
#          subsystem up -- driven by a host program, not by the DV helpers.
#
# Documentation: projects/components/retro_legacy_blocks/docs/rlb_top_mas/
# Subsystem: retro_legacy_blocks/rlb_top
#
# Created: 2026-10-03

"""Book-driven bring-up proof for rlb_top (RLB TASK-020, acceptance item 2).

WHY THIS EXISTS: the sequences in
docs/rlb_top_mas/ch04_programming/01_initialization.md were transcribed FROM
the DV helpers (``init_pic``, ``init_pic_cascade``, ``arm_ioapic_pin``). That
makes them correct descriptions of what the DV does -- which is NOT the same
as proving the book alone is sufficient. This test drives bring-up ONLY
through ``dv/host/rlb_bringup_programs.py``, a plain-Python program module in
the repo's host-program shape (cf. the reed-solomon ``rs_loop_programs.py``):
the same layer could later be driven over a ``UARTAxiBridge`` on a board, so
it must not import cocotb, the tbclasses, or the DV helpers it replaces.

The honesty rule for this file: no call to ``RLBTopTB.init_pic``,
``init_pic_cascade``, ``arm_ioapic_pin`` or ``arm_ioapic_for_fabric``. Those
helpers are the transcription SOURCE; calling them here would test the
testbench against itself.

Pattern B per GLOBAL_REQUIREMENTS 2.x: the cocotb entry point is prefixed
``cocotb_test_`` so pytest does not collect it, and the pytest wrapper names
it explicitly via ``testcase=``.
"""

import os
import random
import sys

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.retro_legacy_blocks.dv.tbclasses.rlb_top.rlb_top_tb import RLBTopTB
from projects.components.retro_legacy_blocks.dv.host import rlb_bringup_programs as bringup


class BookBus:
    """Host-program bus protocol over the TB's APB master.

    This is the ONLY adapter the program module sees: ``write32``/``read32``
    raise ``BringUpError`` on PSLVERR so a failed access is loud, never a
    silent zero. A board port of the program would supply the same three
    methods over its own transport.
    """

    def __init__(self, tb: RLBTopTB):
        self.tb = tb

    async def write32(self, addr: int, value: int):
        _, _, pslverr = await self.tb.apb_write(addr & 0xFFFFFFFF,
                                                value & 0xFFFFFFFF)
        if pslverr:
            raise bringup.BringUpError(
                f"APB write 0x{addr & 0xFFFFFFFF:08X} completed with PSLVERR")
        await self.tb.wait_clocks('pclk', 5)

    async def try_read32(self, addr: int):
        _, data, pslverr = await self.tb.apb_read(addr & 0xFFFFFFFF)
        return data, bool(pslverr)

    async def read32(self, addr: int) -> int:
        data, pslverr = await self.try_read32(addr)
        if pslverr:
            raise bringup.BringUpError(
                f"APB read 0x{addr & 0xFFFFFFFF:08X} completed with PSLVERR")
        return data


@cocotb.test(timeout_time=500, timeout_unit="us")
async def cocotb_test_rlb_top_bringup(dut):
    """Bring the subsystem up from the book's program and verify it."""
    tb = RLBTopTB(dut)

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'RLB top book bring-up with seed: {seed}')

    await tb.setup_clocks_and_reset()
    await tb.setup_components()

    bus = BookBus(tb)
    result = await bringup.run_initialization(bus, topology="cascade")

    # Book step 1 / step 6 row 1: every window answered its probe.
    assert len(result.probes) == 10, \
        f"expected 10 window probes, got {len(result.probes)}"
    tb.log.info("book step 1 GREEN: all ten windows answered")

    # Book step 1, second half: an unmapped address completes with PSLVERR.
    _, missed = await bus.try_read32(bringup.RLB_BASE + 10 * bringup.RLB_WINDOW)
    assert missed, "unmapped address did not complete with PSLVERR"
    tb.log.info("book step 1b GREEN: decode miss errors instead of hanging")

    # Book step 6 row 2: each configured controller reports init complete.
    assert result.master_init, "master 8259 did not report init complete"
    assert result.slave_init, "slave 8259 did not report init complete"
    tb.log.info("book step 6a GREEN: both controllers initialised")

    # Book step 6 row 3: the cascade invariant holds at rest.
    assert tb.cascade_invariant_ok(), \
        "master IR2 does not equal the slave's INT before any source fires"
    tb.log.info("book step 6b GREEN: cascade invariant holds")

    # Book steps 5-6 rows 4-5: a route works end to end. Arming the source is
    # BLOCK function (the gpio book), so the TEST does it; the integration
    # program owns everything up to "controllers configured, blocks free".
    for offset, value in ((0x000, 0x3),   # gpio_enable | int_enable
                          (0x010, 0x1),   # INT_ENABLE pin 0
                          (0x014, 0x0),   # INT_TYPE edge
                          (0x018, 0x1),   # INT_POLARITY rising
                          (0x01C, 0x0)):  # INT_BOTH off
        await bus.write32(tb.window_addr(bringup.WIN_GPIO, offset), value)

    tb.clear_ioapic_deliveries()
    tb.dut.gpio_in.value = 0
    await tb.wait_clocks('pclk', 5)
    tb.dut.gpio_in.value = 1
    await tb.wait_clocks('pclk', 40)

    want = bringup.ioapic_vector(bringup.IRQ_GPIO)
    assert tb.pic_int_out(), \
        "GPIO source did not reach pic_int_out through the book's bring-up"
    vectors = [int(getattr(p, 'vector', -1)) for p in tb.ioapic_deliveries()]
    assert want in vectors, \
        f"IOAPIC did not deliver vector 0x{want:02X} (saw {vectors})"
    assert tb.rlb_irq_out(), "rlb_irq_out not asserted while a source is up"
    tb.log.info(f"book step 6c GREEN: GPIO reached the 8259 and the IOAPIC "
                f"delivered vector 0x{want:02X}")

    tb.log.info("All book-driven bring-up checks PASSED")


def generate_test_params():
    """REG_LEVEL selects the grid, as in test_rlb_top."""
    return [(lvl, f"RLB top book bring-up {lvl}") for lvl in reg_level_grid()]


@pytest.mark.parametrize("test_level, description", generate_test_params())
def test_rlb_top_bringup(request, test_level, description):
    """Pytest wrapper -- calls cocotb_test_rlb_top_bringup."""
    module, repo_root_local, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "rlb_top"
    test_name_plus_params = f"test_rlb_top_bringup_{test_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_local,
        filelist_path='projects/components/retro_legacy_blocks/rtl/rlb_top/filelists/rlb_top.f'
    )

    rtl_parameters = {
        'IOAPIC_NUM_IRQS':  '24',
        'HPET_NUM_TIMERS':  '2',
        'PIT_NUM_COUNTERS': '3',
        'GPIO_WIDTH':       '32',
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        **level_env(test_level),
        'TEST_APB_CLOCK_PERIOD': '10',
    }

    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    compile_args = [
        "--trace", "--trace-structs", "--trace-depth", "99",
        "--timescale", "1ns/1ps",
        "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND", "-Wno-CASEINCOMPLETE",
        "-Wno-BLKANDNBLK", "-Wno-MULTIDRIVEN", "-Wno-TIMESCALEMOD",
        "-Wno-MODDUP", "-Wno-GENUNNAMED", "-Wno-PINCONNECTEMPTY",
        "-Wno-UNUSEDSIGNAL", "-Wno-UNUSEDPARAM", "-Wno-SYNCASYNCNET",
        "-Wno-DECLFILENAME", "-Wno-VARHIDDEN",
    ]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_rlb_top_bringup",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=bool(int(os.environ.get('WAVES', '0'))),
        keep_files=True,
        compile_args=compile_args,
    )

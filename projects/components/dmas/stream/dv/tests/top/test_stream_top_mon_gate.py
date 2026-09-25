# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_stream_top_mon_gate
# Purpose: The NEGATIVE direction of the monitor register contract (TASK-002).
#          On a monitors-OFF build the MON window must FAIL, not answer.
#
# WHY A SEPARATE FILE FROM test_stream_top_mon_cfg.py
# ---------------------------------------------------
# That file proves the ON direction: with USE_AXI_MONITORS=1, an APB write by
# name reaches the matching cfg_* port. It cannot cover this direction, because
# the two need different ELABORATIONS of the DUT -- a parameter is not something
# a test can toggle at runtime.
#
# WHAT WAS ACTUALLY WRONG
# -----------------------
# stream_regs.rdl instantiates the monitor regfile unconditionally (MON @ 0x1000)
# while USE_AXI_MONITORS decides whether the monitors it configures exist. With
# monitors off the registers still accepted writes and read back the written
# value, driving nothing. A host arms RDMON_TIMEOUT, reads it back correctly, and
# concludes the monitor is configured. There is no monitor.
#
# That is worse than a silent failure: read-back success is normally the
# strongest evidence a host has that configuration took, so the bus was
# affirmatively lying. It is live on TWO shipping bitstreams --
# Genesys2 build-perf/Makefile:45 and build-obs/Makefile:57 both export
# USE_AXI_MONITORS=0.
#
# WHY THIS TEST GOES THROUGH THE BFM PACKET, NOT tb.read_reg()
# ------------------------------------------------------------
# StreamCoreTB.read_apb_register returns `packet.fields['prdata']` and discards
# the `pslverr` sitting beside it in the same packet, so read_reg STRUCTURALLY
# cannot report an error response. The APB master does capture it
# (apb_components.py: transaction.fields['pslverr'] = bus.PSLVERR), so this file
# builds the APBPacket and calls busy_send directly -- the same thing read_reg
# does internally, minus the discard.
#
# NOTE ON A DEAD CHECK NEXT DOOR: test_stream_top_mon_cfg.py treats 0xDEADBEEF as
# a no-response sentinel. Nothing in this DUT's closure drives that value (it
# appears only as an LFSR_SEED in rtl/amba/shared and as axi4_subtractive_slave's
# READ_FILL), so that branch cannot fire here. Filed for the TASK-003 scrub
# rather than worked around.

import os
import sys

import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.dmas.stream.dv.tbclasses.stream_core_tb import StreamCoreTB

STREAM_TEST_SEED = os.environ.get('RANDOM_SEED', '12345')

# Registers addressed BY NAME; offsets come from stream_regmap.py via the
# RegisterMap, never from a literal. MON regs live at 0x1000+ (paddr[12] set),
# GLOBAL_CTRL at 0x100 (bit 12 clear) -- which is exactly the guard's decode, so
# GLOBAL_CTRL doubles as the control that must keep working.
MON_REGS = ('DAXMON_ENABLE', 'RDMON_ENABLE', 'WRMON_ENABLE')
CONTROL_REG = 'GLOBAL_CTRL'


async def _xfer(tb, addr, write, wdata=0):
    """One APB transfer, returning BOTH prdata and the completer's error flag."""
    from CocoTBFramework.components.apb.apb_packet import APBPacket
    pkt = APBPacket(
        pwrite=1 if write else 0,
        paddr=addr,
        pwdata=wdata,
        pstrb=0xF,
        pprot=0,
        data_width=32,
        addr_width=tb.apb_addr_width,
        strb_width=4,
    )
    # busy_send blocks until PREADY; if the guard wedged the bus by holding
    # cmd_ready low, this never returns and the cocotb timeout fails the test.
    # That is the failure apbx-xbar's APBX-002 found on its own decode miss, and
    # it is the one this guard could plausibly reintroduce.
    await tb.apb4_master.busy_send(pkt)
    await RisingEdge(tb.clk)
    return int(pkt.fields.get('prdata', 0)), int(pkt.fields.get('pslverr', 0))


@cocotb.test(timeout_time=2000, timeout_unit="us")
async def cocotb_test_mon_window_gated(dut):
    """With the monitors not built, the MON window must error rather than answer."""
    tb = StreamCoreTB(dut, apb_addr_width=13)
    await tb.setup_clocks_and_reset()
    await tb.init_apb4_master()

    # ---- VACUITY GUARD -------------------------------------------------------
    # cocotb_bus gates OPTIONAL signals on a case-SENSITIVE hasattr, and this
    # DUT's ports are lowercase (s_apb_pslverr). CocoTBFramework's
    # _match_optional_case shim rebinds them, but if that ever regresses,
    # pslverr silently reads 0 forever and every assertion below passes while
    # checking nothing. Prove the flag is observable before trusting it.
    assert tb.apb4_master.is_signal_present('PSLVERR'), (
        "PSLVERR did not bind on the APB master, so an error response is "
        "invisible to this test and every check below would be vacuous. "
        "This DUT's APB ports are lowercase; see _match_optional_case in "
        "CocoTBFramework/components/apb/apb_components.py.")

    ctrl_addr = tb.reg_offset(CONTROL_REG)
    failures = []

    # ---- POSITIVE CONTROL, BEFORE -------------------------------------------
    # If the bus is broken in this build, every MON check below would "pass" for
    # the wrong reason. Prove a NON-MON register works first.
    _, err = await _xfer(tb, ctrl_addr, write=1, wdata=1)
    if err:
        failures.append(f"{CONTROL_REG} write raised PSLVERR on a monitors-off "
                        f"build -- the bus itself is broken, nothing below means anything")
    rb, err = await _xfer(tb, ctrl_addr, write=0)
    if err or (rb & 1) != 1:
        failures.append(f"{CONTROL_REG} readback failed (0x{rb:X}, pslverr={err}) "
                        f"-- the control register must work for the MON checks to mean anything")

    # ---- THE CONTRACT: the MON window must refuse ---------------------------
    for reg in MON_REGS:
        addr = tb.reg_offset(reg)
        if not (addr >> 12) & 1:
            failures.append(f"{reg} resolved to 0x{addr:X}, which does not set "
                            f"paddr[12] -- the guard decodes on that bit, so this "
                            f"test would not be exercising it")
            continue

        _, werr = await _xfer(tb, addr, write=1, wdata=0x1)
        if not werr:
            failures.append(
                f"{reg} WRITE at 0x{addr:X} completed WITHOUT PSLVERR on a "
                f"monitors-off build -- the register accepted configuration for "
                f"hardware that does not exist")

        rb, rerr = await _xfer(tb, addr, write=0)
        if not rerr:
            failures.append(
                f"{reg} READ at 0x{addr:X} completed WITHOUT PSLVERR on a "
                f"monitors-off build")
        if rb == 0x1:
            failures.append(
                f"{reg} READ BACK the value just written (0x{rb:X}) with the "
                f"monitors not built -- this is the exact lie TASK-002 exists to "
                f"stop: 'not built' must be distinguishable from 'built and zero'")

    # ---- POSITIVE CONTROL, AFTER --------------------------------------------
    # A decode miss must not wedge the bus. apbx-xbar's out-of-range access used
    # to leave cmd_ready low forever, and this guard sits in the same position.
    rb, err = await _xfer(tb, ctrl_addr, write=0)
    if err or (rb & 1) != 1:
        failures.append(f"{CONTROL_REG} broke AFTER the blocked MON accesses "
                        f"(0x{rb:X}, pslverr={err}) -- the guard wedged or "
                        f"corrupted the bus")

    assert not failures, (
        "monitor register window is not gated:\n  " + "\n  ".join(failures)
        + "\n\nUSE_MON_REGS defaults to (USE_AXI_MONITORS != 0) and is "
          "deliberately NOT passed by this test, so a failure here can also "
          "mean that default was broken.")
    tb.log.info("MON window correctly errors with the monitors not built")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_stream_top_mon_gate(request, test_level):
    """Monitors-off build: the MON register window must return an error."""
    module, repo_root_path, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_top': '../../../../rtl/top',
        'rtl_stream_macro': '../../../../rtl/macro',
        'rtl_stream_fub': '../../../../rtl/fub',
        'rtl_amba': '../../../../../rtl/amba',
    })

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_path,
        filelist_path='projects/components/dmas/stream/rtl/filelists/top/stream_top_ch8.f')

    dut_name = "stream_top_ch8"
    rtl_parameters = {
        'NUM_CHANNELS': 4,
        'DATA_WIDTH': 128,
        'AXI_ID_WIDTH': 8,
        # The point of the test. USE_MON_REGS is NOT set here on purpose: it
        # defaults to (USE_AXI_MONITORS != 0), and that derivation is part of
        # what TASK-002 asked for, so the test should exercise it rather than
        # pin it.
        'USE_AXI_MONITORS': 0,
        # 13 bits = 8 KB, so paddr[12] exists and MON at 0x1000+ is addressable.
        # At 12 bits the MON addresses would TRUNCATE into the functional block
        # (WRMON_ENABLE 0x1100 -> 0x100 = GLOBAL_CTRL) and this test would be
        # writing the DMA's global control register instead.
        'APB_ADDR_WIDTH': 13,
    }

    test_name = "test_stream_top_mon_gate"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=os.path.splitext(os.path.basename(__file__))[0],
        testcase="cocotb_test_mon_window_gated",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env={
            **level_env(test_level),
            'DUT': dut_name,
            'NUM_CHANNELS': '4',
            'DATA_WIDTH': '128',
            'APB_ADDR_WIDTH': '13',
            'LOG_PATH': log_path,
            'COCOTB_LOG_LEVEL': 'INFO',
            'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
            'RANDOM_SEED': STREAM_TEST_SEED,
            'COCOTB_RANDOM_SEED': STREAM_TEST_SEED,
        },
        keep_files=True,
        compile_args=["-Wno-fatal", "--timescale", "1ns/1ps",
                      "--unroll-count", "4096", "--unroll-stmts", "20000"],
    )

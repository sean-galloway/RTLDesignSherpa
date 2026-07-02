# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_rapids_beats_top
# Purpose: rapids_beats_top APB -> register -> config smoke test (Pattern B)
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids_beats_top
#
# Author: sean galloway
# Created: 2026-07-02

"""
Smoke test for rapids_beats_top.

Config-only bring-up: instantiate the top with USE_AXI_MONITORS=0, tie off / idle
every non-APB interface, and exercise the APB -> register -> config chain using
BY-NAME register access (RegisterMap + rapids_regmap.py). Proves that
apb_slave -> cmdrsp_router -> peakrdl_to_cmdrsp -> rapids_regs -> rapids_config_block
is alive and that the top is live (system_idle / sched_error readable, no X/hang).

No descriptor kickoff, no data transfers -- nothing that could hang.
"""

import os
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.rapids.dv.tbclasses.rapids_beats_top_tb import (
    RapidsBeatsTopTB, RapidsBeatsTopDatapathTB)


# ===========================================================================
# COCOTB TEST FUNCTIONS - thin; logic lives in the TB
# ===========================================================================

@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_smoke(dut):
    """APB->register->config smoke: by-name read/write-back on base registers."""
    tb = RapidsBeatsTopTB(dut)
    await tb.setup_clocks_and_reset()

    errors = []

    # ---- 1. Read-only sanity: confirm the APB->regblock read path is alive. ----
    # VERSION reset default from rapids_regmap.py: 0x0008005A
    #   MINOR=0x5A [7:0], MAJOR=0x00 [15:8], NUM_CHANNELS=0x08 [23:16]
    version = await tb.read_reg('VERSION')
    if (version & 0xFF) != 0x5A:
        errors.append(f"VERSION MINOR mismatch: got 0x{version:08X}, expected MINOR=0x5A")
    if ((version >> 16) & 0xFF) != tb.NUM_CHANNELS:
        errors.append(f"VERSION NUM_CHANNELS mismatch: got 0x{version:08X}, "
                      f"expected 0x{tb.NUM_CHANNELS:02X}")
    tb.log.info(f"VERSION = 0x{version:08X} (read path alive)")

    # GLOBAL_STATUS is readable (SYSTEM_IDLE reflected in bit 0).
    global_status = await tb.read_reg('GLOBAL_STATUS')
    tb.log.info(f"GLOBAL_STATUS = 0x{global_status:08X}")

    # ---- 2. Write/read-back RW base config registers (0x100-0x3FF). ----
    # (reg_name, write_value, readback_mask) -- mask covers only the RW field bits
    # that read back what was written (RSVD bits read 0).
    checks = [
        ('SCHED_TIMEOUT_CYCLES', 0x0001_2345, 0xFFFF_FFFF),  # full 32-bit RW
        ('DESCENG_ADDR0_BASE',   0xDEAD_BEEF, 0xFFFF_FFFF),  # full 32-bit RW
        ('CHANNEL_ENABLE',       0x0000_00AB, 0x0000_00FF),  # CH_EN[7:0]
        ('GLOBAL_CTRL',          0x0000_0001, 0x0000_0003),  # GLOBAL_EN[0] (avoid RST bit)
    ]

    for reg_name, wr_val, mask in checks:
        await tb.write_reg(reg_name, wr_val)
        rd_val = await tb.read_reg(reg_name)
        exp = wr_val & mask
        got = rd_val & mask
        if got != exp:
            errors.append(f"{reg_name}: wrote 0x{wr_val:08X}, read 0x{rd_val:08X} "
                          f"(masked exp 0x{exp:08X} != got 0x{got:08X})")
        else:
            tb.log.info(f"{reg_name}: write/readback OK (0x{got:08X})")

    # ---- 3. Confirm the top is live: status outputs resolvable (no X/hang). ----
    system_idle, sched_error = tb.read_status_signals()
    # After config-only bring-up nothing was kicked off -> no scheduler errors.
    if sched_error != 0:
        errors.append(f"sched_error non-zero after config-only bring-up: 0x{sched_error:X}")

    assert not errors, "rapids_beats_top smoke errors:\n  " + "\n  ".join(errors)
    tb.log.info("rapids_beats_top smoke PASSED")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_datapath(dut):
    """End-to-end DATAPATH test: config + kickoff over APB (by name), real data
    moved through the top in BOTH directions, verified against memory.

    SOURCE (memory->network): rd_mem is preloaded with a known pattern; the core
      reads it via m_axi_rd, pushes it through the source SRAM, and the TB drains
      it via src_drain -> compared to the preloaded pattern.
    SINK (network->memory): the TB injects a known pattern via snk_fill; the core
      buffers it in the sink SRAM and writes it via m_axi_wr into wr_mem ->
      compared to the injected pattern.
    """
    tb = RapidsBeatsTopDatapathTB(dut)
    await tb.setup_clocks_and_reset()   # clock/reset + APB master + config-by-name + BFMs
    await tb.initialize_test()          # start the source drainer

    # Phase 1: single channel, one descriptor, modest length.
    ok1, stats1 = await tb.test_single_channel(channel=0, beats=8)
    # Phase 2: same channel, two sequential descriptors.
    ok2, stats2 = await tb.test_multi_descriptor(channel=1, beats=6, ndesc=2)

    tb.finalize_test()

    # The top must not have flagged a scheduler error moving real data.
    _, sched_error = tb.read_status_signals()

    tb.log.info(f"datapath phase1={stats1} phase2={stats2} sched_error=0x{sched_error:X}")
    assert ok1, f"single-channel datapath failed: {stats1.get('errors')}"
    assert ok2, f"multi-descriptor datapath failed: {stats2.get('errors')}"
    assert sched_error == 0, f"sched_error non-zero after datapath run: 0x{sched_error:X}"
    tb.log.info("rapids_beats_top datapath PASSED (source + sink verified)")


# ===========================================================================
# PYTEST WRAPPER
# ===========================================================================

def _run_top(testcase, test_name):
    """Shared runner: compile rapids_beats_top and run the given cocotb testcase."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_top_beats': '../../rtl/top_beats',
    })
    dut_name = "rapids_beats_top"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/top_beats/rapids_beats_top.f'
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'NUM_CHANNELS': 8,
        'DATA_WIDTH': 512,
        'ADDR_WIDTH': 64,
        'AXI_ID_WIDTH': 8,
        'SRAM_DEPTH': 512,
        'APB_ADDR_WIDTH': 12,
        'APB_DATA_WIDTH': 32,
        'USE_AXI_MONITORS': 0,
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(12345),
        'TEST_NUM_CHANNELS': '8',
        'TEST_ADDR_WIDTH': '64',
        'TEST_DATA_WIDTH': '512',
        'TEST_AXI_ID_WIDTH': '8',
        'TEST_APB_ADDR_WIDTH': '12',
        'TEST_APB_DATA_WIDTH': '32',
    }

    compile_args = [
        "-Wno-fatal",  # generated rapids_regs.sv trips MULTIDRIVEN/UNOPT; keep warnings non-fatal
        "-Wno-TIMESCALEMOD", "-Wno-WIDTH", "-Wno-UNOPTFLAT", "-Wno-CASEINCOMPLETE",
        "-Wno-MULTIDRIVEN", "-Wno-SELRANGE", "-Wno-UNUSEDSIGNAL",
    ]
    if enable_waves:
        compile_args.extend(['--trace', '--trace-structs', '--trace-max-array', '512'])

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir, os.path.join(repo_root, 'projects/components/rapids/dv/tbclasses')],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase=testcase,
            parameters=rtl_parameters,
            simulator='verilator',
            sim_build=sim_build,
            results_xml=results_path,
            extra_env=extra_env,
            compile_args=compile_args,
            waves=enable_waves,
            keep_files=True,
            plus_args=['--trace'] if enable_waves else [],
        )
        print(f"Test completed! Logs: {log_path}")
    except Exception as e:
        print(f"Test failed: {e}\nLogs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"View: {cmd_filename}")
        raise


@pytest.mark.top_beats
@pytest.mark.rapids_beats_top
def test_rapids_beats_top(request):
    """Config-only smoke: APB -> register -> config chain (by name)."""
    _run_top("cocotb_test_smoke", "test_rapids_beats_top_smoke")


@pytest.mark.top_beats
@pytest.mark.rapids_beats_top
def test_rapids_beats_top_datapath(request):
    """End-to-end datapath: real data moved through the top in both directions."""
    _run_top("cocotb_test_datapath", "test_rapids_beats_top_datapath")


if __name__ == "__main__":
    class MockRequest:
        pass
    test_rapids_beats_top(MockRequest())
    test_rapids_beats_top_datapath(MockRequest())

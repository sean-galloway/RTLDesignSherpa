# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_wb4_master_slave_loop
# Purpose: wb4_master <-> wb4_slave (Wishbone B4 pipelined), driven through
#          the FUB-side valid/ready queues with the GAXI BFMs. Proves both
#          directions, in-order delivery, all three terminations (ACK/ERR/RTY)
#          and the pipelined protocol on the wires between the two blocks.
#
# Documentation: docs/markdown/rtl-amba/wb4/wb4_master.md
# Subsystem: amba
#
# Author: sean galloway
# Created: 2026-09-09
"""
REG_LEVEL controls the parameter sweep, TEST_LEVEL the traffic per test:
    GATE: 1 config, ~200 commands over 3 profile mixes
    FUNC: 2 data widths x shallow/deep queues
    FULL: widths x depths x MAX_OUTSTANDING, ~2000 commands each
"""
import os
import random
from itertools import product

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.amba.wb4_master_slave_loop_tb import WB4MasterSlaveLoopTB
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Profile mixes per phase: (m_cmd, m_rsp, s_cmd, s_rsp). The fourth is the
# one that stalls the response path, which is what the master's credit gate
# exists for; the third stalls the command path, which is what the slave's
# STALL exists for.
PHASES = [
    ('fixed',      'fixed',      'fixed',      'fixed'),
    ('backtoback', 'backtoback', 'backtoback', 'backtoback'),
    ('fast',       'burst_pause', 'fast',      'fast'),
    ('fast',       'fast',       'burst_pause', 'fast'),
    ('constrained', 'constrained', 'constrained', 'constrained'),
    ('burst_pause', 'fast',      'fast',       'burst_pause'),
]
COUNTS = {'gate': 70, 'func': 250, 'full': 400}


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def wb4_master_slave_loop_test(dut):
    """Random commands through the master, answered behind the slave."""
    tb = WB4MasterSlaveLoopTB(dut)
    seed = int(os.environ.get('SEED', '0'))
    rng = random.Random(seed)
    random.seed(seed)
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    if level not in COUNTS:
        level = 'gate'
    tb.log.info(f"seed={seed} level={level}")

    await tb.setup_clocks_and_reset()

    per_phase = COUNTS[level]
    phases = PHASES if level != 'gate' else PHASES[:3]
    total = 0
    for prof in phases:
        tb.set_profiles(*prof)
        ok = await tb.run_traffic(per_phase, rng, mix=0.2)
        total += per_phase
        tb.log.info(f"phase {prof}: {'ok' if ok else 'FAILED'} "
                    f"(responses so far {tb.stats['responses']})")
        if not ok:
            break

    # Every termination has been consumed; the wires must agree.
    await tb.wait_clocks('clk', 20)
    peak = tb.check_wires(total)
    tb.done = True
    passed = tb.report()
    assert passed, f"{len(tb.errors)} error(s); first: {tb.errors[0] if tb.errors else ''}"
    # Non-vacuity: the back-to-back phase must have had more than one transfer
    # in flight, or the pipelined mode was never exercised (classic: exactly one).
    if os.environ.get('CLASSIC', '0') == '1':
        assert peak == 1, f"max_inflight={peak}: classic mode holds one request at a time"
    else:
        assert peak > 1, f"max_inflight={peak}: the bus never pipelined"
    assert tb.stats['ack'] and tb.stats['err'] and tb.stats['rty'], \
        f"not every status exercised: {tb.stats}"


def generate_test_params():
    """(addr_width, data_width, m_depth, s_depth, max_outstanding, classic, hints, test_level)

    `hints` is USE_BURST_HINTS. With it on, the TB drives a CTI/BTE pattern
    into the master's command queue and checks each hint arrives at the
    slave's FUB with its own transfer; with it off the slave's FUB must read
    CLASSIC/LINEAR whatever the master was handed.
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [(32, 32, 4, 2, 16, 0, 0, 'gate'), (32, 32, 4, 2, 16, 0, 1, 'gate'),
                (32, 32, 4, 2, 16, 1, 1, 'gate')]
    if reg_level == 'FUNC':
        return [(32, 32, 4, 2, 16, 0, 0, 'func'),
                (32, 64, 2, 2, 4, 0, 1, 'func'),
                (32, 32, 8, 4, 8, 0, 1, 'func'),
                (32, 32, 4, 2, 16, 1, 0, 'func'),
                (32, 32, 4, 2, 16, 1, 1, 'func')]
    return list(product([32], [32, 64], [2, 4, 8], [2, 4], [2, 16], [0, 1], [0, 1], ['full']))


params = generate_test_params()


@pytest.mark.parametrize("addr_width, data_width, m_depth, s_depth, max_outstanding, "
                         "classic, hints, test_level", params)
def test_wb4_master_slave_loop(request, addr_width, data_width, m_depth, s_depth,
                               max_outstanding, classic, hints, test_level):
    """wb4_master + wb4_slave back to back (rtl/amba/testcode/wb4_master_slave_loop.sv)."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba',
        'rtl_amba_includes': 'rtl/amba/includes',
    })
    dut_name = "wb4_master_slave_loop"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/wb4_master_slave_loop.f")

    tag = (f"aw{TBBase.format_dec(addr_width, 3)}_dw{TBBase.format_dec(data_width, 3)}"
           f"_md{m_depth}_sd{s_depth}_mo{max_outstanding}_{'classic' if classic else 'pipe'}"
           f"_{'hints' if hints else 'nohints'}_{test_level}")
    test_name_plus_params = f"test_{worker_id}_{dut_name}_{tag}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
        'M_CMD_DEPTH': str(m_depth), 'M_RSP_DEPTH': str(m_depth),
        'S_CMD_DEPTH': str(s_depth), 'S_RSP_DEPTH': str(s_depth),
        'MAX_OUTSTANDING': str(max_outstanding), 'CLASSIC': str(classic),
        'USE_BURST_HINTS': str(hints),
    }
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_LEVEL': test_level,
        'ADDR_WIDTH': str(addr_width),
        'DATA_WIDTH': str(data_width),
        'CLASSIC': str(classic),
        'USE_BURST_HINTS': str(hints),
    }
    compile_args = [
        "--trace-fst" if enable_waves else "",
        "--trace-structs" if enable_waves else "",
        "-Wno-DECLFILENAME", "-Wno-UNUSEDPARAM",
    ]
    compile_args = [a for a in compile_args if a]
    sim_args = ["--trace-fst", "--trace-structs"] if enable_waves else []
    plusargs = ["--trace"] if enable_waves else []

    create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=enable_waves,
        keep_files=True,
        compile_args=compile_args,
        sim_args=sim_args,
        plus_args=plusargs,
    )

# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_wb4_master
# Purpose: wb4_master alone. GAXI BFMs on the cmd/rsp queues, the framework
#          WB4Slave answering on the Wishbone side, a WB4Monitor on the wires.
#
# Documentation: docs/markdown/rtl-amba/wb4/wb4_master.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-09-09
"""REG_LEVEL: GATE 1 config; FUNC widths x depths; FULL adds MAX in-flight sweeps.
TEST_LEVEL scales the commands per profile phase."""
import os
import random
from itertools import product

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.amba.wb4_master_tb import WB4MasterTB
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# (cmd GAXI profile, rsp GAXI profile, WB4Slave profile)
# GATE runs the first three phases, and they are chosen so the smoke run is
# not vacuous: phase 2 is the pipelining proof (the FUB consumes every clock,
# the slave terminates late, so the master's credit RSP_DEPTH is the only
# limit on transfers in flight); phase 3 pauses the CONSUMER while the slave
# keeps terminating, which is the only way a missing credit gate shows up --
# without it the response queue overflows and a response is lost. With a
# slower consumer the credit is shared with queued responses and the peak on
# the wires is lower by design.
from wb4_test_common import MASTER_PHASES as PHASES, COUNTS  # noqa: E402


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def wb4_master_test(dut):
    tb = WB4MasterTB(dut)
    seed = int(os.environ.get('SEED', '0'))
    rng = random.Random(seed)
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    level = level if level in COUNTS else 'gate'
    tb.log.info(f"seed={seed} level={level}")
    await tb.setup_clocks_and_reset()
    phases = PHASES if level != 'gate' else PHASES[:3]
    peak = 0
    for prof in phases:
        tb.set_profiles(*prof)
        tb.mon.max_inflight = 0
        ok = await tb.run_traffic(COUNTS[level], rng, mix=0.2)
        tb.log.info(f"phase {prof}: {'ok' if ok else 'FAILED'} max_inflight={tb.mon.max_inflight}")
        peak = max(peak, tb.mon.max_inflight)
        if not ok:
            break
    await tb.wait_clocks('clk', 20)
    passed = tb.report()
    assert passed, f"{len(tb.errors)} error(s); first: {tb.errors[0] if tb.errors else ''}"
    if tb.classic:
        assert peak == 1, f"max_inflight={peak}: classic mode must hold one request at a time"
    else:
        assert peak > 1, f"max_inflight={peak}: never pipelined"
    s = tb.slave.stats
    assert s['ack'] and s['err'] and s['rty'], f"not every status exercised: {s}"
    # The hints are only proven if they were actually on the wires. The
    # monitor is a third party watching m_wb_CTI/m_wb_BTE, so its count is
    # the evidence -- tb.stats counts only what the TB intended to drive.
    if tb.burst_hints:
        assert tb.stats['eob'], "no end-of-burst transfer was driven"
        assert tb.mon.bursts, "the monitor saw no burst hint on the wires"
    else:
        assert not tb.mon.bursts, (
            f"USE_BURST_HINTS=0 must tie the bus to CLASSIC, monitor saw {tb.mon.bursts}")


def generate_test_params():
    """(addr_width, data_width, cmd_depth, rsp_depth, classic, hints, test_level)

    `hints` is USE_BURST_HINTS. Both settings are covered from GATE up,
    because the two are opposite claims about the same wires: with it on the
    monitor must see the pattern the sequence laid, with it off it must see
    CLASSIC/LINEAR whatever the command queue was handed.
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [(32, 32, 4, 4, 0, 0, 'gate'), (32, 32, 4, 4, 0, 1, 'gate'),
                (32, 32, 4, 4, 1, 0, 'gate')]
    if reg_level == 'FUNC':
        return [(32, 32, 4, 4, 0, 0, 'func'), (32, 64, 2, 2, 0, 0, 'func'),
                (32, 32, 8, 8, 0, 0, 'func'), (32, 32, 4, 4, 0, 1, 'func'),
                (32, 64, 2, 2, 0, 1, 'func'),
                (32, 32, 4, 4, 1, 0, 'func'), (32, 64, 2, 2, 1, 0, 'func'),
                (32, 32, 4, 4, 1, 1, 'func')]
    return list(product([32], [32, 64], [2, 4, 8], [2, 4, 8], [0, 1], [0, 1], ['full']))


@pytest.mark.parametrize(
    "addr_width, data_width, cmd_depth, rsp_depth, classic, hints, test_level",
    generate_test_params())
def test_wb4_master(request, addr_width, data_width, cmd_depth, rsp_depth, classic,
                    hints, test_level):
    """wb4_master (rtl/amba/wb4/wb4_master.sv) against the framework Wishbone slave
    in the same mode (pipelined, or classic with CLASSIC=1)."""
    tag = (f"aw{addr_width:03d}_dw{data_width:03d}_cd{cmd_depth}_rd{rsp_depth}"
           f"_{'classic' if classic else 'pipe'}_{'hint' if hints else 'nohint'}_{test_level}")
    _run(request, "wb4_master", "rtl/amba/filelists/wb4_master.f", tag,
         {'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
          'CMD_DEPTH': str(cmd_depth), 'RSP_DEPTH': str(rsp_depth), 'CLASSIC': str(classic),
          'USE_BURST_HINTS': str(hints)},
         {'TEST_LEVEL': test_level, 'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
          'CLASSIC': str(classic), 'USE_BURST_HINTS': str(hints)})

def _run(request, dut_name, filelist, tag, rtl_parameters, extra_env):
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba', 'rtl_amba_includes': 'rtl/amba/includes'})
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=filelist)
    name = f"test_{worker_id}_{dut_name}_{tag}"
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_env.update({
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    })
    compile_args = ["-Wno-DECLFILENAME", "-Wno-UNUSEDPARAM"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, parameters=rtl_parameters, sim_build=sim_build,
        extra_env=extra_env, waves=enable_waves, keep_files=True, compile_args=compile_args,
        sim_args=(["--trace-fst", "--trace-structs"] if enable_waves else []),
        plus_args=(["--trace"] if enable_waves else []))

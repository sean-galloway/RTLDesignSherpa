# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""avmm_to_axil4: Avalon-MM slave in, AXI4-Lite master out.

Phases:
  random        reads and writes over a shared memory model with random
                byteenables and idle gaps, plus an out-of-range window that
                answers SLVERR and must reach Avalon as response 2'b10
  back-to-back  write then read of the same word with no idle clock, which
                is where a sent-flag that clears a clock late shows up
"""
import os
import random
from itertools import product

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from projects.components.utility_ip.converters.dv.tbclasses.avmm_to_axil4_tb import AvmmToAXIL4TB

COUNTS = {'gate': 40, 'func': 150, 'full': 400}


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def cocotb_test_avmm_to_axil4(dut):
    tb = AvmmToAXIL4TB(dut)
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    level = level if level in COUNTS else 'gate'
    n = COUNTS[level]
    rng = random.Random(int(os.environ.get('SEED', '0')))
    await tb.setup_clocks_and_reset()

    ok = await tb.run_traffic(n, rng)
    tb.log.info(f"random: {'ok' if ok else 'FAILED'}")
    if ok:
        ok = await tb.run_back_to_back(rng, pairs=max(4, n // 10))
        tb.log.info(f"back-to-back: {'ok' if ok else 'FAILED'}")

    assert await tb.wait_idle(), "busy never dropped after traffic"
    assert tb.report(), f"{len(tb.errors)} error(s); first: {tb.errors[0] if tb.errors else ''}"
    assert tb.stats['okay'] and tb.stats['slverr'], \
        f"both response kinds must be exercised: {tb.stats}"


def generate_test_params():
    """(addr_width, data_width, wr_delay, rd_delay, test_level)"""
    reg = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg == 'GATE':
        return [(32, 32, 6, 1, 'gate')]
    if reg == 'FUNC':
        return [(32, 32, 6, 1, 'func'), (32, 32, 0, 0, 'func'), (32, 64, 1, 5, 'func')]
    return list(product([32], [32, 64], [0, 6], [0, 5], ['full']))


@pytest.mark.parametrize("addr_width, data_width, wr_delay, rd_delay, test_level",
                         generate_test_params())
def test_avmm_to_axil4(request, addr_width, data_width, wr_delay, rd_delay, test_level):
    """avmm_to_axil4 (projects/components/utility-ip/converters/rtl/avmm_to_axil4.sv)."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/utility-ip/converters/rtl',
        'rtl_amba_includes': 'rtl/amba/includes'})
    dut_name = 'avmm_to_axil4'
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    name = (f"test_{worker_id}_{dut_name}_aw{addr_width:03d}_dw{data_width:03d}"
            f"_wd{wr_delay}_rd{rd_delay}_{test_level}")
    log_path = os.path.join(log_dir, f'{name}.log')
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/utility-ip/converters/rtl/filelists/avmm_to_axil4.f')
    rtl_parameters = {'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width)}
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    extra_env = {
        'TEST_LEVEL': test_level, 'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
        'WR_DELAY': str(wr_delay), 'RD_DELAY': str(rd_delay),
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    compile_args = ["-Wno-DECLFILENAME", "-Wno-UNUSEDPARAM", "-Wno-UNUSEDSIGNAL"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
    create_view_cmd(log_dir, log_path, sim_build, module, name)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_avmm_to_axil4",
        parameters=rtl_parameters, sim_build=sim_build, extra_env=extra_env, waves=enable_waves,
        keep_files=True, compile_args=compile_args,
        sim_args=(["--trace-fst", "--trace-structs"] if enable_waves else []),
        plus_args=(["--trace"] if enable_waves else []))

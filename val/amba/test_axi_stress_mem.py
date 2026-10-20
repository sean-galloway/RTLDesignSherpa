# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""axi4_master_stress on a real memory (the framework's AXI4 slave BFM).

One cocotb test, through bin/TBClasses/amba/axi_stress_mem_tb.py:

  cocotb_test_axi_stress_mem
    1. fill   the write direction sweeps the mem window (cfg fill); the
              memory model must then hold the image axi_stress_model computes
              byte for byte
    2. mix    random reads and writes, narrow and partially strobed, on the
              same window at once: zero errors, and the image unchanged --
              every write carried what the byte already held
    3. fault  one byte of the memory flipped behind the master's back; a read
              sweep (fill on the read direction) must raise RD_DATA at it

TEST_LEVEL sets the mix budget. The window is aligned INCR only: the slave
BFM models no other burst shape (see the TB's docstring).
"""

import os
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.amba.axi_stress_mem_tb import AxiStressMemTB
from TBClasses.amba import axi_stress_model as M

TXNS = {'gate': 150, 'func': 600, 'full': 3000}


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_axi_stress_mem(dut):
    tb = AxiStressMemTB(dut)
    await tb.setup_clocks_and_reset()
    n = TXNS[os.environ.get('TEST_LEVEL', 'gate')]

    # 1. fill
    st = await tb.run(tb.direction(0, enable=0), tb.direction(tb.fill_count(), fill=1))
    tb.log.info(f"fill: {tb.describe(st['wr'])}")
    assert st['wr']['err_mask'] == 0, f"fill: {tb.describe(st['wr'])}"
    assert st['wr']['completed'] == tb.fill_count()
    bad = tb.image_errors()
    assert not bad, 'fill left the memory wrong: ' + '; '.join(bad)

    # 2. mix
    st = await tb.run(tb.direction(n), tb.direction(n))
    for k in ('rd', 'wr'):
        tb.log.info(f"mix {k}: {tb.describe(st[k])}")
        assert st[k]['err_mask'] == 0, f"mix {k}: {tb.describe(st[k])}"
        assert st[k]['completed'] == n, f"mix {k}: {st[k]['completed']} of {n}"
    bad = tb.image_errors()
    assert not bad, 'the mix changed the image: ' + '; '.join(bad)

    # 3. fault
    addr = tb.corrupt()
    st = await tb.run(tb.direction(tb.fill_count(), fill=1), tb.direction(0, enable=0))
    tb.log.info(f"fault at {addr:#010x}: {tb.describe(st['rd'])}")
    assert st['rd']['err_mask'] == 1 << M.ERR_CODES['RD_DATA'], tb.describe(st['rd'])
    assert st['rd']['fe_addr'] == addr & ~3, \
        f"first error at {st['rd']['fe_addr']:#010x}, the flipped byte is at {addr:#010x}"


def _params():
    level = os.environ.get('TEST_LEVEL', 'gate')
    return [64] if level == 'gate' else [32, 64, 128]


@pytest.mark.parametrize("dw", _params())
def test_axi_stress_mem(request, dw):
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba_shared': 'rtl/amba/shared',
    })
    dut_name = "tb_axi_stress_mem"

    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root,
                                                          module='axi4_master_stress')
    verilog_sources = list(verilog_sources) + [os.path.join(tests_dir, "tb_axi_stress_mem.sv")]

    test_level = os.environ.get('TEST_LEVEL', 'gate')
    test_name_plus_params = f"test_{worker_id}_axi_stress_mem_dw{dw:03d}_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    seed = int(os.environ.get('SEED', str(random.randint(0, 100000))))

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_LEVEL': test_level,
        'TEST_DATA_WIDTH': str(dw),
        'TEST_ID_WIDTH': '4',
        'TEST_NWIN': '2',
        'TEST_MEM_LG2': '14',
        'SEED': str(seed),
    }
    compile_args = [
        "-Wall",
        "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC", "-Wno-UNOPTFLAT",
        "-Wno-PINMISSING", "-Wno-PINCONNECTEMPTY", "-Wno-TIMESCALEMOD",
        "-Wno-DECLFILENAME", "-Wno-UNUSEDSIGNAL", "-Wno-GENUNNAMED",
        "-Wno-SYNCASYNCNET", "-Wno-UNUSEDGENVAR", "-Wno-UNUSEDPARAM",
        "-Wno-VARHIDDEN",
    ]
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_axi_stress_mem",
            parameters={'DW': str(dw), 'IW': '4', 'DEPTH': '16', 'NWIN': '2'},
            sim_build=sim_build,
            simulator="verilator",
            extra_env=extra_env,
            waves=enable_waves,
            plus_args=(['--trace'] if enable_waves else []),
            keep_files=True,
            compile_args=compile_args,
        )
    except Exception as e:
        print(f"Test failed: {e}\nLogs: {log_path}\nWaveforms: {cmd_filename}")
        raise

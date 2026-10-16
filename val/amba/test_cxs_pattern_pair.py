# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: tb_cxs_pattern_pair
# Purpose: Test runner for cxs_master_injector -> cxs_slave_pattern_check
#
# Documentation: docs/markdown/rtl-amba/shared/cxs_injectors.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-10-16

"""Runner for the CXS pattern generator/checker pair.

Test intelligence lives in the TB class (`bin/TBClasses/cxs/cxs_pattern_pair_tb.py`,
which reuses the AXIS pair's scenarios and scoreboard); this file holds only
the parameter grid and the cocotb_test.run() call. The DUT is
`val/amba/tb_cxs_pattern_pair.sv`: the injector's CXS link wired straight into
the checker's.
"""

import os
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.cxs.cxs_pattern_pair_tb import CxsPatternPairTB
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cxs_pattern_pair_test(dut):
    tb = CxsPatternPairTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_all()


# Full CXS (with CXSCNTL) has 256/512/1024/2048-bit flits only (IHI 0079D
# rule 6), so the AXIS pair's 128-bit point has no CXS equivalent. At 1024
# bits TSTRB alone fills CXSUSER, so TUSER is dropped (CARRY_TUSER = 0).
params = [
    (4, 512, 32),
    (2, 256, 32),
    (8, 1024, 32),
]


@pytest.mark.parametrize("num_ch, dw, lfsr_w", params)
def test_cxs_pattern_pair(request, num_ch, dw, lfsr_w):
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba_shared': 'rtl/amba/shared',
    })

    dut_name = "tb_cxs_pattern_pair"
    toplevel = dut_name

    gen_sources, gen_inc = get_sources_from_filelist(
        repo_root=repo_root,
        module='cxs_master_injector')
    chk_sources, chk_inc = get_sources_from_filelist(
        repo_root=repo_root,
        module='cxs_slave_pattern_check')

    # Harness last: it instantiates both DUTs.
    verilog_sources = list(dict.fromkeys(list(gen_sources) + list(chk_sources)))
    verilog_sources.append(os.path.join(tests_dir, "tb_cxs_pattern_pair.sv"))
    includes = list(dict.fromkeys(list(gen_inc) + list(chk_inc)))

    test_level = os.environ.get('TEST_LEVEL', 'gate')
    test_name_plus_params = (f"test_{worker_id}_cxs_pattern_pair"
                             f"_ch{num_ch}_dw{dw:03d}_{test_level}")
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    seed = int(os.environ.get('SEED', str(random.randint(0, 100000))))

    rtl_parameters = {
        'NUM_CHANNELS': str(num_ch),
        'AXIS_DATA_WIDTH': str(dw),
        'LFSR_WIDTH': str(lfsr_w),
    }
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_LEVEL': test_level,
        'TEST_NUM_CHANNELS': str(num_ch),
        'TEST_DATA_WIDTH': str(dw),
        'SEED': str(seed),
    }

    # Style-class lint in the DUTs and their LFSR/CRC submodules; not
    # defects, and not this test's job to gate on.
    compile_args = [
        "-Wall",
        "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC", "-Wno-UNOPTFLAT",
        "-Wno-PINMISSING", "-Wno-PINCONNECTEMPTY", "-Wno-TIMESCALEMOD",
        "-Wno-DECLFILENAME", "-Wno-UNUSEDSIGNAL", "-Wno-GENUNNAMED",
        "-Wno-SYNCASYNCNET", "-Wno-UNUSEDGENVAR", "-Wno-UNUSEDPARAM",
        "-Wno-VARHIDDEN",
    ]
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module,
                                   test_name_plus_params)

    try:
        # simulator is pinned, not defaulted: cocotb-test falls back to
        # icarus (via $SIM) when this is omitted, and the oss-cad-suite vvp
        # wrapper forces its own glibc-2.35 libm, which the system
        # libpython3.12 (glibc 2.38+) cannot load against. Every sibling
        # runner in val/amba pins verilator the same way.
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            simulator="verilator",
            extra_env=extra_env,
            waves=enable_waves,
            plus_args=(['--trace'] if enable_waves else []),
            keep_files=True,
            compile_args=compile_args,
        )
    except Exception as e:
        print(f"cxs pattern pair test failed: {e}")
        print(f"Logs at: {log_path}")
        print(f"View waveforms: {cmd_filename}")
        raise

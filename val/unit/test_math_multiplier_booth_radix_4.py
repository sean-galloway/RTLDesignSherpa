import cocotb
import itertools
from cocotb.triggers import RisingEdge, Timer
# from cocotb.regression import TestFactory
from cocotb.clock import Clock

import os
import random
import subprocess
import pytest
from cocotb_test.simulator import run
import logging
from pathlib import Path


def configure_logging(dut_name, log_file_path):
    log = logging.getLogger(f'cocotb_log_{dut_name}')
    log.setLevel(logging.DEBUG)
    fh = logging.FileHandler(log_file_path)
    fh.setLevel(logging.DEBUG)
    formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    fh.setFormatter(formatter)
    log.addHandler(fh)
    return log

@cocotb.test()
async def exhaustive_test(dut):
    # Now that we know where the sim_build directory is, configure logging
    log_path = os.environ.get('LOG_PATH')
    dut_name = os.environ.get('DUT')
    log = configure_logging(dut_name, log_path)
    N = int(os.environ.get('PARAM_N', '0'))
    max_val = 2**(N-1) # only keep the numbers positive
    if N == 4:
        i_list = list(range(max_val))
        j_list = list(range(max_val))
    else:
        count = 128
        i_list = [random.randint(0, max_val-1) for _ in range(count)]
        j_list = [random.randint(0, max_val-1) for _ in range(count)]
    dut.i_multiplier.value = 0
    dut.i_multiplicand.value = 0

    for i in i_list:
        for j in j_list:
            dut.i_multiplier.value = i
            dut.i_multiplicand.value = j

            # Wait a little for the output to be stable
            await Timer(1, units='ns')  # Adding a 100 ps delay

            expected = i * j
            found = dut.ow_product.value.integer
            log.info(f'{max_val=} {i=} {j=} {expected=} {found=}')
            assert expected == found, f"For inputs {hex(i)} and {hex(j)}, expected output was {hex(expected)} but got {hex(found)}"


# factory = TestFactory(exhaustive_test)
# factory.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("n", [4, 16, 32])
def test_math_multiplier_booth_radix_4(request, n):
    dut_name = "math_multiplier_booth_radix_4"   
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_multiplier_booth_radix_4"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_adder_carry_lookahead.sv"),
        os.path.join(rtl_dir, "math_adder_hierarchical.sv"),
        os.path.join(rtl_dir, "math_multiplier_booth_radix_4_encoder.sv"),
        os.path.join(rtl_dir, "math_multiplier_booth_radix_4.sv"),
    ]

    parameters = {'N':n, }

    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

    # sourcery skip: no-conditionals-in-tests
    if request.config.getoption("--regression"):
        sim_build = os.path.join(repo_root, 'val', 'unit', 'regression_area', 'sim_build', request.node.name.replace('[', '-').replace(']', ''))
    else:
        sim_build = os.path.join(repo_root, 'val', 'unit', 'local_sim_build', request.node.name.replace('[', '-').replace(']', ''))

    extra_env['LOG_PATH'] = os.path.join(str(sim_build), f'cocotb_log_{dut_name}.log')
    extra_env['DUT'] = dut_name

    run(
        python_search=[tests_dir],  # where to search for all the python test files
        verilog_sources=verilog_sources,
        toplevel=toplevel,
        module=module,
        parameters=parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=True,
    )

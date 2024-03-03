import cocotb
import itertools
from cocotb.triggers import Timer
from cocotb.result import TestFailure
import os
import subprocess
import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_math_adder_full')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_math_adder_full.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


@cocotb.test()
def full_adder_test(dut):
    """Test for full adder."""
    
    for i, j, k in itertools.product(range(2), range(2), range(2)):
        dut.i_a.value = i
        dut.i_b.value = j
        dut.i_c.value = k

        yield Timer(1, units="ns")

        sum_result = int(dut.ow_sum.value)
        expected_sum = i ^ j ^ k

        carry_result = int(dut.ow_carry.value)
        expected_carry = (i & j) | (i & k) | (j & k)

        if sum_result != expected_sum:
            raise TestFailure(
                f"Mismatch detected! Inputs: {i} {j} {k}. Expected sum: {expected_sum}, Got: {sum_result}"
            )

        if carry_result != expected_carry:
            raise TestFailure(
                f"Mismatch detected! Inputs: {i} {j} {k}. Expected carry: {expected_carry}, Got: {carry_result}"
            )

    yield Timer(1, units="ns")
    log.info("All tests passed!")


from cocotb.regression import TestFactory
tf = TestFactory(full_adder_test)
tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("", [()])
def test_math_adder_full(request, ):
    dut = "math_adder_full"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "math_adder_full"   

    verilog_sources = [
        os.path.join(rtl_dir, "math_adder_full.sv"),

    ]
    parameters = { }

    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}

    # sourcery skip: no-conditionals-in-tests
    if request.config.getoption("--regression"):
        sim_build = os.path.join('regression_area', 'sim_build', request.node.name.replace('[', '-').replace(']', ''))
    else:
        sim_build = os.path.join('local_sim_build', request.node.name.replace('[', '-').replace(']', ''))

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


import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Timer
from cocotb.regression import TestFactory
import os
import subprocess
import pytest
from cocotb_test.simulator import run
import logging
log = logging.getLogger('cocotb_log_shifter_barrel')
log.setLevel(logging.DEBUG)
# Create a file handler that logs even debug messages
fh = logging.FileHandler('cocotb_log_shifter_barrel.log')
fh.setLevel(logging.DEBUG)
# Create a formatter and add it to the handler
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
fh.setFormatter(formatter)
# Add the handler to the logger
log.addHandler(fh)


@cocotb.test()
async def fifo_test(dut):

    dut.i_data.value = 0xFFFF
    dut.i_shift_amount.value = 1
    dut.i_ctrl.value = 0x0
    await Timer(20, units="ns")

    for i in range(17):
        dut.i_data.value = 0xFFFF
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x1
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.i_data.value = 0xFFFF
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x2
        await Timer(20, units="ns")

    await Timer(200, units="ns")
    
    for i in range(17):
        dut.i_data.value = 0x7FFF
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x2
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.i_data.value = 0xA5A5
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x3
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.i_data.value = 0xC3C3
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x3
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.i_data.value = 0x1
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x4
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.i_data.value = 0x3
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x4
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.i_data.value = 0x1
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x6
        await Timer(20, units="ns")

    await Timer(200, units="ns")

    for i in range(17):
        dut.i_data.value = 0x3
        dut.i_shift_amount.value = i
        dut.i_ctrl.value = 0x6
        await Timer(20, units="ns")

    await Timer(200, units="ns")

tf = TestFactory(fifo_test)
tf.generate_tests()

repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

@pytest.mark.parametrize("width", [(16,)])
def test_shifter_barrel(request, width):
    dut = "shifter_barrel"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "shifter_barrel"   

    verilog_sources = [
        os.path.join(rtl_dir, "shifter_barrel.sv"),

    ]
    parameters = {'WIDTH':width, }

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

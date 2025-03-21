import os
import subprocess
import random
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.crc_testing import CRCTB, crc_parameters


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def crc_basic_test(dut):
    """ Test the CRC calculation for a basic input Across 250 Configurations"""
    tb = CRCTB(dut, 100)
    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)
    tb.print_settings()
    tb.generate_test_data()

    await tb.start_clock('i_clk', 10, 'ns')
    tb.assert_reset()
    await tb.wait_clocks('i_clk', 10)
    tb.deassert_reset()
    await tb.wait_clocks('i_clk', 10)
    await tb.main_loop()


repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).strip().decode('utf-8')
tests_dir = os.path.abspath(os.path.dirname(__file__)) #gives the path to the test(current) directory in which this test.py file is placed
rtl_dir = os.path.abspath(os.path.join(repo_root, 'rtl/', 'common')) #path to hdl folder where .v files are placed

# @pytest.mark.parametrize("algo_name, data_width, crc_width, poly, poly_init, refin, refout, xorout", [('CRC-08', 8, 8, "8'h07", "8'h00", 0, 0, "8'h00")])
@pytest.mark.parametrize("algo_name, data_width, crc_width, poly, poly_init, refin, refout, xorout", crc_parameters)
def test_dataint_crc(request, algo_name, data_width, crc_width, poly, poly_init, refin, refout, xorout):
    dut_name = "dataint_crc"
    module = os.path.splitext(os.path.basename(__file__))[0]  # The name of this file
    toplevel = "dataint_crc"   

    verilog_sources = [
        os.path.join(rtl_dir, "dataint_crc_xor_shift.sv"),
        os.path.join(rtl_dir, "dataint_crc_xor_shift_cascade.sv"),
        os.path.join(rtl_dir, "dataint_crc.sv"),
    ]
    includes = []
    parameters = {'ALGO_NAME':algo_name,
                    'DATA_WIDTH':data_width,
                    'CRC_WIDTH':crc_width,
                    'REFIN':refin,
                    'REFOUT':refout,
                    }

    extra_env = {f'PARAM_{k}': str(v) for k, v in parameters.items()}
    extra_env['PARAM_POLY'] = poly
    extra_env['PARAM_POLY_INIT'] = poly_init
    extra_env['PARAM_XOROUT'] = xorout

    sim_build = os.path.join(repo_root, 'val', 'unit_common', 'local_sim_build', request.node.name.replace('[', '-').replace(']', ''))

    extra_env['LOG_PATH'] = os.path.join(str(sim_build), f'cocotb_log_{dut_name}.log')
    extra_env['DUT'] = dut_name

    run(
        python_search=[tests_dir],  # where to search for all the python test files
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=toplevel,
        module=module,
        parameters=parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=True,
    )

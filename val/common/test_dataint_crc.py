import os
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.common.crc_testing import CRCTB, crc_parameters
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


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

    await tb.start_clock('clk', 10, 'ns')
    tb.assert_reset()
    await tb.wait_clocks('clk', 10)
    tb.deassert_reset()
    await tb.wait_clocks('clk', 10)
    await tb.main_loop()



# @pytest.mark.parametrize("params", [
#     # Standard parameter sets from the crc_parameters list
#     {
#         'algo_name': entry[0],
#         'data_width': entry[1],
#         'crc_width': entry[2],
#         'poly': entry[3],
#         'poly_init': entry[4],
#         'refin': entry[5],
#         'refout': entry[6],
#         'xorout': entry[7],
#         'test_level': 'basic'
#     } for entry in crc_parameters
# ])
@pytest.mark.parametrize("params", [
    # Only use the first entry from crc_parameters list
    {
        'algo_name': crc_parameters[0][0],
        'data_width': crc_parameters[0][1],
        'crc_width': crc_parameters[0][2],
        'poly': crc_parameters[0][3],
        'poly_init': crc_parameters[0][4],
        'refin': crc_parameters[0][5],
        'refout': crc_parameters[0][6],
        'xorout': crc_parameters[0][7],
        'test_level': 'basic'
    }
])
def test_dataint_crc(request, params):
    """Run the test with pytest and configurable parameters"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {'rtl_cmn': 'rtl/common'}
    )

    dut_name = "dataint_crc"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "dataint_crc_xor_shift.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "dataint_crc_xor_shift_cascade.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "dataint_crc.sv"),
    ]

    # Create a human-readable test identifier
    algorithm = params['algo_name']
    data_w = params['data_width']
    crc_w = params['crc_width']
    refin = params['refin']
    refout = params['refout']
    t_name = params['test_level']

    test_name_plus_params = f"test_{dut_name}_{algorithm}_DW{data_w}_CW{crc_w}_RI{refin}_RO{refout}_{t_name}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters
    parameters = {
        # 'ALGO_NAME': params['algo_name'],
        'DATA_WIDTH': params['data_width'],
        'CRC_WIDTH': params['crc_width'],
        'REFIN': params['refin'],
        'REFOUT': params['refout'],
    }

    # Prepare environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(0x414347),
        'TEST_LEVEL': params['test_level'],
        'PARAM_POLY': params['poly'],
        'PARAM_POLY_INIT': params['poly_init'],
        'PARAM_XOROUT': params['xorout'],
    }

    # Pass all parameters as environment variables for consistency
    # sourcery skip: no-loop-in-tests
    for k, v in parameters.items():
        extra_env[f'PARAM_{k}'] = str(v)

    # Calculate timeout based on test complexity
    timeout_factor = 50
    extra_env['COCOTB_TIMEOUT_MULTIPLIER'] = str(timeout_factor)


    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    sim_args = [
        "--trace-fst",  # Tell Verilator to use FST
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = [
        "+trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
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
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
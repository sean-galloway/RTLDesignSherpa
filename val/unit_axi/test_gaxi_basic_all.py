"""Universal test runner for all types of AXI buffers using the enhanced framework"""
import os
import random
from dataclasses import dataclass
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.TBClasses.gaxi_basic_all_buffer import GaxiBasicBufferAllTB
from CocoTBFramework.TBClasses.utilities import get_paths, create_view_cmd


@dataclass
class BufferTestParams:
    """Parameters for universal buffer tests"""
    # RTL parameters
    dut_name: str
    buffer_type: str
    data_width: int
    depth: int
    addr_width: int = 0
    ctrl_width: int = 0
    mode: str = 'skid'
    clk_wr_period: int = 10
    clk_rd_period: int = 10
    n_flop_cross: int = 2
    timeout_ms: int = 1
    
    # Test control
    short_test: bool = False
    
    def __post_init__(self):
        """Validate and adjust parameters"""
        # For multi and field types, ensure addr_width and ctrl_width are set
        if self.buffer_type in ['multi', 'field'] and (self.addr_width == 0 or self.ctrl_width == 0):
            # Set default values if not provided
            if self.addr_width == 0:
                self.addr_width = 4
            if self.ctrl_width == 0:
                self.ctrl_width = 3
                
        # For standard buffer, ensure mode is set correctly
        if self.buffer_type == 'standard' and self.dut_name == 'gaxi_skid_buffer':
            # Skid buffer always uses 'skid' mode
            self.mode = 'skid'
            
        # For async buffers, ensure clock periods are set
        if (self.buffer_type == 'async' or 'async' in self.dut_name) and self.clk_wr_period == self.clk_rd_period:
            self.clk_rd_period = self.clk_wr_period + 5


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def buffer_test(dut):
    """Universal test for all GAXI buffer types"""
    # Determine buffer type and other parameters from environment
    buffer_type = os.environ.get('BUFFER_TYPE', 'standard')
    is_async = ('async' in os.environ.get('DUT', '').lower()) or (buffer_type == 'async')
    short_test = os.environ.get('SHORT_TEST', 'false').lower() == 'true'
    
    # Determine clock signals based on async or sync design
    if is_async:
        wr_clk = dut.i_axi_wr_aclk
        wr_rstn = dut.i_axi_wr_aresetn
        rd_clk = dut.i_axi_rd_aclk
        rd_rstn = dut.i_axi_rd_aresetn
    else:
        wr_clk = dut.i_axi_aclk
        wr_rstn = dut.i_axi_aresetn
        rd_clk = None
        rd_rstn = None
    
    # Create the testbench
    tb = GaxiBasicBufferAllTB(
        dut, 
        wr_clk=wr_clk, 
        wr_rstn=wr_rstn,
        rd_clk=rd_clk, 
        rd_rstn=rd_rstn,
        buffer_type=buffer_type
    )
    
    # Set random seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'Using seed: {seed}')
    
    # Start the clock(s)
    await tb.start_clock(tb.wr_clk_name, tb.config.clk_wr_period, 'ns')
    if tb.is_async:
        await tb.start_clock(tb.rd_clk_name, tb.config.clk_rd_period, 'ns')
    
    # Run comprehensive test suite
    await tb.run_comprehensive_test_suite(short_test=short_test)
    
    tb.log.info("All tests completed successfully")


# Helper functions to generate test parameters
def generate_standard_buffer_params():
    """Generate parameters for standard buffer tests"""
    params = []

    # Skid buffer tests
    params.extend(
        BufferTestParams(
            dut_name="gaxi_skid_buffer",
            buffer_type="standard",
            data_width=width,
            depth=depth,
            mode="skid",
        )
        for width, depth in product([8, 16], [2, 4])
    )
    # FIFO tests
    params.extend(
        BufferTestParams(
            dut_name="gaxi_fifo_sync",
            buffer_type="standard",
            data_width=width,
            depth=depth,
            mode=mode,
        )
        for width, depth, mode in product(
            [8], [2, 4], ['fifo_mux', 'fifo_flop']
        )
    )
    return params

def generate_multi_buffer_params():
    """Generate parameters for multi-signal buffer tests"""
    params = []

    # Multi-signal skid buffer tests
    params.extend(
        BufferTestParams(
            dut_name="gaxi_skid_buffer_multi",
            buffer_type="multi",
            addr_width=addr_width,
            ctrl_width=ctrl_width,
            data_width=data_width,
            depth=2,  # Fixed depth for skid buffer
            mode="skid",  # Skid buffer always uses skid mode
        )
        for addr_width, ctrl_width, data_width in product([4, 8], [3, 7], [8])
    )
    # Multi-signal FIFO tests
    params.extend(
        BufferTestParams(
            dut_name="gaxi_fifo_sync_multi",
            buffer_type="multi",
            addr_width=addr_width,
            ctrl_width=ctrl_width,
            data_width=data_width,
            depth=depth,
            mode=mode,
        )
        for addr_width, ctrl_width, data_width, depth, mode in product(
            [4, 6], [3, 5], [8], [2, 4], ['fifo_mux', 'fifo_flop']
        )
    )
    return params

def generate_field_buffer_params():
    """Generate parameters for field-based buffer tests"""
    params = []

    # Field-based FIFO tests - standard FIFO used with multi-field mapping
    params.extend(
        BufferTestParams(
            dut_name="gaxi_fifo_sync",  # Uses standard FIFO with field mapping
            buffer_type="field",
            addr_width=addr_width,
            ctrl_width=ctrl_width,
            data_width=data_width,
            depth=depth,
            mode=mode,
        )
        for addr_width, ctrl_width, data_width, depth, mode in product(
            [6], [9], [8], [2], ['fifo_mux', 'fifo_flop']
        )
    )
    return params

def generate_async_buffer_params():
    """Generate parameters for asynchronous buffer tests"""
    params = []

    # Async FIFO tests
    params.extend(
        BufferTestParams(
            dut_name="gaxi_fifo_async",
            buffer_type="async",
            data_width=width,
            depth=depth,
            mode=mode,
            clk_wr_period=wr_clk,
            clk_rd_period=rd_clk,
        )
        for width, depth, mode, wr_clk, rd_clk in product(
            [8], [2, 4], ['fifo_mux', 'fifo_flop'], [10, 15], [10, 15]
        )
        if wr_clk != rd_clk  # Only keep cases where clocks differ
    )
    # Async skid buffer tests
    params.extend(
        BufferTestParams(
            dut_name="gaxi_skid_buffer_async",
            buffer_type="async",
            data_width=width,
            depth=depth,
            mode=mode,
            clk_wr_period=wr_clk,
            clk_rd_period=rd_clk,
        )
        for width, depth, mode, wr_clk, rd_clk in product(
            [8], [2], ['fifo_mux', 'fifo_flop'], [10, 15], [10, 15]
        )
        if wr_clk != rd_clk  # Only keep cases where clocks differ
    )
    return params

def generate_all_test_params(include_standard=True, include_multi=True, 
                            include_field=True, include_async=True,
                            short_list=False):
    """Generate all test parameters"""
    params = []
    
    if include_standard:
        std_params = generate_standard_buffer_params()
        if short_list:
            # Just pick one from each type
            params.extend([
                std_params[0],  # One skid buffer
                std_params[-1]  # One FIFO
            ])
        else:
            params.extend(std_params)
    
    if include_multi:
        multi_params = generate_multi_buffer_params()
        if short_list:
            # Just pick one from each type
            params.extend([
                multi_params[0],  # One multi skid buffer
                multi_params[-1]  # One multi FIFO
            ])
        else:
            params.extend(multi_params)
    
    if include_field:
        field_params = generate_field_buffer_params()
        if short_list:
            # Just one field buffer
            params.append(field_params[0])
        else:
            params.extend(field_params)
    
    if include_async:
        async_params = generate_async_buffer_params()
        if short_list:
            # Just pick one from each type
            params.extend([
                async_params[0],  # One async FIFO
                async_params[-1]  # One async skid buffer
            ])
        else:
            params.extend(async_params)
    
    # Mark short tests for faster runs
    for param in params:
        param.short_test = short_list
        
    return params

# Comment/uncomment these lines to control which test types to run
# For faster development/debugging, use short_list=True
test_params = generate_all_test_params(
    include_standard=True,
    include_multi=True,
    include_field=True,
    include_async=True,
    short_list=False  # Set to True for faster development runs
)

# Use a single specific test configuration for focused debugging
# uncomment this line and comment the test_params above for quick debugging
# test_params = [BufferTestParams(dut_name='gaxi_skid_buffer', buffer_type='standard', data_width=8, depth=2, short_test=True)]

@pytest.mark.parametrize("params", test_params)
def test_gaxi_buffer(request, params):
    """Universal parametrized test for all AXI buffer types"""
    # Get paths for the test
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common', 
        'rtl_axi': 'rtl/axi'
    })

    # Set up DUT information
    dut_name = params.dut_name
    toplevel = dut_name
    
    # Get Verilog sources based on DUT name
    verilog_sources = get_verilog_sources(rtl_dict, dut_name)

    # Create human-readable test identifier
    test_name = create_test_name(params)
    
    # Set up paths
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')

    # Define RTL parameters based on buffer type
    rtl_parameters = create_rtl_parameters(params)

    # Environment variables
    extra_env = create_env_variables(params, dut_name, log_path, results_path)

    # Create view command for debugging
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    # Run the test
    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[],
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=True,
            keep_files=True
        )
    except Exception as e:
        # If the test fails, preserve logs and provide debugging information
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure


# Helper functions for test configuration

def get_verilog_sources(rtl_dict, dut_name):
    """Get the Verilog source files needed for the specified DUT"""

    if dut_name == 'gaxi_skid_buffer':
        return [
            os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv"),
        ]
    elif dut_name == 'gaxi_skid_buffer_multi':
        return [
            os.path.join(rtl_dict['rtl_axi'], "gaxi_skid_buffer.sv"),
            os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv"),
        ]
    elif dut_name == 'gaxi_fifo_sync':
        return [
            os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
            os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv"),
        ]
    elif dut_name == 'gaxi_fifo_sync_multi':
        return [
            os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
            os.path.join(rtl_dict['rtl_axi'], "gaxi_fifo_sync.sv"),
            os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv"),
        ]
    elif dut_name == 'gaxi_skid_buffer_async':
        return [
            os.path.join(rtl_dict['rtl_cmn'], "find_first_set.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "find_last_set.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "leading_one_trailing_one.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "counter_johnson.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "grayj2bin.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "glitch_free_n_dff_arn.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
            os.path.join(rtl_dict['rtl_axi'], "gaxi_fifo_async.sv"),
            os.path.join(rtl_dict['rtl_axi'], "gaxi_skid_buffer.sv"),
            os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv"),
        ]
    elif dut_name == 'gaxi_fifo_async':
        return [
            os.path.join(rtl_dict['rtl_cmn'], "find_first_set.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "find_last_set.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "leading_one_trailing_one.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "counter_johnson.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "grayj2bin.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "glitch_free_n_dff_arn.sv"),
            os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
            os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv"),
        ]
    else:
        # For any unrecognized DUT, try a basic guess at the required files
        print(f"Unknown DUT type: {dut_name}, using basic source list")
        return [
            os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv"),
        ]

def create_test_name(params):
    """Create a human-readable test identifier from parameters"""
    test_name = f"test_{params.dut_name}_"
    
    if params.buffer_type != 'standard':
        test_name += f"{params.buffer_type}_"
        
    test_name += f"dw{params.data_width:03d}_d{params.depth:03d}"
    
    if params.buffer_type in ['multi', 'field']:
        test_name += f"_aw{params.addr_width:03d}_cw{params.ctrl_width:03d}"
        
    if params.dut_name.startswith('gaxi_fifo'):
        test_name += f"_{params.mode}"
        
    if params.buffer_type == 'async' or 'async' in params.dut_name:
        test_name += f"_wrclk{params.clk_wr_period}_rdclk{params.clk_rd_period}"
        
    return test_name

def create_rtl_parameters(params):
    """Create RTL parameters based on buffer type"""
    if params.buffer_type in ['multi']:
        rtl_parameters = {
            'ADDR_WIDTH': str(params.addr_width),
            'CTRL_WIDTH': str(params.ctrl_width),
            'DATA_WIDTH': str(params.data_width),
            'DEPTH': str(params.depth)
        }
    else:
        rtl_parameters = {
            'DATA_WIDTH': str(params.data_width),
            'DEPTH': str(params.depth)
        }
    if params.buffer_type == 'async' or 'async' in params.dut_name:
        rtl_parameters |= {
            'N_FLOP_CROSS': str(params.n_flop_cross)
        }
        
    return rtl_parameters

def create_env_variables(params, dut_name, log_path, results_path):
    """Create environment variables for the test"""
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_WIDTH': str(params.data_width),
        'TEST_DEPTH': str(params.depth),
        'TEST_MODE': params.mode,
        'BUFFER_TYPE': params.buffer_type,
        'SHORT_TEST': str(params.short_test).lower(),
        'TEST_CLK_WR': str(params.clk_wr_period),
        'TEST_CLK_RD': str(params.clk_rd_period),
        'TEST_N_FLOP_CROSS': str(params.n_flop_cross)
    }
    
    # Add multi-signal parameters if needed
    if params.buffer_type in ['multi', 'field']:
        extra_env['TEST_ADDR_WIDTH'] = str(params.addr_width)
        extra_env['TEST_CTRL_WIDTH'] = str(params.ctrl_width)
        
    return extra_env

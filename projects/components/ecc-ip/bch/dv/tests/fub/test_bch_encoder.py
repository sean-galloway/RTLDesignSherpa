"""
bch_encoder_core test runner

Systematic binary BCH encoder core against the BCHModel golden reference,
through the GAXI master/slave BFMs on the in_/out_ valid/ready ports.
Profiles: CCSDS (63,56) modified BCH at 8 bits/beat, the flash-class
shortened BCH(4224,4120) at 8 bits/beat, and a narrow-sense BCH(63,51).
"""

import os
import sys
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.ecc_ip.bch.dv.tbclasses.bch_encoder_tb import BCHEncoderTB

FILELIST = 'projects/components/ecc-ip/bch/rtl/filelists/bch_encoder_core.f'

# (field_dim, prim_poly, t_bits, n_bits, first_root, bits_per_beat)
PROFILES = [
    (6, 0x43, 1, 63, 0, 8),     # CCSDS (63,56) modified BCH
    (13, 0x201B, 8, 4224, 1, 8),  # flash-class shortened BCH(4224,4120)
    (6, 0x43, 2, 63, 1, 8),     # narrow-sense BCH(63,51)
]


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bch_encoder_core(dut):
    tb = BCHEncoderTB(dut)
    await tb.setup_clocks_and_reset()
    ok = True
    ok &= await tb.run_blocks()
    ok &= await tb.run_backpressure()
    ok &= await tb.run_framing()
    ok &= await tb.run_throughput()
    ok &= await tb.run_no_dead_cycles()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"bch_encoder_core: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("field_dim, prim_poly, t_bits, n_bits, first_root, bits_per_beat", PROFILES)
def test_bch_encoder_core(request, field_dim, prim_poly, t_bits, n_bits, first_root, bits_per_beat, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bch': 'projects/components/ecc-ip/bch/rtl',
    })
    dut_name = "bch_encoder_core"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=FILELIST)

    test_name_plus_params = (f"test_{dut_name}_m{TBBase.format_dec(field_dim, 2)}"
                             f"_n{TBBase.format_dec(n_bits, 4)}"
                             f"_t{TBBase.format_dec(t_bits, 2)}"
                             f"_b{TBBase.format_dec(first_root, 2)}"
                             f"_s{TBBase.format_dec(bits_per_beat, 2)}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        'FIELD_DIM': str(field_dim),
        'PRIM_POLY': str(prim_poly),
        'T_BITS': str(t_bits),
        'N_BITS': str(n_bits),
        'FIRST_ROOT': str(first_root),
        'BITS_PER_BEAT': str(bits_per_beat),
    }
    extra_env = level_env(test_level, DUT=dut_name, LOG_PATH=log_path, COCOTB_LOG_LEVEL='INFO')

    compile_args = ["--trace-fst", "--trace-structs", "--trace-depth", "99"] if enable_waves else []
    sim_args = ["--trace-fst", "--trace-structs"] if enable_waves else []
    plusargs = ["+trace"] if enable_waves else []

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    print(f"\n{'='*60}\nRunning {test_name_plus_params}\nLog: {log_path}\n{'='*60}")
    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_bch_encoder_core",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"PASS {test_name_plus_params}")
    except Exception as e:
        print(f"FAIL {test_name_plus_params}: {e}\nLog: {log_path}\nView: {cmd_filename}")
        raise

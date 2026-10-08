"""
bch_decoder_core test runner

Decodes random and pathological BCH blocks with the decoder core and scores
against bch_model.BCHModel. Profiles mirror the syndrome unit: CCSDS (63,56),
flash-class BCH(4224,4120), and narrow-sense BCH(63,51). The ENABLE_RECHECK=0
variant on the m06 t02 profile exercises the weaker R2 posture.
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

from projects.components.ecc_ip.bch.dv.tbclasses.bch_decoder_core_tb import BCHDecoderCoreTB

FILELIST = 'projects/components/ecc-ip/bch/rtl/filelists/bch_decoder_core.f'

# (field_dim, prim_poly, t_bits, n_bits, first_root, bits_per_beat, enable_recheck)
CONFIGS = [
    (6, 0x43, 1, 63, 0, 8, 1),       # CCSDS (63,56) modified BCH
    (13, 0x201B, 8, 4224, 1, 8, 1),  # flash-class shortened BCH(4224,4120)
    (6, 0x43, 2, 63, 1, 8, 1),       # narrow-sense BCH(63,51)
    (6, 0x43, 2, 63, 1, 8, 0),       # narrow-sense BCH(63,51), re-check OFF
]


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bch_decoder_core(dut):
    tb = BCHDecoderCoreTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run_blocks()
    ok &= await tb.run_framing()
    ok &= await tb.run_over_n()
    ok &= await tb.run_backpressure()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"bch_decoder_core: {report['mismatches']} mismatches in {report['checks']} checks"


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("field_dim, prim_poly, t_bits, n_bits, first_root, bits_per_beat, enable_recheck", CONFIGS)
def test_bch_decoder_core(request, field_dim, prim_poly, t_bits, n_bits, first_root,
                          bits_per_beat, enable_recheck, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bch': 'projects/components/ecc-ip/bch/rtl',
    })
    dut_name = "bch_decoder_core"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=FILELIST)

    test_name_plus_params = (f"test_{dut_name}_m{TBBase.format_dec(field_dim, 2)}"
                             f"_n{TBBase.format_dec(n_bits, 4)}"
                             f"_t{TBBase.format_dec(t_bits, 2)}"
                             f"_s{TBBase.format_dec(bits_per_beat, 2)}"
                             f"_r{enable_recheck}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        'FIELD_DIM': str(field_dim),
        'PRIM_POLY': str(prim_poly),
        'T_BITS': str(t_bits),
        'N_BITS': str(n_bits),
        'BITS_PER_BEAT': str(bits_per_beat),
        'FIRST_ROOT': str(first_root),
        'ENABLE_RECHECK': str(enable_recheck),
    }
    extra_env = level_env(test_level, DUT=dut_name, LOG_PATH=log_path,
                          COCOTB_LOG_LEVEL='INFO')

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
            testcase="cocotb_test_bch_decoder_core",
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

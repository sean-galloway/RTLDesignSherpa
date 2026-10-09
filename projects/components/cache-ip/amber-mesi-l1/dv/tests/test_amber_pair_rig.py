"""
amber pair rig test runner

Task 11 (THE gated deliverable): two amber_top caches + the
amber_pair_fabric snoopy manager + the house sdpram_slave_axi4_axi4 shared
memory, coherent end-to-end -- the PRD's headline deliverable. The DUT is
the rig harness amber_pair_rig_tb (dv/tb/): two full amber tops (CPU GAXI
slaves, AXI4 m_axi rd/wr via the axi4_master_rd/wr_monlite transports, ACE
snoop responders, one MonBus each via the D-7 monbus_arbiter), the pair
fabric between them, and one shared sdpram memory behind it. The TB drives
both CPU ports concurrently and scores the coherence against a 2-cache
Python lockstep model (Task 2 oracle + fabric rules).

Geometries: tiny formal config (16 sets / 2 ways) + pkg default (128/4);
64-bit bus / 64 B lines per the macro-ladder convention. Levels: gate =
directed coherence families (a)-(e); func = + randomized dual-CPU lockstep
(f) + MonBus present-vs-absent (g); full = + dual-CPU soak. A USE_MONITOR=0
gate cell per geometry re-runs the suite asserting observer non-perturbation.

One generated test function per (geometry, level, monitor) cell so the node
ids are the exact required names (test_amber_pair_rig_s016w2_gate et al).

Author: RTL Design Sherpa
Created: 2026-10-09
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

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_pair_rig_tb import (
    AmberPairRigTB,
)

FILELIST_DIR = 'projects/components/cache-ip/amber-mesi-l1/rtl/filelists'
# test-side rig harness (pure wiring + taps; lives with the test, not in an
# RTL filelist -- the same sanctioned pattern as amber_snoop_resp_th.sv)
HARNESS = 'projects/components/cache-ip/amber-mesi-l1/dv/tb/amber_pair_rig_tb.sv'

# (sets, ways, line_bytes, bus_width): tiny formal config + pkg default
GEOMS = [
    (16, 2, 64, 64),
    (128, 4, 64, 64),
]

DUT_TOP = 'amber_pair_rig_tb'
TEST_PREFIX = 'amber_pair_rig'


@cocotb.test(timeout_time=1800, timeout_unit="ms")
async def cocotb_test_amber_pair_rig(dut):
    tb = AmberPairRigTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"amber_pair_rig: {report['mismatches']} mismatches in {report['checks']} checks"


def _run_cell(request, sets, ways, line_bytes, bus_width, test_level, use_monitor):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    # Merge the rig closures: amber_top.f (the whole top closure incl. the
    # core, the monlite transports, the arbiter, the snoop slave, the
    # sdpram) + amber_pair_fabric.f (own source only), dedup'ing
    # order-preserving -- the same merge idiom as the macro suites.
    verilog_sources = []
    includes = []
    for fl in ('amber_top', 'amber_pair_fabric'):
        srcs, incs = get_sources_from_filelist(
            repo_root=repo_root,
            filelist_path=f'{FILELIST_DIR}/{fl}.f')
        for s in srcs:
            if s not in verilog_sources:
                verilog_sources.append(s)
        for i in incs:
            if i not in includes:
                includes.append(i)
    verilog_sources = verilog_sources + [os.path.join(repo_root, HARNESS)]

    # TB working set (mirrors the TB's SPAN formula): the sdpram is sized to
    # it; the runner owns the parameter so the TH needs no TB knowledge.
    set_bits = (sets - 1).bit_length()
    span = min(max(sets * 16, 32 << set_bits, 64), 4096)
    fill_beats = line_bytes // (bus_width // 8)
    mem_depth = span * fill_beats

    mon = 'mon' if use_monitor else 'nomon'
    test_name_plus_params = (
        f"test_{TEST_PREFIX}"
        f"_s{TBBase.format_dec(sets, 3)}w{ways}l{line_bytes}b{bus_width}"
        f"_{mon}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {'SETS': str(sets), 'WAYS': str(ways),
                      'LINE_BYTES': str(line_bytes), 'BUS_WIDTH': str(bus_width),
                      'USE_MONITOR': '1' if use_monitor else '0',
                      'MEM_DEPTH': str(mem_depth)}
    extra_env = level_env(test_level, SETS=sets, WAYS=ways,
                          LINE_BYTES=line_bytes, BUS_WIDTH=bus_width,
                          USE_MONITOR='1' if use_monitor else '0',
                          MEM_DEPTH=mem_depth,
                          DUT=TEST_PREFIX, LOG_PATH=log_path,
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
            toplevel=DUT_TOP,
            module=module,
            testcase="cocotb_test_amber_pair_rig",
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


def _generate_cells():
    """One test function per (geometry, level, monitor) cell -> exact node ids."""
    for sets, ways, line_bytes, bus_width in GEOMS:
        for use_monitor in (True, False):
            for test_level in reg_level_grid():
                if not use_monitor and test_level != 'gate':
                    continue   # the pva cell re-runs the gate suite (scenario g)
                mon = 'mon' if use_monitor else 'nomon'
                name = (f"test_{TEST_PREFIX}"
                        f"_s{TBBase.format_dec(sets, 3)}w{ways}l{line_bytes}b{bus_width}"
                        f"_{mon}_{test_level}")

                def make(s=sets, w=ways, lb=line_bytes, bw=bus_width,
                         um=use_monitor, lvl=test_level, n=name):
                    def _cell(request):
                        _run_cell(request, s, w, lb, bw, lvl, um)
                    _cell.__name__ = n
                    _cell.__doc__ = (f"amber_pair_rig {n}: two ambers + fabric + "
                                     f"shared memory (geometry s{s}/w{w}/l{lb}/b{bw} "
                                     f"monitor={'on' if um else 'off'}, level {lvl})")
                    return _cell

                globals()[name] = make()


_generate_cells()

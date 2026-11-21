"""
onyx pair rig test runner (onyx TASK-001 step 2)

The jet-prime pair rig with onyx_ccu (N_PORTS=2) in jet_prime_pair_fabric's
place: two jet_prime_top caches, onyx between them, one shared
sdpram_slave_axi4_axi4 memory.  The DUT is dv/tb/onyx_pair_rig_tb.sv,
derived from jet_prime_pair_rig_tb with the fabric swapped and the
instance name and debug taps kept, so the jet-prime pair-rig TB
(JetPairRigTB: both CPU ports driven, the 2-cache lockstep model with the
fabric rules, the ACE compliance scoring) runs against onyx unchanged.
Every cell that passed on the fabric is the proof that onyx replaces it;
the grid, levels, geometries and knob sweep are the jet-prime test's
(see test_jet_prime_pair_rig.py).  Node ids:
test_onyx_pair_rig_s016w2l64b64_mon_gate et al.

Author: RTL Design Sherpa
Created: 2026-11-21
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

from projects.components.cache_ip.jet_prime_mesi_l1.dv.tbclasses.jet_prime_pair_rig_tb import (
    JetPairRigTB,
)

JETP_FILELIST_DIR = 'projects/components/cache-ip/jet-prime-mesi-l1/rtl/filelists'
ONYX_FILELIST_DIR = 'projects/components/cache-ip/onyx-ace-ccu/rtl/filelists'
# test-side rig harness (pure wiring + taps; lives with the test, not in an
# RTL filelist -- the same sanctioned pattern as the other tb harnesses)
HARNESS = 'projects/components/cache-ip/onyx-ace-ccu/dv/tb/onyx_pair_rig_tb.sv'

# (sets, ways, line_bytes, bus_width): tiny formal config + pkg default
GEOMS = [
    (16, 2, 64, 64),
    (128, 4, 64, 64),
]

# (mshr_count, victim_depth, repl_policy): the J1/J5/pkg-default cell
DEFAULT_KNOBS = (8, 2, 0)

# FULL-grid policy axis on the rig (amber_repl_t encodings; RANDOM lives
# on the core grid -- see the header note)
RIG_POLICIES = ((0, 'lru'), (2, 'fifo'))
# corners: MSHR {2,16} x VICTIM {1,4}; interior samples at the default
# geometry
CORNER_MSHR = (2, 16)
CORNER_VIC = (1, 4)
INTERIOR = [(4, 2, 0), (8, 2, 2)]

DUT_TOP = 'onyx_pair_rig_tb'
TEST_PREFIX = 'onyx_pair_rig'


@cocotb.test(timeout_time=1800, timeout_unit="ms")
async def cocotb_test_onyx_pair_rig(dut):
    tb = JetPairRigTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, f"onyx_pair_rig: {report['mismatches']} mismatches in {report['checks']} checks"


def _run_cell(request, sets, ways, line_bytes, bus_width, test_level,
              use_monitor, mshr=8, victim=2, repl=0, knob_suffix=''):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})
    # Merge the rig closures: jet_prime_top.f (the whole top closure incl. the
    # jet FUBs, the common-ip slice, the monlite transports, the arbiter,
    # the snoop responder, and the sdpram slave closure) +
    # jet_prime_pair_fabric.f (own source only), dedup'ing order-preserving.
    verilog_sources = []
    includes = []
    for fl in (f'{JETP_FILELIST_DIR}/jet_prime_top.f', f'{ONYX_FILELIST_DIR}/onyx_ccu.f'):
        srcs, incs = get_sources_from_filelist(
            repo_root=repo_root,
            filelist_path=fl)
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
        f"{knob_suffix}_{mon}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {'SETS': str(sets), 'WAYS': str(ways),
                      'LINE_BYTES': str(line_bytes), 'BUS_WIDTH': str(bus_width),
                      'USE_MONITOR': '1' if use_monitor else '0',
                      'MSHR_COUNT': str(mshr), 'VICTIM_DEPTH': str(victim),
                      'REPL_POLICY': str(repl),
                      'MEM_DEPTH': str(mem_depth)}
    extra_env = level_env(test_level, SETS=sets, WAYS=ways,
                          LINE_BYTES=line_bytes, BUS_WIDTH=bus_width,
                          USE_MONITOR='1' if use_monitor else '0',
                          MSHR_COUNT=mshr, VICTIM_DEPTH=victim,
                          REPL_POLICY=repl,
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
            testcase="cocotb_test_onyx_pair_rig",
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
    """One test function per (geometry, level, monitor[, knobs]) cell.

    gate/func: the default-knob cells (mon + the nomon gate re-run), ids
    unchanged.  full (mon only): the default-knob cell (id unchanged)
    plus the ch06/02 sweep -- corners MSHR {2,16} x VICTIM {1,4} x
    {LRU,FIFO} at both geometries, interior samples at the default
    geometry.
    """
    for sets, ways, line_bytes, bus_width in GEOMS:
        for use_monitor in (True, False):
            for test_level in reg_level_grid():
                if not use_monitor and test_level != 'gate':
                    continue   # the pva cell re-runs the gate suite (scenario g)
                # the knob cells of this (geometry, monitor, level)
                if test_level == 'full' and use_monitor:
                    knob_cells = [(DEFAULT_KNOBS, '')]
                    for repl, pol_name in RIG_POLICIES:
                        for mshr in CORNER_MSHR:
                            for victim in CORNER_VIC:
                                knob_cells.append(
                                    ((mshr, victim, repl),
                                     f"_m{TBBase.format_dec(mshr, 2)}"
                                     f"v{victim}_{pol_name}"))
                    if (sets, ways) == (128, 4):
                        for mshr, victim, repl in INTERIOR:
                            pol_name = dict(RIG_POLICIES)[repl]
                            knob_cells.append(
                                ((mshr, victim, repl),
                                 f"_m{TBBase.format_dec(mshr, 2)}"
                                 f"v{victim}_{pol_name}"))
                else:
                    knob_cells = [(DEFAULT_KNOBS, '')]
                for (mshr, victim, repl), suffix in knob_cells:
                    mon = 'mon' if use_monitor else 'nomon'
                    name = (f"test_{TEST_PREFIX}"
                            f"_s{TBBase.format_dec(sets, 3)}w{ways}"
                            f"l{line_bytes}b{bus_width}"
                            f"{suffix}_{mon}_{test_level}")

                    def make(s=sets, w=ways, lb=line_bytes, bw=bus_width,
                             um=use_monitor, lvl=test_level, m=mshr,
                             v=victim, r=repl, sfx=suffix, n=name):
                        def _cell(request):
                            _run_cell(request, s, w, lb, bw, lvl, um,
                                      mshr=m, victim=v, repl=r,
                                      knob_suffix=sfx)
                        _cell.__name__ = n
                        _cell.__doc__ = (
                            f"onyx_pair_rig {n}: two jets + onyx_ccu + shared "
                            f"memory (geometry s{s}/w{w}/l{lb}/b{bw} "
                            f"MSHR={m} VICTIM={v} policy={r} "
                            f"monitor={'on' if um else 'off'}, "
                            f"level {lvl})")
                        return _cell

                    globals()[name] = make()


_generate_cells()

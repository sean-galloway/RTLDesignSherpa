"""
jet cache_sim trace-replay parity grid -- test runner (Task 12)

Grid: {traces} x {LRU, FIFO, RANDOM} x {128/4, 16/2} at the J1 default
knobs (MSHR_COUNT=8, VICTIM_DEPTH=2 -- the MSHR/VICTIM sweep cells pin
the victim way at every alloc against the same policy models under
concurrency; this grid is the cache_sim reference for the policy axis).
Per cell the trace is replayed through jet_top
(dv/tbclasses/jet_parity_tb.py) and hits/misses/compulsory/capacity/
conflict are compared EXACTLY against the cache_sim JS golden model
(bin/apps/cache_sim/js/model.js via amber's dv/golden/
cache_sim_harness.py):

  * LRU / FIFO run the shipped model bytes natively (exact parity)
  * RANDOM runs the recorded LFSR extension (amber's
    dv/golden/cache_sim_lfsr_extension.js) replaying the l1_repl LFSR
    polynomial/seed -- mulberry32 cannot parity natively (amber D-9)

Levels: gate replays the smoke trace only (seq_1k); func and full both
run the complete committed trace set (no per-level scaling -- parity
intensity comes from the traces themselves; the 'full' key must exist
regardless: make/tests.mk's run-all-full-parallel walks every level of
every test file).  Seeds are pinned per test node by the repo-root
conftest; the trace files are deterministic committed artifacts.  The
golden-runner validation cells live with amber's parity suite
(test_amber_parity.py) -- this runner reuses that harness unchanged, and
the wrapper's post-sim golden re-comparison is the defense-in-depth
half of the mechanism here.

Run: pytest dv/tests/test_jet_parity.py -v

Author: RTL Design Sherpa
Created: 2026-10-29
"""

import json
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

from projects.components.cache_ip.jet_mesi_l1.dv.tbclasses.jet_parity_tb import (
    JetParityTB,
)
from projects.components.cache_ip.amber_mesi_l1.dv.golden import (
    cache_sim_harness as golden,
)

JET_FL = 'projects/components/cache-ip/jet-mesi-l1/rtl/filelists'
# test-side harness wrapper (the jet_core harness; the parity TB drives
# the same external shape)
HARNESS = 'projects/components/cache-ip/jet-mesi-l1/dv/tb/jet_core_th.sv'
TRACES_DIR = os.path.join(repo_root,
                          'projects/components/cache-ip/amber-mesi-l1/dv/traces')

# (sets, ways): tiny formal config + pkg default
GEOMS = [(128, 4), (16, 2)]
# (repl_policy, name): amber_repl_t encodings
POLICIES = [(0, 'lru'), (2, 'fifo'), (3, 'rand')]
# committed regression traces (amber dv/traces/gen_traces.py); gate =
# smoke trace only, func and full both run the complete set (the 'full'
# key must exist: make/tests.mk's run-all-full-parallel walks every level)
TRACE_SETS = {
    'gate': ('seq_1k',),
    'func': ('seq_1k', 'strided_8k', 'walk_16k', 'thrash_32k', 'mix_100k'),
    'full': ('seq_1k', 'strided_8k', 'walk_16k', 'thrash_32k', 'mix_100k'),
}

DUT_TOP = 'jet_core_th'
TEST_PREFIX = 'jet_parity'


@cocotb.test(timeout_time=1800, timeout_unit="ms")
async def cocotb_test_jet_parity(dut):
    tb = JetParityTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, (f"jet parity: {report['mismatches']} mismatches in "
                f"{report['checks']} checks; jet={report['totals']} "
                f"cache_sim={report['golden_totals']}")


def _golden_for(trace, sets, ways, line_bytes, repl_policy):
    policy = golden.POLICY_BY_REPL[repl_policy]
    return golden.run_golden(
        trace_path=os.path.join(TRACES_DIR, f'{trace}.txt'),
        sets=sets, ways=ways, line_bytes=line_bytes, policy=policy,
        seed=golden.REPL_SEED if repl_policy == 3 else 1,
        use_extension=repl_policy == 3)


def _run_cell(request, trace, repl_policy, pol_name, sets, ways,
              test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root_, tests_dir, log_dir, rtl_dict = get_paths({})
    verilog_sources = []
    includes = []
    for fl in ('jet_top',):
        srcs, incs = get_sources_from_filelist(
            repo_root=repo_root_, filelist_path=f'{JET_FL}/{fl}.f')
        for s in srcs:
            if s not in verilog_sources:
                verilog_sources.append(s)
        for i in incs:
            if i not in includes:
                includes.append(i)
    verilog_sources = verilog_sources + [os.path.join(repo_root_, HARNESS)]

    test_name_plus_params = (
        f"test_{TEST_PREFIX}_{trace}_{pol_name}"
        f"_s{TBBase.format_dec(sets, 3)}w{ways}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)

    # JS golden totals for this cell (native LRU/FIFO; recorded LFSR
    # extension for RANDOM) -- computed on the pytest side, handed to the
    # TB through the environment, and re-compared after the sim.
    js = _golden_for(trace, sets, ways, 64, repl_policy)
    parity_out = os.path.join(log_dir, f'{test_name_plus_params}.parity.json')

    rtl_parameters = {'SETS': str(sets), 'WAYS': str(ways),
                      'REPL_POLICY': str(repl_policy),
                      'MSHR_COUNT': '8', 'VICTIM_DEPTH': '2'}
    extra_env = level_env(test_level, SETS=sets, WAYS=ways,
                          REPL_POLICY=repl_policy, MSHR_COUNT=8,
                          VICTIM_DEPTH=2,
                          DUT=TEST_PREFIX, LOG_PATH=log_path,
                          COCOTB_LOG_LEVEL='INFO',
                          PARITY_TRACE=os.path.join(TRACES_DIR,
                                                    f'{trace}.txt'),
                          PARITY_EXPECT=json.dumps(js),
                          PARITY_OUT=parity_out)

    compile_args = ["--trace-fst", "--trace-structs", "--trace-depth", "99"] if enable_waves else []
    sim_args = ["--trace-fst", "--trace-structs"] if enable_waves else []
    plusargs = ["+trace"] if enable_waves else []

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    print(f"\n{'='*60}\nRunning {test_name_plus_params}\n"
          f"golden totals: {js['totals']}\nLog: {log_path}\n{'='*60}")
    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=DUT_TOP,
            module=module,
            testcase="cocotb_test_jet_parity",
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

    # defense in depth: re-compare the TB-written report against the JS
    # totals (the TB already asserted this in-sim; a vacuous or lost
    # comparison must not pass silently)
    with open(parity_out, 'r', encoding='utf-8') as fh:
        tb_report = json.load(fh)
    assert tb_report['mismatches'] == 0, \
        f"{test_name_plus_params}: TB logged {tb_report['mismatches']} mismatches"
    diffs = golden.check_totals(tb_report['totals'], tb_report['golden_totals'],
                                label=f'{test_name_plus_params}: ')
    assert not diffs, f'{test_name_plus_params} golden drift:\n' + '\n'.join(diffs)
    assert tb_report['n_accesses'] == js['num_accesses'], \
        f"{test_name_plus_params}: access count {tb_report['n_accesses']} vs " \
        f"golden {js['num_accesses']}"


def _generate_cells():
    """One test function per (trace, policy, geometry, level) cell."""
    for test_level in reg_level_grid():
        for trace in TRACE_SETS[test_level]:
            for repl_policy, pol_name in POLICIES:
                for sets, ways in GEOMS:
                    name = (f"test_{TEST_PREFIX}_{trace}_{pol_name}"
                            f"_s{TBBase.format_dec(sets, 3)}w{ways}"
                            f"_{test_level}")

                    def make(tr=trace, rp=repl_policy, pn=pol_name,
                             s=sets, w=ways, lvl=test_level, n=name):
                        def _cell(request):
                            _run_cell(request, tr, rp, pn, s, w, lvl)
                        _cell.__name__ = n
                        _cell.__doc__ = (f"jet parity {n}: trace {tr} vs "
                                         f"cache_sim (policy {pn}, "
                                         f"geometry {s}/{w}, "
                                         f"level {lvl})")
                        return _cell

                    globals()[name] = make()


_generate_cells()

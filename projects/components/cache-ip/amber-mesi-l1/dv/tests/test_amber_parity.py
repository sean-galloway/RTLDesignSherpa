"""
amber cache_sim trace-replay parity grid -- test runner (Task 10, PRD
success criterion 1)

Grid: {traces} x {LRU, FIFO, RANDOM} x {128/4/64/64, 16/2/64/64}.  Per cell
the trace is replayed through amber_core (dv/tbclasses/amber_parity_tb.py)
and hits/misses/compulsory/capacity/conflict are compared EXACTLY against
the cache_sim JS golden model (bin/apps/cache_sim/js/model.js via
dv/golden/cache_sim_harness.py):

  * LRU / FIFO run the shipped model bytes natively (exact parity)
  * RANDOM runs the recorded LFSR extension (dv/golden/
    cache_sim_lfsr_extension.js, applied to a compiled copy) replaying the
    amber_repl LFSR polynomial/seed -- mulberry32 cannot parity natively
    (DECISION D-9)

Levels: gate replays the smoke trace only (seq_1k); func is the full grid.
Seeds are pinned per test node by the repo-root conftest; the trace files
themselves are deterministic committed artifacts (dv/traces/gen_traces.py,
pinned seeds).

The golden-runner validation cells (no RTL) pin the harness itself:
  * test_amber_parity_golden_app_selftest -- the app's own node suite
    (bin/apps/cache_sim/test/run_tests.js) is green in this environment
  * test_amber_parity_golden_runner -- the app's hand-computed
    run_tests.js expectations are reproduced through THIS harness
  * test_amber_parity_lfsr_extension_pin -- the recorded LFSR extension's
    victim-way sequence bit-matches the Python reference LFSR for several
    associativities and replays every-miss-draw semantics; native mulberry32
    provably differs
  * test_amber_parity_comparator_selfcheck -- the exact-count comparator
    accepts equality and rejects a one-count drift (non-vacuity control)

Run: pytest dv/tests/test_amber_parity.py -v
     make run-amber_parity-func

Author: RTL Design Sherpa
Created: 2026-10-09
"""

import json
import os
import shutil
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

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_parity_tb import (
    AmberParityTB,
)
from projects.components.cache_ip.amber_mesi_l1.dv.golden import (
    cache_sim_harness as golden,
)


FILELIST_DIR = 'projects/components/cache-ip/amber-mesi-l1/rtl/filelists'
DUT_TOP = 'amber_core'
TEST_PREFIX = 'amber_parity'
TRACES_DIR = os.path.join(repo_root,
                          'projects/components/cache-ip/amber-mesi-l1/dv/traces')

# committed regression traces (see dv/traces/gen_traces.py); gate = smoke
TRACE_SETS = {
    'gate': ('seq_1k',),
    'func': ('seq_1k', 'strided_8k', 'walk_16k', 'thrash_32k', 'mix_100k'),
}

# (repl_policy, name): amber_repl_t encodings
POLICIES = [(0, 'lru'), (2, 'fifo'), (3, 'rand')]
GEOMS = [(128, 4, 64, 64), (16, 2, 64, 64)]


@cocotb.test(timeout_time=900, timeout_unit="ms")
async def cocotb_test_amber_parity(dut):
    tb = AmberParityTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run()
    report = tb.get_test_report()
    tb.log.info(f"Test report: {report}")
    assert ok, (f"amber parity: {report['mismatches']} mismatches in "
                f"{report['checks']} checks; amber={report['totals']} "
                f"cache_sim={report['golden_totals']}")


def _golden_for(trace, sets, ways, line_bytes, repl_policy):
    policy = golden.POLICY_BY_REPL[repl_policy]
    return golden.run_golden(
        trace_path=os.path.join(TRACES_DIR, f'{trace}.txt'),
        sets=sets, ways=ways, line_bytes=line_bytes, policy=policy,
        seed=golden.REPL_SEED if repl_policy == 3 else 1,
        use_extension=repl_policy == 3)


def _run_cell(request, trace, repl_policy, pol_name, sets, ways, line_bytes,
              bus_width, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    module, repo_root_, tests_dir, log_dir, rtl_dict = get_paths({})
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path=f'{FILELIST_DIR}/amber_core.f')

    test_name_plus_params = (
        f"test_{TEST_PREFIX}_{trace}_{pol_name}"
        f"_s{TBBase.format_dec(sets, 3)}w{ways}_{test_level}")
    os.makedirs(log_dir, exist_ok=True)   # clean-all removes logs/
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # JS golden totals for this cell (native LRU/FIFO; recorded LFSR
    # extension for RANDOM) -- computed on the pytest side, handed to the
    # TB through the environment, and re-compared after the sim.
    js = _golden_for(trace, sets, ways, line_bytes, repl_policy)
    parity_out = os.path.join(log_dir, f'{test_name_plus_params}.parity.json')

    rtl_parameters = {'SETS': str(sets), 'WAYS': str(ways),
                      'LINE_BYTES': str(line_bytes), 'BUS_WIDTH': str(bus_width),
                      'REPL_POLICY': str(repl_policy)}
    extra_env = level_env(test_level, SETS=sets, WAYS=ways,
                          LINE_BYTES=line_bytes, BUS_WIDTH=bus_width,
                          REPL_POLICY=repl_policy,
                          DUT=TEST_PREFIX, LOG_PATH=log_path,
                          COCOTB_LOG_LEVEL='INFO',
                          PARITY_TRACE=os.path.join(TRACES_DIR, f'{trace}.txt'),
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
            testcase="cocotb_test_amber_parity",
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
                for sets, ways, line_bytes, bus_width in GEOMS:
                    name = (f"test_{TEST_PREFIX}_{trace}_{pol_name}"
                            f"_s{TBBase.format_dec(sets, 3)}w{ways}_{test_level}")

                    def make(tr=trace, rp=repl_policy, pn=pol_name, s=sets,
                             w=ways, lb=line_bytes, bw=bus_width,
                             lvl=test_level, n=name):
                        def _cell(request):
                            _run_cell(request, tr, rp, pn, s, w, lb, bw, lvl)
                        _cell.__name__ = n
                        _cell.__doc__ = (f"amber parity {n}: trace {tr} vs "
                                         f"cache_sim (policy {pn}, geometry "
                                         f"{s}/{w}/{lb}/{bw}, level {lvl})")
                        return _cell

                    globals()[name] = make()


_generate_cells()


# ----------------------------------------------------------------------
# golden-runner validation cells (no RTL; they pin the harness itself)
# ----------------------------------------------------------------------

def test_amber_parity_golden_app_selftest():
    """The app's own node suite must be green in this environment before
    any amber comparison trusts the model."""
    assert shutil.which('node'), 'node >= 18 required for the cache_sim golden'
    out = golden.run_app_selftest()
    assert '# 13/13 passed, 0 failed' in out, \
        f'cache_sim run_tests.js not green:\n{out}'


# (addresses, sets, ways, block_words, policy, expected counts) -- the
# hand-computed expectations copied from bin/apps/cache_sim/test/
# run_tests.js (the app suite's own comments); reproduced here through the
# PARITY harness, so a runner defect cannot hide behind the RTL comparison.
RUNNER_EXPECTATIONS = [
    ([0, 2, 0, 2, 0], 2, 1, 1, 'LRU',
     dict(hits=0, misses=5, compulsory=2, capacity=0, conflict=3)),
    ([0, 2, 0, 2, 0], 2, 2, 1, 'LRU',
     dict(hits=3, misses=2, compulsory=2, capacity=0, conflict=0)),
    ([0, 1, 0, 2, 1], 4, 1, 1, 'LRU',
     dict(hits=2, misses=3, compulsory=3, capacity=0, conflict=0)),
    ([0, 2, 0, 2], 2, 1, 1, 'LRU',
     dict(hits=0, misses=4, compulsory=2, capacity=0, conflict=2)),
    ([0, 2, 4, 0], 2, 1, 1, 'LRU',
     dict(hits=0, misses=4, compulsory=3, capacity=1, conflict=0)),
    ([0, 1, 2, 1, 0, 2], 1, 2, 1, 'LRU',
     dict(hits=1, misses=5, compulsory=3, capacity=2, conflict=0)),
    ([0, 1, 2, 1, 0, 2], 1, 2, 1, 'FIFO',
     dict(hits=2, misses=4, compulsory=3, capacity=1, conflict=0)),
    ([0, 1, 4, 5], 1, 1, 2, 'LRU',
     dict(hits=2, misses=2, compulsory=2, capacity=0, conflict=0)),
    ([0, 1, 2, 0, 1, 2], 1, 2, 1, 'LRU',
     dict(hits=0, misses=6, compulsory=3, capacity=3, conflict=0)),
]


@pytest.mark.parametrize('case', range(len(RUNNER_EXPECTATIONS)),
                         ids=[f'case{i}' for i in range(len(RUNNER_EXPECTATIONS))])
def test_amber_parity_golden_runner(case):
    """Harness reproduces the app's own hand-computed expectations."""
    addrs, sets, ways, block_words, policy, exp = RUNNER_EXPECTATIONS[case]
    line_bytes = block_words * 4
    got = golden.run_golden(addresses=addrs, sets=sets, ways=ways,
                            line_bytes=line_bytes, policy=policy)
    diffs = golden.check_totals(got['totals'], exp)
    assert not diffs, f'runner case {case} drift: {diffs}'
    assert got['num_accesses'] == len(addrs)


def test_amber_parity_lfsr_extension_pin():
    """The recorded extension must bit-match the amber_repl LFSR: victim-way
    sequence equals the Python reference for several associativities, the
    LFSR draws on EVERY miss (fills included, no empty-way preference), and
    native mulberry32 provably differs (the extension is doing real work).
    """
    trace = list(range(16)) + [0, 1, 2, 3]   # 16 fills + 4 revisits (hits)
    for ways in (2, 4, 8):
        ext = golden.run_golden(addresses=trace, sets=1, ways=ways,
                                line_bytes=4, policy='RANDOM',
                                use_extension=True, per_access=True,
                                seed=golden.REPL_SEED)
        got_ways = [pa['way'] for pa in ext['per_access'] if not pa['hit']]
        ref = golden.LfsrRng()
        exp_ways = [ref.next_int(ways) for _ in range(len(got_ways))]
        assert got_ways == exp_ways, \
            f'ways={ways}: extension victim ways {got_ways} != LFSR {exp_ways}'
        # 16 distinct blocks through a ways-deep cache: all 16 compulsory
        # (first-ever), the re-accessed 4 are capacity misses; every miss
        # is an LFSR draw
        assert ext['totals']['compulsory'] == 16
        assert ext['totals']['misses'] == len(got_ways)

    # every-miss-draw (no empty-way preference): the FIRST miss already
    # lands on LFSR draw #1, not on way 0
    first = golden.run_golden(addresses=[7, 8], sets=4, ways=4, line_bytes=4,
                              policy='RANDOM', use_extension=True,
                              per_access=True, seed=golden.REPL_SEED)
    assert first['per_access'][0]['way'] == golden.LfsrRng().next_int(4), \
        'extension used an empty-way preference the RTL does not have'

    # native mulberry32 must differ from the extension somewhere (the
    # patch actually changes the policy)
    trace = list(range(64))
    native = golden.run_golden(addresses=trace, sets=1, ways=4, line_bytes=4,
                               policy='RANDOM', per_access=True,
                               seed=golden.REPL_SEED)
    ext = golden.run_golden(addresses=trace, sets=1, ways=4, line_bytes=4,
                            policy='RANDOM', use_extension=True,
                            per_access=True, seed=golden.REPL_SEED)
    assert [pa['way'] for pa in native['per_access']] != \
           [pa['way'] for pa in ext['per_access']], \
        'native mulberry32 and the LFSR extension agreed bit-for-bit?'


def test_amber_parity_comparator_selfcheck():
    """Non-vacuity control for the exact-count comparator."""
    ok = {k: 10 for k in golden.COUNT_KEYS}
    assert golden.check_totals(dict(ok), dict(ok)) == []
    drifted = dict(ok)
    drifted['conflict'] += 1
    diffs = golden.check_totals(drifted, ok)
    assert len(diffs) == 1 and 'conflict' in diffs[0]

# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_rapids_byte_sim_campaign
# Purpose: The board's host program, unmodified, over the UART sim of
#          rapids_byte_top (rapids TASK-019). Each cell calls
#          run_characterization.main() -- the same argv, descriptor builder,
#          goldens, counters and results-JSON writer as the board -- with the
#          simulated UART as the transport. The only sim/board difference is
#          poll pacing (sim_transport_hook); nothing here re-implements a
#          sequence. Results land under dv/logs and feed
#          host/merge_byte_perf.py -> reports/make_byte_perf_report.py.
#          One sim run is capped at 100 ms of SIM time, so the perf sweep and
#          the long sequences are split into --chunk K/N cells.
#
# Documentation: projects/fpga-systems/Genesys2/rapids/flows-rapids/
# Subsystem: rapids_byte_harness

"""Levels (reg_level_grid): gate = smoke, byte-smoke, each sequence at gate depth
and the quick perf profile; func adds the sequences at func depth and the
standard perf profile; full adds the sequences at full depth and the full
perf profile. Run with TEST_DATA_WIDTH=256 TEST_SRAM_DEPTH=128 (the board)."""

import contextlib
import fcntl
import json
import os
import shlex
import subprocess
import sys

import cocotb
import pytest

from TBClasses.shared.test_levels import reg_level_grid

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rapids_byte_harness_tb import (AxiBurstMonitor, RapidsByteHarnessTB,  # noqa: E402
                                    sim_transport_hook)

LOG_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'logs')
SEQS = ('zero_length', 'boundary_4k', 'tlast_mismatch', 'recovery',
        'axi_resp_error')

# chunk counts keep each sim run under the 100 ms cap (calibrated in uart_ops;
# see the estimate each perf row records). (profile, chunks) per level.
PERF_CHUNKS = {'gate': ('quick', int(os.environ.get('TEST_PERF_CHUNKS_GATE', '1'))),
               'func': ('standard', int(os.environ.get('TEST_PERF_CHUNKS_FUNC', '6'))),
               'full': ('full', int(os.environ.get('TEST_PERF_CHUNKS_FULL', '16')))}
SEQ_CHUNKS = {'gate': 1, 'func': int(os.environ.get('TEST_SEQ_CHUNKS_FUNC', '2')),
              'full': int(os.environ.get('TEST_SEQ_CHUNKS_FULL', '4'))}


def _cases(level):
    """[(case id, argv)] for one depth."""
    cases = []
    if level == 'gate':
        cases += [('smoke', ['--smoke']), ('byte_smoke', ['--byte-smoke'])]
    n = SEQ_CHUNKS[level]
    for seq in SEQS:
        for k in range(1, n + 1):
            cases.append((f'seq_{seq}_{k}of{n}',
                          ['--byte-seq', seq, '--seq-level', level, '--chunk', f'{k}/{n}']))
    profile, nchunk = PERF_CHUNKS[level]
    for k in range(1, nchunk + 1):
        cases.append((f'perf_{profile}_{k}of{nchunk}',
                      ['--byte-perf', '--profile', profile, '--chunk', f'{k}/{nchunk}']))
    return cases


BOARD_CHANNELS = int(os.environ.get('TEST_NUM_CHANNELS', '8'))    # the BUILD register check wants the real count
CELLS = [(lvl, cid, argv) for lvl in reg_level_grid() for cid, argv in _cases(lvl)]


def _rtl_state():
    """Which RTL the sim ran: HEAD plus a digest of uncommitted rapids RTL, so a
    result on an uncommitted working tree says so."""
    root = os.environ.get('REPO_ROOT', '.')
    rtl = 'projects/components/dma-ip/rapids/rtl'
    def git(*a):
        return subprocess.run(['git', '-C', root, *a], capture_output=True, text=True).stdout
    dirty = git('status', '--porcelain', '--', rtl).splitlines()
    return {'head': git('rev-parse', 'HEAD').strip(), 'rtl_dirty_files': len(dirty),
            'rtl_dirty': [ln[3:] for ln in dirty][:40]}


# ===========================================================================
# COCOTB TEST -- thin: main() does everything
# ===========================================================================

# 100 ms of SIM time is the repo cap; TEST_SIM_TIMEOUT_MS may only LOWER it (debug).
SIM_CAP_MS = min(100, int(os.environ.get('TEST_SIM_TIMEOUT_MS', '100')))


@cocotb.test(timeout_time=SIM_CAP_MS, timeout_unit="ms")
async def cocotb_test_campaign(dut):
    """run_characterization.main(argv) over the sim UART, plus the sim-only
    4 KB burst monitor. The 100 ms SIM-time cap is the repo's, never raised."""
    from run_characterization import main
    tb = RapidsByteHarnessTB(dut)
    await tb.setup_clocks_and_reset(configure=False)
    bpb = tb.convert_to_int(os.environ['TEST_DATA_WIDTH']) // 8
    mon = AxiBurstMonitor(dut, bpb)
    cocotb.start_soon(mon.run())
    argv = shlex.split(os.environ['TEST_CAMPAIGN_ARGV'])
    results = os.environ['TEST_CAMPAIGN_RESULTS']
    rc = await cocotb.external(lambda: main(
        argv + ['--results', results], io=tb.io, campaign_hook=sim_transport_hook,
        transport='sim-uart'))()
    if rc != 0 and mon.log_max:
        tb.log.error(f"AXI monitor: {json.dumps(mon.stats)}")
    assert rc == 0, f"run_characterization.main({argv}) returned {rc}"
    with open(results) as fh:
        doc = json.load(fh)
    doc['axi_monitor'] = mon.stats
    doc['rtl_state'] = json.loads(os.environ['TEST_RTL_STATE'])
    with open(results, 'w') as fh:
        json.dump(doc, fh, indent=1)
    assert not mon.stats['violations'], f"4 KB crossings: {mon.stats['violations'][:5]}"
    assert mon.stats['ar_bursts'] + mon.stats['aw_bursts'] > 0, "monitor saw no bursts: blind"


# ===========================================================================
# PYTEST WRAPPER
# ===========================================================================

@contextlib.contextmanager
def _compile_lock(sim_build):
    """One compile at a time per shared sim_build (xdist workers race otherwise)."""
    os.makedirs(os.path.dirname(sim_build), exist_ok=True)
    with open(sim_build + '.lock', 'w') as fh:
        fcntl.flock(fh, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(fh, fcntl.LOCK_UN)


@pytest.mark.rapids_byte_harness
@pytest.mark.parametrize('test_level, case_id, argv', CELLS,
                         ids=[f'{lvl}-{cid}' for lvl, cid, _ in CELLS])
def test_rapids_byte_sim_campaign(request, test_level, case_id, argv):
    """The board's host program (main) over the UART sim, one cell per argv."""
    from test_rapids_byte_harness import _run_harness
    os.makedirs(LOG_DIR, exist_ok=True)
    name = f'byte_sim_{test_level}_{case_id}'
    results = os.path.join(LOG_DIR, f'{name}.json')
    if os.path.exists(results):
        os.remove(results)
    _run_harness('cocotb_test_campaign', name, test_level=test_level,
                 build_name='test_rapids_byte_sim_campaign', compile_first=_compile_lock,
                 module_name='test_rapids_byte_sim_campaign',
                 extra_env={'TEST_CAMPAIGN_ARGV': ' '.join(shlex.quote(a) for a in
                                                               ['--channels', str(BOARD_CHANNELS), *argv]),
                            # a stuck wait must cost ~6 ms of sim, not the 40 ms the sweep's
                            # default poll budget allows, or one hang eats the 100 ms cap
                            'TEST_POLL_MAX_READS': os.environ.get(
                                'TEST_POLL_MAX_READS', '600' if '--byte-seq' in argv else '4000'),
                            'TEST_CAMPAIGN_RESULTS': results,
                            'TEST_RTL_STATE': json.dumps(_rtl_state())})
    assert os.path.isfile(results), f"{name}: the host program wrote no results JSON"


ALIGNED_CHUNKS = int(os.environ.get('TEST_ALIGNED_CHUNKS', '3'))


@pytest.mark.rapids_byte_harness
@pytest.mark.parametrize('chunk', range(1, ALIGNED_CHUNKS + 1), ids=lambda k: f'{k}of{ALIGNED_CHUNKS}')
def test_rapids_byte_sim_aligned_word_crc(request, monkeypatch, chunk):
    """The beat-aligned performance profile on the word-wide-checker flavour of
    the harness (BYTE_CRC=0, BUILD.WORD_CRC=1), the build the "utilization
    unchanged" comparison is measured on. Same host program, same UART sim."""
    from test_rapids_byte_harness import _run_harness
    monkeypatch.setenv('TEST_BYTE_CRC', '0')
    os.makedirs(LOG_DIR, exist_ok=True)
    name = f'byte_sim_aligned_wordcrc_{chunk}of{ALIGNED_CHUNKS}'
    results = os.path.join(LOG_DIR, f'{name}.json')
    if os.path.exists(results):
        os.remove(results)
    argv = ['--byte-perf', '--profile', 'aligned', '--chunk', f'{chunk}/{ALIGNED_CHUNKS}']
    _run_harness('cocotb_test_campaign', name, test_level='gate',
                 build_name='test_rapids_byte_sim_campaign_wordcrc', compile_first=_compile_lock,
                 module_name='test_rapids_byte_sim_campaign',
                 extra_env={'TEST_CAMPAIGN_ARGV': ' '.join(shlex.quote(a) for a in
                                                               ['--channels', str(BOARD_CHANNELS), *argv]),
                            'TEST_POLL_MAX_READS': os.environ.get('TEST_POLL_MAX_READS', '4000'),
                            'TEST_CAMPAIGN_RESULTS': results,
                            'TEST_RTL_STATE': json.dumps(_rtl_state())})
    assert os.path.isfile(results), f"{name}: the host program wrote no results JSON"
    with open(results) as fh:
        doc = json.load(fh)
    assert doc['design']['word_crc'] is True, "the build did not report BUILD.WORD_CRC=1"
    assert all(p['pass'] for p in doc['points']), [p['id'] for p in doc['points'] if not p['pass']]

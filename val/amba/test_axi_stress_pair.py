# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""axi{4,3,5}_master_stress -> axi{4,3,5}_slave_stress, back to back.

Two cocotb tests, both through bin/TBClasses/amba/axi_stress_pair_tb.py:

  cocotb_test_axi_stress_clean   one traffic scenario (TEST_TYPE) at the
      TEST_LEVEL budget; passes only if both blocks report zero errors, the
      independent bus monitor agrees with every beat, the budget moved in full
      on both sides, and the scenario's feature (reordering, interleaving,
      partial strobes, error responses) was actually seen on the wire.
  cocotb_test_axi_stress_faults  each of the harness's one-shot faults (eight;
      nine with AXI3, which adds a flipped WID; nineteen with AXI5, which adds
      flipped ARTRACE, AWMECID, WPOISON, RTRACE, RPOISON, BTRACE, RIDUNQ, BIDUNQ,
      a forced ARIDUNQ on a busy ID, a corrupted atomic read-return and a
      reserved AWATOP) must raise the error the blocks claim it raises.

TEST_PROTO picks the shells (axi4 | axi3 | axi5); the cores and every check
are the same. With AXI3 no burst may be longer than 16 beats, and the monitor
checks WID against the AWID of the burst each beat belongs to. With AXI5 both
shells carry NSAID, TRACE, MPAM, MECID, POISON, UNIQUE and ATOMIC, every window is a sideband
path and one beat in four is poisoned; the monitor checks every field, and a
run must have poisoned beats in both directions.
"""

import os
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.amba.axi_stress_pair_tb import AxiStressPairTB
from TBClasses.amba import axi_stress_model as M

TXNS = {'gate': 150, 'func': 600, 'full': 3000}
SLV_BASE, SLV_LG2 = 0x0000_0000, 20
ERR_BASE, ERR_LG2 = 0x0008_0000, 16


def _windows(tag, *, err=False, narrow=False, aligned=False):
    full = dict(len_mask=0xFF, size_min=0 if narrow else 7, size_max=7,
                unaligned=0 if aligned else 1, strb_rand=1 if narrow else 0)
    wins = [M.Window(SLV_BASE, 19, tag, **full)]
    if err:
        wins.append(M.Window(ERR_BASE, ERR_LG2, tag, resp=M.SLVERR, **full))
    return wins


AXI5_POISON_LG2 = 2      # one beat in four
AXI5_ATOM_LG2 = 2        # one write burst in four becomes an atomic


def _scenario(name, n, tag, proto='axi4'):
    """(windows, master rd/wr cfg, slave rd/wr cfg) for one scenario."""
    m = dict(enable=1, txn_count=n, id_base=0x30, id_mask=0x0F,
             timeout_lg2=16, max_out=0)
    s = dict(base=SLV_BASE, size_lg2=SLV_LG2, tag=tag, err_en=1,
             err_base=ERR_BASE, err_mask=(~((1 << ERR_LG2) - 1)) & M.M32)
    wins = _windows(tag)
    if name == 'inorder':
        s.update(inorder=1)
        m.update(id_mask=0x03)
    elif name == 'ooo':
        s.update(lat_mask=0x3F)
    elif name == 'interleave':
        s.update(interleave=1, lat_mask=0x1F, req_throttle=4, data_throttle=6)
        m.update(resp_throttle=5, data_throttle=3, gap_mask=0x03, qos_rand=1)
    elif name == 'narrow':
        wins = _windows(tag, narrow=True)
        s.update(lat_mask=0x0F, data_throttle=3)
    elif name == 'errwin':
        wins = _windows(tag, err=True)
        s.update(lat_mask=0x0F)
    elif name == 'one_id':
        s.update(lat_mask=0x3F, interleave=1)
        m.update(id_mask=0, max_out=4)
    else:
        raise ValueError(f'unknown scenario {name}')
    if proto == 'axi5':
        for w in wins:
            w.sb, w.poison_lg2, w.atomic = 1, AXI5_POISON_LG2, 1
        s.update(sb_src=0x01, poison_lg2=AXI5_POISON_LG2)
        m.update(idunq=1, atom_lg2=AXI5_ATOM_LG2)
    return wins, dict(m, seed=0x1111_0000 + n), dict(m, seed=0x2222_0000 + n), \
        dict(s, seed=0x3333), dict(s, seed=0x4444)


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_axi_stress_clean(dut):
    tb = AxiStressPairTB(dut)
    name = os.environ.get('TEST_TYPE', 'ooo')
    n = TXNS.get(tb.TEST_LEVEL, TXNS['gate'])
    await tb.setup_clocks_and_reset()
    wins, mrd, mwr, srd, swr = _scenario(name, n, tag=0x5A, proto=tb.PROTO)
    tb.configure(wins, mrd, mwr, srd, swr)
    await tb.wait_clocks('aclk', 2)
    await tb.go()
    # ~50 beats per burst behind throttles: the limit scales with the budget
    s = await tb.wait_done(timeout_cycles=max(200_000, 400 * n))
    tb.log.info(f'{name}: monitor {dict(tb.stats)}\n{tb.describe(s)}')

    for k in ('mrd', 'mwr', 'srd', 'swr'):
        assert s[k]['err_mask'] == 0 and s[k]['err_cnt'] == 0, \
            f'{k} reported errors:\n{tb.describe(s)}'
    assert not tb.mon_errors, f'monitor: {len(tb.mon_errors)} errors, first {tb.mon_errors[0]}'
    for k in ('mrd', 'mwr'):
        assert s[k]['issued'] == n and s[k]['completed'] == n, \
            f'{k}: issued {s[k]["issued"]} completed {s[k]["completed"]} of {n}'
    assert s['srd']['bursts'] == n and s['swr']['bursts'] == n
    for k in ('mrd', 'mwr'):      # mean <= max: LAT_SUM must not have wrapped or saturated
        assert 0 < s[k]['lat_sum'] <= s[k]['lat_max'] * s[k]['completed'], \
            f"{k}: lat_sum {s[k]['lat_sum']} vs max {s[k]['lat_max']} x {s[k]['completed']}"
    assert tb.stats['ar'] == n and tb.stats['aw'] == n and tb.stats['b'] == n
    assert tb.stats['r_beats'] == s['mrd']['beats'] == s['srd']['beats']
    assert tb.stats['w_beats'] == s['mwr']['beats'] == s['swr']['beats']
    if tb.PROTO == 'axi3':
        assert tb.stats['max_len'] == 15, \
            f"AXI3: longest burst AxLEN {tb.stats['max_len']}, expected exactly 15"
    else:
        assert tb.stats['max_len'] > 15, f'{tb.PROTO}: no burst longer than 16 beats'
    if tb.PROTO == 'axi5':
        assert tb.stats['sb_req'] == 2 * n, f"AXI5: {tb.stats['sb_req']} requests checked"
        assert tb.stats['r_poison'] > 0 and tb.stats['w_poison'] > 0, \
            'AXI5: no beat was poisoned in one direction'
        assert tb.stats['r_poison'] < tb.stats['r_beats'], 'AXI5: every R beat poisoned'
        assert tb.stats['uq_ar'] > 0 and tb.stats['uq_aw'] > 0, \
            'AXI5: no burst was issued with AxIDUNQ in one direction'
        for c in ('store', 'load', 'swap', 'compare'):
            assert tb.stats[f'atom_{c}'] > 0, f'AXI5: no Atomic{c.capitalize()} issued'
        assert tb.stats['atom_rr'] == (tb.stats['atom_load'] + tb.stats['atom_swap']
                                       + tb.stats['atom_compare']), \
            'AXI5: a read-return atomic got no R beat (or one too many)'

    if name in ('ooo', 'interleave', 'narrow', 'errwin'):
        assert tb.stats['r_ooo'] > 0, 'no read completed out of order'
    if name == 'inorder':
        assert tb.stats['r_ooo'] == 0, 'an in-order slave reordered'
    if name in ('interleave', 'one_id'):
        if name == 'interleave':
            assert tb.stats['r_interleave'] > 0, 'no R beats interleaved'
        else:
            assert tb.stats['r_interleave'] == 0 and tb.stats['r_ooo'] == 0, \
                'one ID must complete in order and never interleave'
    if name == 'narrow':
        assert tb.stats['w_partial_strb'] > 0, 'no partial strobes were sent'
    if name == 'errwin':
        assert tb.stats['r_err_beats'] > 0 and tb.stats['b_err'] > 0, \
            'the error window answered no SLVERR'
        assert tb.stats['r_err_beats'] < tb.stats['r_beats'], 'every read errored'
    else:
        assert tb.stats['r_err_beats'] == 0 and tb.stats['b_err'] == 0


FAULTS = [
    # (bit, status block, error bits any of which proves detection)
    (0, 'mrd', {'RD_DATA'}),
    (1, 'mrd', {'RD_STRAY', 'RD_LAST', 'RD_DATA', 'RD_RESP'}),
    (2, 'mrd', {'RD_LAST'}),
    (3, 'swr', {'S_WDATA'}),
    (4, 'mwr', {'WR_STRAY', 'WR_EARLY'}),
    (5, 'srd', {'S_ADDR'}),
    (6, 'mwr', {'WR_RESP'}),
    (7, 'mrd', {'RD_RESP'}),
]
FAULTS_AXI3 = [(8, 'swr', {'S_WID'})]
FAULTS_AXI5 = [(9, 'srd', {'S_SB'}), (10, 'swr', {'S_SB'}), (11, 'mrd', {'M_SB'}),
               (12, 'mrd', {'M_SB'}), (13, 'mwr', {'M_SB'}), (14, 'swr', {'S_SB'}),
               (15, 'mrd', {'M_SB'}), (16, 'mwr', {'M_SB'}), (17, 'srd', {'S_SB'}),
               (18, 'mwr', {'RD_DATA'}), (19, 'swr', {'S_PROTO'})]
FAULTS_BY_PROTO = {'axi4': [], 'axi3': FAULTS_AXI3, 'axi5': FAULTS_AXI5}


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_axi_stress_faults(dut):
    tb = AxiStressPairTB(dut)
    for bit, blk, expect in FAULTS + FAULTS_BY_PROTO[tb.PROTO]:
        await tb.setup_clocks_and_reset()
        wins, mrd, mwr, srd, swr = _scenario('ooo', 0, tag=0x5A, proto=tb.PROTO)  # until STOP
        tb.configure(wins, mrd, mwr, srd, swr)
        await tb.wait_clocks('aclk', 2)
        await tb.go()
        await tb.wait_clocks('aclk', 200)
        clean = tb.status()
        assert all(clean[k]['err_mask'] == 0 for k in clean), \
            f'errors before fault {bit}:\n{tb.describe(clean)}'
        await tb.pulse('flt_arm', 1 << bit)
        for _ in range(5000):
            await tb.wait_clocks('aclk', 1)
            if (int(dut.flt_done.value) >> bit) & 1:
                break
        else:
            raise AssertionError(f'fault {bit} never found a handshake to corrupt')
        await tb.wait_clocks('aclk', 400)
        await tb.pulse('stop')
        await tb.wait_clocks('aclk', 50)
        s = tb.status()
        got = set(M.err_list(s[blk]['err_mask']))
        tb.log.info(f'fault {bit}: {blk} {sorted(got)}')
        assert got & expect, \
            f'fault {bit}: {blk} raised {sorted(got)}, expected one of {sorted(expect)}\n' \
            f'{tb.describe(s)}'
        assert s[blk]['fe_valid'], f'fault {bit}: no first-error capture'
        tb.reset_monitor()


PROTO_CODE = {'axi4': 0, 'axi3': 1, 'axi5': 2}


def _params():
    level = os.environ.get('TEST_LEVEL', 'gate')
    dws = [64] if level == 'gate' else [32, 64, 128]
    scen = ['inorder', 'ooo', 'interleave', 'narrow', 'errwin', 'one_id']
    out = []
    for proto in PROTO_CODE:
        out += [(proto, dw, 'clean', sc) for dw in dws for sc in scen]
        out += [(proto, dw, 'faults', '-') for dw in dws]
    return out


@pytest.mark.parametrize("proto, dw, kind, scenario", _params())
def test_axi_stress_pair(request, proto, dw, kind, scenario):
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba_shared': 'rtl/amba/shared',
    })
    dut_name = "tb_axi_stress_pair"

    m_src, m_inc = get_sources_from_filelist(repo_root=repo_root, module=f'{proto}_master_stress')
    s_src, s_inc = get_sources_from_filelist(repo_root=repo_root, module=f'{proto}_slave_stress')
    verilog_sources = list(dict.fromkeys(list(m_src) + list(s_src)))
    verilog_sources.append(os.path.join(tests_dir, "tb_axi_stress_pair.sv"))
    includes = list(dict.fromkeys(list(m_inc) + list(s_inc)))

    test_level = os.environ.get('TEST_LEVEL', 'gate')
    tag = scenario if kind == 'clean' else 'faults'
    test_name_plus_params = f"test_{worker_id}_axi_stress_pair_{proto}_dw{dw:03d}_{tag}_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    seed = int(os.environ.get('SEED', str(random.randint(0, 100000))))

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1' if enable_waves else '0',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_LEVEL': test_level,
        'TEST_TYPE': scenario,
        'TEST_DATA_WIDTH': str(dw),
        'TEST_NWIN': '8',
        'TEST_PROTO': proto,
        'SEED': str(seed),
    }
    compile_args = [
        "-Wall",
        "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC", "-Wno-UNOPTFLAT",
        "-Wno-PINMISSING", "-Wno-PINCONNECTEMPTY", "-Wno-TIMESCALEMOD",
        "-Wno-DECLFILENAME", "-Wno-UNUSEDSIGNAL", "-Wno-GENUNNAMED",
        "-Wno-SYNCASYNCNET", "-Wno-UNUSEDGENVAR", "-Wno-UNUSEDPARAM",
        "-Wno-VARHIDDEN",
    ]
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase=f"cocotb_test_axi_stress_{kind}",
            parameters={'DW': str(dw), 'IW': '8', 'DEPTH': '16', 'NWIN': '8',
                        'PROTO': str(PROTO_CODE[proto])},
            sim_build=sim_build,
            simulator="verilator",
            extra_env=extra_env,
            waves=enable_waves,
            plus_args=(['--trace'] if enable_waves else []),
            keep_files=True,
            compile_args=compile_args,
        )
    except Exception as e:
        print(f"Test failed: {e}\nLogs: {log_path}\nWaveforms: {cmd_filename}")
        raise

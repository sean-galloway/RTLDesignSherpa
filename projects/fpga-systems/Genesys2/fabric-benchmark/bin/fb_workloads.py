# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""The DDR3 workloads (PRD §4.1) as one CRC-checked chain, for sim and board.

W2 needs no memory; the others read or write DDR3 (S0), where nothing computes
a CRC. So they run as a chain in which every step ends in a CRC verdict at the
sink -- the DE10 PRD's C1 loop, extended through W4:

    w1_f2  LFSR source -> DDR3 region A    fill     (records the LFSR CRCs)
    w1_f1  DDR3 A      -> CRC sink         drain    sink CRC == w1_f2's, per channel
    w4     DDR3 A      -> DDR3 region B    copy
    w4_f1  DDR3 B      -> CRC sink         drain    sink CRC == w1_f2's, per channel

A step's own verdict is: the run completed (the timer stopped on its
destination's last beat), and the S0 beat counters saw exactly the transfer
in each direction the step crosses S0 -- so a run cannot pass by moving data
somewhere else. The two drains carry the data check.

fb_ctl's WORKLOAD register tells the run timer which endpoints to watch;
STREAM's descriptors (this builder's bases) choose where the data actually
goes. Both are set from the same step entry below, so they cannot disagree.

Region B starts right after region A's last channel, so a short chain uses
little memory (the sim models S0 densely) and an 8-channel chain still fits
the 1 GB device.
"""
from __future__ import annotations

import importlib.util
from functools import lru_cache
from pathlib import Path

import fb_map

FB_CTL_BASE = 0x0020_0000          # bridge_fb_cfg.toml, window fb_ctl
DDR_A_BASE = 0x0000_0000           # S0
REGION_ALIGN = 1 << 20

_REGMAP = (Path(__file__).resolve().parent.parent
           / 'rtl' / 'regs' / 'generated' / 'fb_ctl_regs_regmap.py')

# (step, source, destination); 'lfsr' / 'snk' are S2 / S3, 'A' / 'B' DDR3.
CHAIN = (('w1_f2', 'lfsr', 'A'),
         ('w1_f1', 'A', 'snk'),
         ('w4', 'A', 'B'),
         ('w4_f1', 'B', 'snk'))
# The drains, and the fill whose LFSR CRCs they must reproduce.
DRAIN_OF = {'w1_f1': 'w1_f2', 'w4_f1': 'w1_f2'}


@lru_cache(maxsize=1)
def _regs() -> dict:
    spec = importlib.util.spec_from_file_location('fb_ctl_regs_regmap', _REGMAP)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.top_block


def C(name: str) -> int:
    """Absolute address of an fb_ctl register, by name."""
    return FB_CTL_BASE + int(_regs()[name]['address'], 16)


# WORKLOAD.WR_DST codes (fb_ctl_regs.rdl)
WR_DST_SINK, WR_DST_S0, WR_DST_M2 = 0, 1, 2


def _lsb(field: dict) -> int:
    return int(str(field['offset']).split(':')[-1])


def workload_word(rd_ddr: bool, wr_dst, inj_sync: bool = False) -> int:
    """wr_dst: a WR_DST_* code, or a bool (True = S0) for the chain's steps.
    inj_sync holds W3's injector until STREAM's measurement window opens."""
    f = _regs()['WORKLOAD']
    code = int(wr_dst) if not isinstance(wr_dst, bool) else (WR_DST_S0 if wr_dst else WR_DST_SINK)
    return ((int(rd_ddr) << _lsb(f['RD_SRC'])) | (code << _lsb(f['WR_DST']))
            | (int(inj_sync) << _lsb(f['INJ_SYNC'])))


def region_b_base(cfg) -> int:
    stride = 1 << fb_map.CH_ADDR_LSB
    span = (cfg.num_channels - 1) * stride + cfg.descriptors_per_channel * cfg.transfer_bytes
    return DDR_A_BASE + -(-span // REGION_ALIGN) * REGION_ALIGN


def ddr_span(cfg) -> int:
    """Bytes of S0 the chain touches, from 0 (sizing a sim memory model)."""
    return region_b_base(cfg) + (region_b_base(cfg) - DDR_A_BASE)


def _base(where: str, cfg) -> int:
    return {'lfsr': fb_map.SRC_BASE, 'snk': fb_map.DST_BASE,
            'A': DDR_A_BASE, 'B': region_b_base(cfg)}[where]


def set_workload(bridge, rd_ddr: bool, wr_dst, inj_sync: bool = False) -> None:
    bridge.write(C('WORKLOAD'), workload_word(rd_ddr, wr_dst, inj_sync))


def calib_complete(bridge) -> bool:
    f = _regs()['STATUS']['INIT_CALIB_COMPLETE']
    return bool((bridge.read(C('STATUS')) >> _lsb(f)) & 1)


def wait_calib(bridge, timeout_s: float = 20.0) -> bool:
    """Wait for the S0 controller to finish calibrating. fb_litedram's BIOS
    calibrates the PHY after every configuration, which takes a few seconds,
    so a program started right after `make program` would otherwise find
    STATUS.INIT_CALIB_COMPLETE still 0 and refuse every DDR3 step."""
    import time
    end = time.monotonic() + timeout_s
    while not calib_complete(bridge):
        if time.monotonic() > end:
            return False
        time.sleep(0.25)
    return True


def run_step(runner, bridge, cfg, src: str, dst: str, *, wr_dst=None, pre_kick=None,
             inj_sync: bool = False) -> dict:
    """One step: point the timer and the descriptors at (src, dst) and run.
    A step that touches DDR3 is refused, not run, before the controller has
    calibrated: a transaction to an uncalibrated controller need not complete
    and can leave work the next run inherits.

    wr_dst overrides the timer's write source (a WR_DST_* code; W3's mirror
    uses WR_DST_M2); pre_kick is the runner's hook, after its soft reset and
    before the kick (W3 programs and starts the injector there)."""
    rd_ddr, wr_ddr = src in ('A', 'B'), dst in ('A', 'B')
    if (rd_ddr or wr_ddr) and not calib_complete(bridge):
        return {'error': 'DDR3 not calibrated (fb_ctl STATUS.INIT_CALIB_COMPLETE = 0)',
                's0_rd_beats': None, 's0_wr_beats': None, 'rd_ddr': rd_ddr, 'wr_ddr': wr_ddr}
    set_workload(bridge, rd_ddr, wr_ddr if wr_dst is None else wr_dst, inj_sync)
    runner.builder = fb_map.make_builder(src_base=_base(src, cfg), dst_base=_base(dst, cfg))
    try:
        res = runner.run_config(cfg, pre_kick=pre_kick)
    finally:
        runner.builder = fb_map.make_builder()
    res['s0_rd_beats'] = bridge.read(C('S0_RD_BEATS'))
    res['s0_wr_beats'] = bridge.read(C('S0_WR_BEATS'))
    for k in ('S0_AW_COUNT', 'S0_B_COUNT', 'S0_AR_COUNT'):
        res[k.lower()] = bridge.read(C(k))
    res['rd_ddr'], res['wr_ddr'] = rd_ddr, wr_ddr
    return res


def _channels(cfg) -> list[int]:
    return list(range(cfg.num_channels))


def judge(step: str, res: dict, cfg, fill: dict | None) -> list[str]:
    """Why this step fails ([] = pass). The runner's own CRC verdict is not
    used: it needs both endpoint CRCs, and a DDR3 step drives only one."""
    why = []
    want = cfg.num_channels * cfg.descriptors_per_channel * cfg.transfer_bytes \
        // (fb_map.DATA_WIDTH // 8)
    if res.get('error'):
        why.append(f"run error: {res['error']}")
    if not res.get('bus_cycles_total'):
        why.append("the run timer never stopped")
    for side, crossed in (('rd', res['rd_ddr']), ('wr', res['wr_ddr'])):
        got = res.get(f's0_{side}_beats')
        if got != (want if crossed else 0):
            why.append(f"S0 {side} beats {got}, want {want if crossed else 0}")
    if step in DRAIN_OF:
        if fill is None:
            why.append(f"no {DRAIN_OF[step]} result to check against")
        else:
            src_crc = (fill.get('crc') or {}).get('rd_per_ch') or []
            got_crc = (res.get('crc') or {}).get('wr_per_ch') or []
            for ch in _channels(cfg):
                a = src_crc[ch] if ch < len(src_crc) else None
                b = got_crc[ch] if ch < len(got_crc) else None
                if a is None or b is None or a != b or a == 0:
                    why.append(f"ch{ch}: sink CRC 0x{(b or 0):08X}, "
                               f"{DRAIN_OF[step]} LFSR CRC 0x{(a or 0):08X}")
    return why


def run_chain(runner, bridge, cfg, log=print) -> list[dict]:
    """Every step of CHAIN on one config; each result carries 'step',
    'verdict' and 'why'. The timer is left watching W2's endpoints."""
    out, by_step = [], {}
    if not wait_calib(bridge):
        log("  DDR3 never finished calibrating (fb_ctl STATUS); the steps will be refused")
    try:
        for step, src, dst in CHAIN:
            res = run_step(runner, bridge, cfg, src, dst)
            res['step'] = step
            res['why'] = judge(step, res, cfg, by_step.get(DRAIN_OF.get(step, ''), None))
            res['verdict'] = not res['why']
            by_step[step] = res
            out.append(res)
            log(f"  {step} ({src} -> {dst}): {'PASS' if res['verdict'] else 'FAIL'} "
                f"cycles {res.get('bus_cycles_total')} "
                f"S0 rd/wr {res['s0_rd_beats']}/{res['s0_wr_beats']} "
                f"aw/b/ar {res.get('s0_aw_count')}/{res.get('s0_b_count')}/{res.get('s0_ar_count')}"
                + (f"  {'; '.join(res['why'])}" if res['why'] else ''))
    finally:
        set_workload(bridge, False, False)
    return out

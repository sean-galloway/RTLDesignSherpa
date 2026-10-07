#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Unit tests for mon_configs.py -- pure register-value checks, no hardware.
#
#   source $REPO_ROOT/env_python
#   pytest projects/NexysA7/stream_characterization/flows-stream-bridge/host/test_mon_configs.py -q

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(__file__))

import mon_configs as mc  # noqa: E402


def regs_for(cfg, monitor="daxmon"):
    """Absolute (addr -> value) dict for one monitor's program."""
    base = mc.MON_BASES[monitor]
    want = {base + off for off in
            (mc.OFF_ENABLE, mc.OFF_PKT_MASK, mc.OFF_ERR_CFG,
             mc.OFF_MASK1, mc.OFF_MASK2, mc.OFF_MASK3)}
    return {a: v for a, v in cfg.register_writes() if a in want}


# --------------------------------------------------------------------------
# perf-mon: only PktTypePerf flows
# --------------------------------------------------------------------------

def test_perf_mon_enable_only_mon_and_perf():
    r = regs_for(mc.PERF_MON)
    base = mc.MON_BASES["daxmon"]
    assert r[base + mc.OFF_ENABLE] == (mc.EN_MON | mc.EN_PERF)


def test_perf_mon_pkt_mask_passes_only_perf():
    r = regs_for(mc.PERF_MON)
    base = mc.MON_BASES["daxmon"]
    pkt_mask = r[base + mc.OFF_PKT_MASK]
    # bit clear == that type passes; only PERF should be clear.
    for t in range(16):
        passes = not (pkt_mask >> t) & 1
        assert passes == (t == mc.PKT_PERF), f"type {t} pass={passes}"


def test_perf_mon_perf_event_mask_open_others_masked():
    r = regs_for(mc.PERF_MON)
    base = mc.MON_BASES["daxmon"]
    mask2 = r[base + mc.OFF_MASK2]
    perf_mask = (mask2 >> 8) & 0xFF
    thresh_mask = mask2 & 0xFF
    assert perf_mask == 0x00, "perf event codes must pass"
    assert thresh_mask == 0xFF, "threshold must stay masked"
    # error / timeout cones masked too.
    assert (r[base + mc.OFF_ERR_CFG] >> 8) & 0xFF == 0xFF
    assert r[base + mc.OFF_MASK1] & 0xFF == 0xFF  # timeout


def test_perf_mon_not_compressed():
    assert mc.PERF_MON.compress is False


# --------------------------------------------------------------------------
# debug configs
# --------------------------------------------------------------------------

def test_debug_basic_enables_err_compl_timeout():
    r = regs_for(mc.DEBUG_BASIC)
    base = mc.MON_BASES["daxmon"]
    assert r[base + mc.OFF_ENABLE] == (
        mc.EN_MON | mc.EN_ERR | mc.EN_COMPL | mc.EN_TIMEOUT)
    # err/compl/timeout event masks cleared (pass), perf/thresh masked.
    assert (r[base + mc.OFF_ERR_CFG] >> 8) & 0xFF == 0x00  # err
    assert r[base + mc.OFF_MASK1] == 0x0000                # timeout+compl
    assert r[base + mc.OFF_MASK2] == 0xFFFF                # thresh+perf masked


def test_debug_all_passes_five_types():
    r = regs_for(mc.DEBUG_ALL)
    base = mc.MON_BASES["daxmon"]
    pkt_mask = r[base + mc.OFF_PKT_MASK]
    passing = {t for t in range(16) if not (pkt_mask >> t) & 1}
    assert passing == {mc.PKT_ERROR, mc.PKT_COMPL, mc.PKT_THRESHOLD,
                       mc.PKT_TIMEOUT, mc.PKT_PERF}


def test_debug_configs_marked_compressed():
    for name in ("debug-basic", "debug-compl", "debug-all", "debug-core"):
        assert mc.get(name).compress is True


def test_debug_core_isolates_core_protocol():
    r = dict(mc.DEBUG_CORE.register_writes())
    # AXI (daxmon) + AXIS (rdmon) monitors off, filters drop-all.
    for mon in ("daxmon", "rdmon"):
        base = mc.MON_BASES[mon]
        assert r[base + mc.OFF_ENABLE] == 0, f"{mon} must be off"
        assert r[base + mc.OFF_PKT_MASK] == mc.PKT_MASK_ALL_DROP
    # CORE (wrmon) active, passes error/compl/timeout.
    cbase = mc.MON_BASES["wrmon"]
    assert r[cbase + mc.OFF_ENABLE] == (
        mc.EN_MON | mc.EN_ERR | mc.EN_COMPL | mc.EN_TIMEOUT)
    pkt_mask = r[cbase + mc.OFF_PKT_MASK]
    for t in (mc.PKT_ERROR, mc.PKT_COMPL, mc.PKT_TIMEOUT):
        assert not (pkt_mask >> t) & 1


def test_unknown_protocol_rejected():
    with pytest.raises(ValueError):
        mc.MonConfig("bad", "x", cones=("perf",), protocols=("nope",))


# --------------------------------------------------------------------------
# addr-match field is masked even though no config enables it
# --------------------------------------------------------------------------

def test_addr_mask_always_masked():
    for cfg in mc.CONFIGS.values():
        base = mc.MON_BASES["daxmon"]
        mask3 = dict(cfg.register_writes())[base + mc.OFF_MASK3]
        assert mask3 & 0xFF == 0xFF, f"{cfg.name}: ADDR_MASK must stay masked"


# --------------------------------------------------------------------------
# apply() + all three monitors programmed identically
# --------------------------------------------------------------------------

def test_apply_programs_all_three_monitors():
    writes = []
    mc.PERF_MON.apply(lambda a, v: writes.append((a, v)))
    assert len(writes) == 6 * 3  # 6 regs x 3 monitors
    # Each monitor gets the same ENABLE value.
    enables = {a: v for a, v in writes
               if a in {b + mc.OFF_ENABLE for b in mc.MON_BASES.values()}}
    assert set(enables.values()) == {mc.EN_MON | mc.EN_PERF}


# --------------------------------------------------------------------------
# validation
# --------------------------------------------------------------------------

def test_unknown_cone_rejected():
    with pytest.raises(ValueError):
        mc.MonConfig("bad", "x", cones=("nope",))


def test_arbiter_is_not_a_cone():
    # Scheduler/arbiter activity rides PROTOCOL_CORE error/compl -- it is
    # not a separate cone, so naming it is a config error.
    with pytest.raises(ValueError):
        mc.MonConfig("bad", "x", cones=("arbiter",))


def test_debug_core_filter_passes_scheduler_event_types():
    # The WRMON block is the CORE protocol filter at the top group; CORE
    # carries scheduler + descriptor-engine + write-engine. A debug config
    # that passes error/compl/timeout there captures arbiter/scheduling
    # activity inherently.
    base = mc.MON_BASES["wrmon"]   # CORE filter
    r = dict(mc.DEBUG_BASIC.register_writes())
    pkt_mask = r[base + mc.OFF_PKT_MASK]
    for t in (mc.PKT_ERROR, mc.PKT_COMPL, mc.PKT_TIMEOUT):
        assert not (pkt_mask >> t) & 1, f"CORE filter must pass type {t}"
    # error + timeout + compl event-code masks cleared on the CORE filter.
    assert (r[base + mc.OFF_ERR_CFG] >> 8) & 0xFF == 0x00
    assert r[base + mc.OFF_MASK1] == 0x0000


def test_get_unknown_config_raises():
    with pytest.raises(KeyError):
        mc.get("does-not-exist")

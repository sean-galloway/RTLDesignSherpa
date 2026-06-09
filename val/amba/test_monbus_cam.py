# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_monbus_cam
# Purpose: FUB cocotb tests for rtl/amba/shared/monbus_cam.sv
#
# Documentation: rtl/amba/shared/monbus_cam.sv (header comment)
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-06-06

"""
FUB tests for monbus_cam — the true-LRU caching CAM that backs the
monbus bulk-trace compressor.

The RTL uses position-indexed storage (slot 0 = MRU, slot DEPTH-1 = LRU).
Touch and install both move the matched/new entry to slot 0 and shift
older entries down by one position. This is a bit-exact mirror of the
Python `Cam` class in bin/TBClasses/monbus/monbus_compressor.py, so the
RTL compressor (when it lands) can use the Python Encoder as its
acceptance-test golden.

Test sequence (run in order by monbus_cam_test):
  1.  reset state             — all invalid, count=0, no eviction
  2.  install + lookup        — install one key, lookup hits with correct data
  3.  fill without overflow   — install DEPTH-1 keys, count tracks, all hit
  4.  touch updates payload   — hit, TOUCH with new data, next lookup returns new
  5.  cam_full asserts        — Nth install asserts cam_full one cycle later
  6.  LRU eviction            — install (DEPTH+1)th key, LRU victim removed
  7.  evicted pulse           — pulses high exactly the cycle an install-on-full fires
  8.  miss on absent key      — hit=0, no state change
  9.  random stress           — random install/touch/lookup mix vs. _LruCamModel

Pattern A (val/amba convention): single cocotb test that dispatches the
sub-sequences, parameterized at the pytest level on (KEY_WIDTH,
DATA_WIDTH, DEPTH, REG_LEVEL).
"""

import os
import random
from collections import deque
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ReadOnly, Timer
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd


# ----------------------------------------------------------------------------
# Action encoding (must match monbus_cam.sv)
# ----------------------------------------------------------------------------
ACTION_NONE    = 0b00
ACTION_TOUCH   = 0b01
ACTION_INSTALL = 0b10


# ----------------------------------------------------------------------------
# Inline LRU-eviction golden model — bit-exact mirror of the RTL
#
# The RTL uses position-indexed storage (slot 0 = MRU, slot DEPTH-1 = LRU).
# Touch / install move the matched (or new) entry to slot 0 and shift
# the older entries down by one position. This matches the Python `Cam`
# class in bin/TBClasses/monbus/monbus_compressor.py exactly, so the
# encoder/decoder Python golden can be used as a higher-level reference
# for the integration test in test_monbus_compressor.py.
# ----------------------------------------------------------------------------
@dataclass
class _LruCamEntry:
    key:  int
    data: int


class _LruCamModel:
    """Mirrors the RTL's true-LRU position-indexed storage.

    State: list of entries; index 0 is MRU, index count-1 is LRU,
    indices count..DEPTH-1 are empty. Touch/install move the matched
    or new entry to position 0; older entries shift down by one.
    """

    def __init__(self, depth: int):
        self.depth = depth
        self.entries: List[_LruCamEntry] = []

    # ---- access port ------------------------------------------------------

    def lookup(self, key: int) -> Tuple[bool, int, int]:
        """Returns (hit, idx, old_data) — the combinational outputs of
        the RTL. `idx` is the entry's current position rank (0=MRU)."""
        for i, e in enumerate(self.entries):
            if e.key == key:
                return True, i, e.data
        return False, 0, 0

    @property
    def count(self) -> int:
        return len(self.entries)

    def cam_full(self) -> bool:
        return self.count == self.depth

    def evicted(self, action: int) -> bool:
        """Combinational `evicted` output for the given access_action."""
        return action == ACTION_INSTALL and self.cam_full()

    def commit(self, action: int, key: int, new_data: int):
        """Apply the registered state update on the rising edge."""
        if action == ACTION_TOUCH:
            # Find the matching entry, move to front, update data.
            for i, e in enumerate(self.entries):
                if e.key == key:
                    self.entries.pop(i)
                    self.entries.insert(0, _LruCamEntry(key=key, data=new_data))
                    return
            # Silent no-op if no match (RTL flags an $error).
        elif action == ACTION_INSTALL:
            # Evict LRU if full; insert new entry at front.
            if self.cam_full():
                self.entries.pop()
            self.entries.insert(0, _LruCamEntry(key=key, data=new_data))
        # ACTION_NONE / reserved: no state change


# ----------------------------------------------------------------------------
# Test config
# ----------------------------------------------------------------------------
@dataclass
class MonbusCamConfig:
    key_width:  int = 49
    data_width: int = 64
    depth:      int = 16

    def __post_init__(self):
        assert self.depth >= 2, "DEPTH must be at least 2 for LRU semantics"
        assert self.key_width >= 1
        assert self.data_width >= 1


# ----------------------------------------------------------------------------
# Testbench class
# ----------------------------------------------------------------------------
class MonbusCamTB(TBBase):
    """Lightweight TB — drive the single access port, sample combinational
    outputs, compare against the LRU golden."""

    def __init__(self, dut):
        super().__init__(dut)

        # Pull parametric widths from PARAM_* env (matches cam_tag pattern).
        self.KEY_WIDTH  = int(os.environ.get('PARAM_KEY_WIDTH',  '49'))
        self.DATA_WIDTH = int(os.environ.get('PARAM_DATA_WIDTH', '64'))
        self.DEPTH      = int(os.environ.get('PARAM_DEPTH',      '16'))
        self.SEED       = int(os.environ.get('SEED', '0'))

        random.seed(self.SEED)
        self.cfg   = MonbusCamConfig(self.KEY_WIDTH, self.DATA_WIDTH, self.DEPTH)
        self.model = _LruCamModel(self.DEPTH)

        self._key_mask  = (1 << self.KEY_WIDTH)  - 1
        self._data_mask = (1 << self.DATA_WIDTH) - 1

        self.log.info(
            f"MonbusCamTB: KEY_WIDTH={self.KEY_WIDTH}, "
            f"DATA_WIDTH={self.DATA_WIDTH}, DEPTH={self.DEPTH}, SEED={self.SEED}"
        )

    # ---- driving helpers --------------------------------------------------

    def _drive_idle(self):
        self.dut.access_key.value      = 0
        self.dut.access_action.value   = ACTION_NONE
        self.dut.access_new_data.value = 0

    async def reset_dut(self):
        self.log.debug("reset_dut: starting")
        self._drive_idle()
        self.dut.rst_n.value = 0
        await self.wait_clocks('clk', 5)
        self.dut.rst_n.value = 1
        await self.wait_clocks('clk', 2)
        self.model = _LruCamModel(self.DEPTH)
        self.log.debug("reset_dut: done")

    async def _step(self, key: int, action: int, new_data: int = 0):
        """Drive one access port cycle, sample combinational outputs at
        the end of the cycle, commit the model's registered update to
        mirror the RTL's clock edge."""
        self.dut.access_key.value      = key & self._key_mask
        self.dut.access_action.value   = action
        self.dut.access_new_data.value = new_data & self._data_mask

        # Sample combinational outputs after they settle this cycle.
        await ReadOnly()
        hit       = int(self.dut.access_hit.value)
        idx       = int(self.dut.access_idx.value)
        old_data  = int(self.dut.access_old_data.value)
        cam_full  = int(self.dut.cam_full.value)
        cam_count = int(self.dut.cam_count.value)
        evicted   = int(self.dut.evicted.value)

        # Cross-check combinational state vs. the model. Mask the lookup
        # key to the same KEY_WIDTH the DUT sees — otherwise large literal
        # keys (e.g. 0xCAFE_1234) won't match the masked entries the model
        # stored on install.
        masked_key = key & self._key_mask
        exp_hit, exp_idx, exp_old = self.model.lookup(masked_key)
        assert hit == int(exp_hit), \
            f"access_hit mismatch: rtl={hit}, model={int(exp_hit)}, key=0x{masked_key:x}"
        if exp_hit:
            assert idx == exp_idx, \
                f"access_idx mismatch on hit: rtl={idx}, model={exp_idx}, key=0x{masked_key:x}"
            assert old_data == exp_old, \
                f"access_old_data mismatch: rtl=0x{old_data:x}, model=0x{exp_old:x}, key=0x{masked_key:x}"
        assert cam_full  == int(self.model.cam_full()), \
            f"cam_full mismatch: rtl={cam_full}, model={int(self.model.cam_full())}"
        assert cam_count == self.model.count, \
            f"cam_count mismatch: rtl={cam_count}, model={self.model.count}"
        assert evicted == int(self.model.evicted(action)), \
            f"evicted mismatch: rtl={evicted}, model={int(self.model.evicted(action))}, action={action}"

        # Advance clock edge, then commit the model's registered update.
        await RisingEdge(self.dut.clk)
        self.model.commit(action, key & self._key_mask, new_data & self._data_mask)

        # Park signals back to idle so the next caller can drive fresh.
        self._drive_idle()
        return hit, idx, old_data, cam_full, cam_count, evicted

    # ---- sub-tests --------------------------------------------------------

    async def t1_reset_state(self):
        self.log.info("=== t1: reset state ===")
        # After reset_dut, the model is fresh; any lookup must miss and
        # all status signals must be zero. Drive a few NONE accesses.
        for _ in range(3):
            await self._step(key=0, action=ACTION_NONE)
        # And one with a non-zero key, still miss.
        await self._step(key=0xDEADBEEF, action=ACTION_NONE)
        self.log.info("=== t1: PASS ===")

    async def t2_install_and_lookup_basic(self):
        self.log.info("=== t2: install + lookup basic ===")
        K, D = 0xCAFE_1234, 0xAAAA_BBBB_CCCC_DDDD & self._data_mask
        # Step A: lookup, miss expected.
        hit, *_ = await self._step(key=K, action=ACTION_NONE)
        assert not hit
        # Step B: install K/D.
        await self._step(key=K, action=ACTION_INSTALL, new_data=D)
        # Step C: lookup K, should hit with old_data=D.
        hit, idx, old, *_ = await self._step(key=K, action=ACTION_NONE)
        assert hit and old == D, f"expected hit with data 0x{D:x}, got hit={hit} old=0x{old:x}"
        self.log.info("=== t2: PASS ===")

    async def t3_fill_without_overflow(self):
        self.log.info("=== t3: fill to N-1, all lookup as hit ===")
        keys, datas = [], []
        # Install DEPTH-1 entries (avoids the overflow boundary).
        for i in range(self.DEPTH - 1):
            k = 0x0001_0000 + i
            d = (0xDEAD_0000 + i) & self._data_mask
            keys.append(k); datas.append(d)
            await self._step(key=k, action=ACTION_INSTALL, new_data=d)
        # All N-1 keys must lookup as hit with correct old_data.
        for k, d in zip(keys, datas):
            hit, _, old, _, count, _ = await self._step(key=k, action=ACTION_NONE)
            assert hit and old == d, \
                f"t3: key=0x{k:x} lookup hit={hit} old=0x{old:x} expected=0x{d:x}"
            assert count == self.DEPTH - 1, \
                f"t3: cam_count={count}, expected {self.DEPTH - 1}"
        self.log.info("=== t3: PASS ===")

    async def t4_touch_updates_payload(self):
        self.log.info("=== t4: TOUCH updates payload ===")
        K = 0xC0DE_FACE
        D1 = 0x1111_2222_3333_4444 & self._data_mask
        D2 = 0x5555_6666_7777_8888 & self._data_mask
        await self._step(key=K, action=ACTION_INSTALL, new_data=D1)
        # Hit confirms install.
        hit, _, old, *_ = await self._step(key=K, action=ACTION_NONE)
        assert hit and old == D1
        # TOUCH overwrites data.
        await self._step(key=K, action=ACTION_TOUCH, new_data=D2)
        # Next lookup must see D2.
        hit, _, old, *_ = await self._step(key=K, action=ACTION_NONE)
        assert hit and old == D2, \
            f"t4: after TOUCH expected data=0x{D2:x}, got 0x{old:x}"
        self.log.info("=== t4: PASS ===")

    async def t5_cam_full_asserts(self):
        self.log.info("=== t5: cam_full asserts after Nth install ===")
        for i in range(self.DEPTH):
            k = 0x0002_0000 + i
            d = i & self._data_mask
            _, _, _, full_before, _, _ = await self._step(
                key=k, action=ACTION_INSTALL, new_data=d
            )
            if i < self.DEPTH - 1:
                assert not full_before, f"t5: cam_full asserted early at install {i}"
        # The cycle after the final install, cam_full should be 1.
        # Use _step (which samples at ReadOnly) rather than poking the DUT
        # signal directly — direct samples after RisingEdge are stale.
        _, _, _, full_post, _, _ = await self._step(key=0, action=ACTION_NONE)
        assert full_post == 1, "t5: cam_full not asserted after DEPTH installs"
        self.log.info("=== t5: PASS ===")

    async def t6_lru_eviction(self):
        self.log.info("=== t6: LRU eviction ===")
        # Install DEPTH unique keys back-to-back, no intervening touches.
        # Under LRU, the first-installed key is also the least-recently-
        # used at the end of the sequence (slot 0 = MRU = last-installed,
        # slot DEPTH-1 = LRU = first-installed). So the (DEPTH+1)th
        # install evicts installed_keys[0] -- the same outcome FIFO
        # would produce, since there have been no access reorderings.
        installed_keys = []
        for i in range(self.DEPTH):
            k = 0x0003_0000 + i
            d = (0xBEEF_0000 + i) & self._data_mask
            installed_keys.append((k, d))
            await self._step(key=k, action=ACTION_INSTALL, new_data=d)
        # Install one more key -> LRU victim (installed_keys[0]) evicted.
        # evicted pulse must fire.
        new_k, new_d = 0xFEED_F00D, 0xDEAD_DEAD_DEAD_DEAD & self._data_mask
        _, _, _, full, _, evicted = await self._step(
            key=new_k, action=ACTION_INSTALL, new_data=new_d
        )
        assert full,    "t6: cam_full not asserted before eviction install"
        assert evicted, "t6: evicted pulse did NOT fire on full-CAM install"
        # The LRU (first-installed) key is no longer present.
        hit, *_ = await self._step(key=installed_keys[0][0], action=ACTION_NONE)
        assert not hit, "t6: LRU key still present after eviction"
        # The new key IS present with correct data.
        hit, _, old, *_ = await self._step(key=new_k, action=ACTION_NONE)
        assert hit and old == new_d, \
            f"t6: new key not found / wrong data: hit={hit} old=0x{old:x}"
        # The OTHER (non-evicted) entries are still present.
        for k, d in installed_keys[1:]:
            hit, _, old, *_ = await self._step(key=k, action=ACTION_NONE)
            assert hit and old == d, \
                f"t6: key 0x{k:x} unexpectedly missing or has wrong data"
        self.log.info("=== t6: PASS ===")

    async def t7_evicted_pulse_only_on_full_install(self):
        self.log.info("=== t7: evicted pulse semantics ===")
        # _step's internal cross-check already validates `evicted` vs the
        # model on every cycle — so we just need to drive the sequence
        # that exercises each case and let the cross-checks catch any
        # mismatch. The explicit asserts below confirm the headline
        # outcomes via _step's return tuple (no direct DUT pokes — those
        # see stale values after RisingEdge).

        # Empty install: model says evicted=0 (cam not full).
        await self._step(key=0xAAAA, action=ACTION_INSTALL, new_data=0x1)
        # Touch: model says evicted=0 (action != INSTALL).
        await self._step(key=0xAAAA, action=ACTION_TOUCH, new_data=0x2)
        # NONE: model says evicted=0.
        await self._step(key=0xAAAA, action=ACTION_NONE)
        # Fill the CAM (DEPTH-1 more installs).
        for i in range(self.DEPTH - 1):
            await self._step(
                key=0x4000 + i, action=ACTION_INSTALL, new_data=i & self._data_mask
            )
        # CAM is now full — lookup-only should NOT pulse evicted.
        _, _, _, full_post, _, evicted_lookup = await self._step(
            key=0xAAAA, action=ACTION_NONE
        )
        assert full_post == 1, "t7: cam_full not asserted after DEPTH installs"
        assert evicted_lookup == 0, "t7: evicted pulsed on full-CAM lookup"
        # Install-on-full DOES pulse evicted.
        _, _, _, _, _, evicted_install = await self._step(
            key=0xBBBB, action=ACTION_INSTALL, new_data=0xFFFF & self._data_mask
        )
        assert evicted_install == 1, "t7: install-on-full did NOT pulse evicted"
        self.log.info("=== t7: PASS ===")

    async def t8_miss_on_absent_key(self):
        self.log.info("=== t8: miss on absent key, no state change ===")
        # Install one key, then look up something else — expect miss + count unchanged.
        await self._step(key=0x1234, action=ACTION_INSTALL, new_data=0xAB)
        count_before = self.model.count
        hit, _, _, _, count_after, evicted = await self._step(
            key=0x9999, action=ACTION_NONE
        )
        assert not hit, "t8: false hit on absent key"
        assert count_after == count_before, "t8: count changed on lookup-only NONE access"
        assert not evicted
        self.log.info("=== t8: PASS ===")

    async def t9_touch_moves_to_mru(self):
        """LRU-specific: TOUCH on a non-MRU entry must move it to slot 0,
        shifting newer entries down. Verifies the position-rank update
        and the bit-exact behavior against the Python golden's
        move-to-front semantics."""
        self.log.info("=== t9: TOUCH moves entry to MRU ===")
        # Fill the CAM with N unique keys. After installing in order,
        # position 0 = last-installed (MRU), position N-1 = first-installed (LRU).
        keys = [0x0008_0000 + i for i in range(self.DEPTH)]
        datas = [(0xCAFE_0000 + i) & self._data_mask for i in range(self.DEPTH)]
        for k, d in zip(keys, datas):
            await self._step(key=k, action=ACTION_INSTALL, new_data=d)
        # The LRU entry (keys[0]) is at position DEPTH-1.
        hit, idx, _, _, _, _ = await self._step(key=keys[0], action=ACTION_NONE)
        assert hit and idx == self.DEPTH - 1, \
            f"t9: pre-touch LRU lookup expected idx={self.DEPTH-1}, got {idx}"
        # TOUCH it. After commit it must be at position 0 (MRU).
        new_d = 0x5A5A_5A5A_5A5A_5A5A & self._data_mask
        await self._step(key=keys[0], action=ACTION_TOUCH, new_data=new_d)
        # Now lookup it again: should be at idx 0 with new data.
        hit, idx, old, _, _, _ = await self._step(key=keys[0], action=ACTION_NONE)
        assert hit and idx == 0, f"t9: post-touch idx expected 0, got {idx}"
        assert old == new_d, \
            f"t9: post-touch data expected 0x{new_d:x}, got 0x{old:x}"
        # The previously-MRU entry (keys[-1]) has shifted to position 1.
        hit, idx, _, _, _, _ = await self._step(key=keys[-1], action=ACTION_NONE)
        assert hit and idx == 1, \
            f"t9: previously-MRU key now expected idx=1, got {idx}"
        self.log.info("=== t9: PASS ===")

    async def t10_random_stress(self, n_ops: int = 500):
        self.log.info(f"=== t9: random stress, {n_ops} ops ===")
        # Respects the caller protocol: only INSTALL on miss, only TOUCH
        # on hit. Otherwise the RTL's $error assertions for duplicate
        # entries / touch-without-hit would fire (legitimately).
        # _step's internal cross-check validates every cycle's outputs.
        key_space = list(range(0x10000, 0x10000 + (self.DEPTH * 4)))

        for op in range(n_ops):
            # Pick a candidate key, do a lookup-only first to see hit/miss.
            k = random.choice(key_space)
            hit, *_ = await self._step(key=k, action=ACTION_NONE)

            r = random.random()
            if hit:
                # On hit: ~60% TOUCH (refresh data), ~40% NONE again.
                if r < 0.6:
                    d = random.randrange(0, 1 << min(32, self.DATA_WIDTH)) & self._data_mask
                    await self._step(key=k, action=ACTION_TOUCH, new_data=d)
            else:
                # On miss: ~70% INSTALL (cache the key), ~30% NONE.
                if r < 0.7:
                    d = random.randrange(0, 1 << min(32, self.DATA_WIDTH)) & self._data_mask
                    await self._step(key=k, action=ACTION_INSTALL, new_data=d)
        self.log.info(f"=== t9: PASS ({n_ops} ops, all model-checked) ===")


# ----------------------------------------------------------------------------
# Cocotb test entry
# ----------------------------------------------------------------------------
@cocotb.test(timeout_time=10, timeout_unit="ms")
async def monbus_cam_test(dut):
    """Full FUB regression for monbus_cam."""
    tb = MonbusCamTB(dut)
    await tb.start_clock('clk', 10, 'ns')
    await tb.reset_dut()

    # REG_LEVEL gates the heavier stress test.
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    n_stress_ops = {'GATE': 100, 'FUNC': 500, 'FULL': 5000}.get(reg_level, 500)

    await tb.t1_reset_state()
    await tb.reset_dut()

    await tb.t2_install_and_lookup_basic()
    await tb.reset_dut()

    await tb.t3_fill_without_overflow()
    await tb.reset_dut()

    await tb.t4_touch_updates_payload()
    await tb.reset_dut()

    await tb.t5_cam_full_asserts()
    await tb.reset_dut()

    await tb.t6_lru_eviction()
    await tb.reset_dut()

    await tb.t7_evicted_pulse_only_on_full_install()
    await tb.reset_dut()

    await tb.t8_miss_on_absent_key()
    await tb.reset_dut()

    await tb.t9_touch_moves_to_mru()
    await tb.reset_dut()

    await tb.t10_random_stress(n_ops=n_stress_ops)

    tb.log.info("=== ALL TESTS PASSED ===")


# ----------------------------------------------------------------------------
# Pytest parametric wrapper
# ----------------------------------------------------------------------------
def get_monbus_cam_params():
    """REG_LEVEL gates the parameter sweep depth.

    Default (49b key, 64b data, depth 32) matches the locked spec in
    bin/TBClasses/monbus/monbus_compressor.py and the compression
    dataset README. Smaller depths exercise the LRU shift logic at the
    boundary and confirm the parametric sweep works.
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [(49, 64, 32)]  # locked default
    elif reg_level == 'FUNC':
        return [(49, 64, 32), (49, 64, 8)]  # locked + small
    else:  # FULL
        return [
            (49, 64, 32),   # locked default
            (49, 64, 16),
            (49, 64, 8),
            (32, 32, 8),
            (16, 16, 4),
            (64, 64, 16),
        ]


@pytest.mark.parametrize("key_width, data_width, depth", get_monbus_cam_params())
def test_monbus_cam(request, key_width, data_width, depth):
    """Pytest wrapper — runs the cocotb test under a single parameter combo."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_shared':   'rtl/amba/shared',
        'rtl_includes': 'rtl/amba/includes',
    })

    dut_name = "monbus_cam"
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    kw_str = TBBase.format_dec(key_width,  2)
    dw_str = TBBase.format_dec(data_width, 2)
    de_str = TBBase.format_dec(depth,      3)
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name = f"test_{worker_id}_{dut_name}_kw{kw_str}_dw{dw_str}_d{de_str}_{reg_level}"
    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources = [
        os.path.join(rtl_dict['rtl_shared'], "monbus_cam.sv"),
    ]
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    rtl_parameters = {
        'KEY_WIDTH':  str(key_width),
        'DATA_WIDTH': str(data_width),
        'DEPTH':      str(depth),
    }

    extra_env = {
        'DUT':                dut_name,
        'LOG_PATH':           log_path,
        'COCOTB_LOG_LEVEL':   'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED':               os.environ.get('SEED', str(random.randint(0, 100000))),
        'PARAM_KEY_WIDTH':    str(key_width),
        'PARAM_DATA_WIDTH':   str(data_width),
        'PARAM_DEPTH':        str(depth),
    }

    compile_args = [
        '+define+SIMULATION',
        '--trace-fst', '--trace-structs',
        '-Wno-DECLFILENAME', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC',
        '-Wno-UNUSEDPARAM', '-Wno-TIMESCALEMOD',
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_includes'], rtl_dict['rtl_shared'], sim_build],
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
        )
    except Exception as e:
        print(f"Test failed: {e}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise

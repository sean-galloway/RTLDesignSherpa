# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: axi4_master_wr_pattern_gen_tb
# Purpose: Direct FUB TB for axi4_master_wr_pattern_gen. Drives the cfg
#          interface and acts as a minimal AXI4 slave on the M side so
#          the FSM exercises end-to-end (cfg_start -> AW/W/B -> cfg_done).

"""TB for `axi4_master_wr_pattern_gen`.

Stubs the M-side AXI by:
  * always asserting `m_axi_awready` / `m_axi_wready` (full back-to-back),
  * capturing every accepted (awaddr, awid, awlen) into `aw_log`,
  * capturing every accepted (wdata, wlast) into `w_log`,
  * driving B responses for each completed burst with the configured
    `bresp` (default OKAY); test can flip `bresp_override` to fire
    sticky-error scenarios.

A Python LFSR mirror in `expected_data_words()` regenerates the same
32-bit LFSR stream the DUT emits, so the test can compare per-beat data.
"""

from __future__ import annotations

import logging
import os
from dataclasses import dataclass
from typing import Deque, List, Optional
from collections import deque

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase


_NBA_SETTLE_PS = 100


@dataclass
class CapturedAw:
    addr: int
    axid: int
    awlen: int  # len-1 per AXI4


@dataclass
class CapturedW:
    data: int
    last: int


class WrPatternGenTB(TBBase):
    CLK = 10

    LFSR_DEFAULT_SEED = 0xDEADBEEF
    # Matches LFSR_TAPS = {12'd32, 12'd22, 12'd2, 12'd1} (Fibonacci taps)
    LFSR_TAPS = (32, 22, 2, 1)

    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.dut = dut
        self.log = logging.getLogger("wr_pattern_gen_tb")
        self.log.setLevel(logging.INFO)

        self.AXI_DATA_WIDTH = self.convert_to_int(
            os.environ.get("AXI_DATA_WIDTH", "64"))
        self.AXI_ID_WIDTH = self.convert_to_int(
            os.environ.get("AXI_ID_WIDTH", "8"))
        self.LFSR_WIDTH = 32
        self.MASK_LFSR = (1 << self.LFSR_WIDTH) - 1
        self.MASK_DATA = (1 << self.AXI_DATA_WIDTH) - 1

        self.aw_log: List[CapturedAw] = []
        self.w_log:  List[CapturedW] = []
        self.b_outstanding: Deque[int] = deque()  # ids awaiting B
        self.bresp_override: int = 0  # 0 = OKAY; override per-test

    # ---- setup ----

    async def setup_clocks_and_reset(self):
        cocotb.start_soon(Clock(self.dut.aclk, self.CLK, units="ns").start())
        self._drive_idle()
        self.dut.aresetn.value = 0
        for _ in range(10):
            await RisingEdge(self.dut.aclk)
        self.dut.aresetn.value = 1
        for _ in range(5):
            await RisingEdge(self.dut.aclk)
        cocotb.start_soon(self._aw_capture())
        cocotb.start_soon(self._w_capture())
        cocotb.start_soon(self._b_responder())

    def _drive_idle(self) -> None:
        # cfg
        self.dut.cfg_start_addr.value       = 0
        self.dut.cfg_addr_stride_0.value    = 0
        self.dut.cfg_addr_stride_1.value    = 0
        self.dut.cfg_addr_wrap_mask_0.value = 0
        self.dut.cfg_addr_wrap_mask_1.value = 0
        self.dut.cfg_burst_len.value        = 1
        self.dut.cfg_txn_count.value        = 0
        self.dut.cfg_axi_id.value           = 0
        self.dut.cfg_axi_size.value         = 3
        self.dut.cfg_axi_burst.value        = 1  # INCR
        self.dut.cfg_lfsr_seed.value        = 0
        self.dut.cfg_data_mode.value        = 0
        self.dut.cfg_hash_seed0.value       = 0
        self.dut.cfg_hash_seed1.value       = 0
        self.dut.cfg_hash_seed2.value       = 0
        self.dut.cfg_wr_gap.value           = 0
        self.dut.cfg_start.value            = 0
        # M-side AXI (we're the slave for the master block under test)
        self.dut.m_axi_awready.value        = 1
        self.dut.m_axi_wready.value         = 1
        self.dut.m_axi_bid.value            = 0
        self.dut.m_axi_bresp.value          = 0
        self.dut.m_axi_buser.value          = 0
        self.dut.m_axi_bvalid.value         = 0

    # ---- background slave-side responders ----

    async def _aw_capture(self) -> None:
        while True:
            await RisingEdge(self.dut.aclk)
            try:
                v = int(self.dut.m_axi_awvalid.value)
                r = int(self.dut.m_axi_awready.value)
            except Exception:
                return
            if v and r:
                aw = CapturedAw(
                    addr  = int(self.dut.m_axi_awaddr.value),
                    axid  = int(self.dut.m_axi_awid.value),
                    awlen = int(self.dut.m_axi_awlen.value),
                )
                self.aw_log.append(aw)
                self.b_outstanding.append(aw.axid)

    async def _w_capture(self) -> None:
        while True:
            await RisingEdge(self.dut.aclk)
            try:
                v = int(self.dut.m_axi_wvalid.value)
                r = int(self.dut.m_axi_wready.value)
            except Exception:
                return
            if v and r:
                self.w_log.append(CapturedW(
                    data = int(self.dut.m_axi_wdata.value),
                    last = int(self.dut.m_axi_wlast.value),
                ))

    async def _b_responder(self) -> None:
        """Drive one B response per outstanding burst, FIFO-ordered."""
        while True:
            await RisingEdge(self.dut.aclk)
            try:
                if self.dut.m_axi_bvalid.value.is_resolvable:
                    cur_v = int(self.dut.m_axi_bvalid.value)
                else:
                    cur_v = 0
                cur_ready = int(self.dut.m_axi_bready.value)
            except Exception:
                return
            # Drop after handshake
            if cur_v and cur_ready:
                self.dut.m_axi_bvalid.value = 0
            # Issue next B if any pending and bus idle
            if not int(self.dut.m_axi_bvalid.value) and self.b_outstanding \
               and self._last_w_was_last():
                bid = self.b_outstanding.popleft()
                self.dut.m_axi_bvalid.value = 1
                self.dut.m_axi_bid.value    = bid
                self.dut.m_axi_bresp.value  = self.bresp_override

    def _last_w_was_last(self) -> bool:
        """B can fire only after we've seen wlast for the outstanding burst."""
        # Count `last` strobes in w_log vs B already drained
        bs_done = len([w for w in self.w_log if w.last == 1])
        bs_drained = len(self.aw_log) - len(self.b_outstanding)
        return bs_done > bs_drained

    # ---- cfg drive helpers ----

    async def program(self, *, start_addr: int, stride_0: int = 0,
                      stride_1: int = 0, wrap_mask_0: int = 0,
                      wrap_mask_1: int = 0, burst_len: int = 1,
                      txn_count: int = 1, axi_id: int = 0,
                      axi_size: int = 3, axi_burst: int = 1,
                      lfsr_seed: int = 0, wr_gap: int = 0,
                      data_mode: int = 0,
                      hash_seed0: int = 0,
                      hash_seed1: int = 0,
                      hash_seed2: int = 0) -> None:
        self.dut.cfg_start_addr.value       = start_addr
        self.dut.cfg_addr_stride_0.value    = stride_0
        self.dut.cfg_addr_stride_1.value    = stride_1
        self.dut.cfg_addr_wrap_mask_0.value = wrap_mask_0
        self.dut.cfg_addr_wrap_mask_1.value = wrap_mask_1
        self.dut.cfg_burst_len.value        = burst_len
        self.dut.cfg_txn_count.value        = txn_count
        self.dut.cfg_axi_id.value           = axi_id
        self.dut.cfg_axi_size.value         = axi_size
        self.dut.cfg_axi_burst.value        = axi_burst
        self.dut.cfg_lfsr_seed.value        = lfsr_seed
        self.dut.cfg_data_mode.value        = data_mode & 0x1
        self.dut.cfg_hash_seed0.value       = hash_seed0 & 0xFFFFFFFF
        self.dut.cfg_hash_seed1.value       = hash_seed1 & 0xFFFFFFFF
        self.dut.cfg_hash_seed2.value       = hash_seed2 & 0xFFFFFFFF
        self.dut.cfg_wr_gap.value           = wr_gap & 0xF
        await RisingEdge(self.dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")

    async def pulse_start(self) -> None:
        self.dut.cfg_start.value = 1
        await RisingEdge(self.dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")
        self.dut.cfg_start.value = 0
        await RisingEdge(self.dut.aclk)

    async def wait_done(self, timeout_cycles: int = 5000) -> None:
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.aclk)
            await Timer(_NBA_SETTLE_PS, units="ps")
            if int(self.dut.cfg_done.value):
                return
        raise TimeoutError(
            f"cfg_done did not assert within {timeout_cycles} cycles"
        )

    # ---- Python LFSR mirror ----

    def expected_lfsr_words(self, count: int,
                            seed: Optional[int] = None) -> List[int]:
        """Regenerate the Fibonacci LFSR sequence the DUT emits. The
        `shifter_lfsr_fibonacci` shifts **right** with feedback to the
        MSB:
          feedback = XOR of bits at (tap_position - 1) for each tap
          next     = (feedback << N-1) | (v >> 1)
        Tap positions are 1-indexed (32 → bit 31, 22 → bit 21, etc).
        Beat k uses lfsr_out after k advances (k=0 is the seed)."""
        seed = seed if seed not in (None, 0) else self.LFSR_DEFAULT_SEED
        seed &= self.MASK_LFSR
        N = self.LFSR_WIDTH
        tap_bits = [t - 1 for t in self.LFSR_TAPS]
        out: List[int] = []
        v = seed
        for _ in range(count):
            out.append(v)
            feedback = 0
            for b in tap_bits:
                feedback ^= (v >> b) & 1
            v = ((feedback << (N - 1)) | (v >> 1)) & self.MASK_LFSR
        return out

    def expected_data_words(self, count: int,
                            seed: Optional[int] = None) -> List[int]:
        """Replicate the 32-bit LFSR across AXI_DATA_WIDTH bits per beat,
        same way the DUT does."""
        lfsr_words = self.expected_lfsr_words(count, seed)
        rep = (self.AXI_DATA_WIDTH + 31) // 32
        out = []
        for w in lfsr_words:
            full = 0
            for k in range(rep):
                full |= (w & 0xFFFFFFFF) << (k * 32)
            out.append(full & self.MASK_DATA)
        return out

    # ---- Python hash mirror (must match the RTL addr_hash32 bit-for-bit) ----

    @staticmethod
    def addr_hash32(addr: int, s0: int, s1: int, s2: int) -> int:
        """Murmur3 fmix32 with constants replaced by cfg seeds. The DUT
        function does the same xor-shift / odd-mul sequence at 32-bit
        truncated arithmetic."""
        mask = 0xFFFFFFFF
        x = (addr ^ s0) & mask
        x = (x ^ (x >> 16)) & mask
        x = (x * ((s1 | 1) & mask)) & mask
        x = (x ^ (x >> 13)) & mask
        x = (x * ((s2 | 1) & mask)) & mask
        x = (x ^ (x >> 16)) & mask
        return x

    def expected_hash_beat_data(self, byte_addr: int,
                                seeds: tuple) -> int:
        """One beat's expected data = REPLICATION_FACTOR slices, each
        slice s = addr_hash32(byte_addr + s*4, seeds). Looks up
        addr_hash32 by class so this method can be borrowed by sibling
        TB classes that share the LFSR/hash mirrors."""
        s0, s1, s2 = seeds
        rep = (self.AXI_DATA_WIDTH + 31) // 32
        full = 0
        for s in range(rep):
            slice_addr = (byte_addr + s * 4) & 0xFFFFFFFF
            slice_word = WrPatternGenTB.addr_hash32(slice_addr, s0, s1, s2)
            full |= slice_word << (s * 32)
        return full & self.MASK_DATA

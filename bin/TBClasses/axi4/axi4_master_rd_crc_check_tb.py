# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: axi4_master_rd_crc_check_tb
# Purpose: Direct FUB TB for axi4_master_rd_crc_check. Drives the cfg
#          interface and acts as a minimal AXI4 read slave on the M side.

"""TB for `axi4_master_rd_crc_check`.

Stubs the M-side AXI by:
  * always asserting `m_axi_arready`,
  * capturing every accepted (araddr, arid, arlen) into `ar_log`,
  * driving R beats per accepted AR: the data fed back is either the
    locally-regenerated LFSR pattern (the "match" path that lets the
    DUT's CRC accumulator + per-beat compare see clean data) or
    constant garbage (the "mismatch" path that exercises o_data_error
    + o_beats_mismatched). RRESP can also be overridden via
    `rresp_override`.
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
from TBClasses.axi4.axi4_master_wr_pattern_gen_tb import (
    WrPatternGenTB as _LfsrMirror,
)


_NBA_SETTLE_PS = 100


@dataclass
class CapturedAr:
    addr: int
    axid: int
    arlen: int  # len-1 per AXI4


class RdCrcCheckTB(TBBase):
    CLK = 10
    LFSR_DEFAULT_SEED = _LfsrMirror.LFSR_DEFAULT_SEED
    LFSR_TAPS         = _LfsrMirror.LFSR_TAPS

    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.dut = dut
        self.log = logging.getLogger("rd_crc_check_tb")
        self.log.setLevel(logging.INFO)

        self.AXI_DATA_WIDTH = self.convert_to_int(
            os.environ.get("AXI_DATA_WIDTH", "64"))
        self.AXI_ID_WIDTH = self.convert_to_int(
            os.environ.get("AXI_ID_WIDTH", "8"))
        self.LFSR_WIDTH = 32
        self.MASK_LFSR = (1 << self.LFSR_WIDTH) - 1
        self.MASK_DATA = (1 << self.AXI_DATA_WIDTH) - 1

        # Slave-side responder behavior knobs (test overrides per scenario)
        self.return_lfsr_data: bool = True   # True: feed LFSR data; False: garbage
        self.garbage_word: int = 0xBADCAFE_DEADBEEF
        self.rresp_override: int = 0         # 0=OKAY
        self.lfsr_seed: int = self.LFSR_DEFAULT_SEED

        self.ar_log: List[CapturedAr] = []
        # Slave-side LFSR state for "match" path. Reseeded on cfg_start.
        self._slave_lfsr_state: int = self.LFSR_DEFAULT_SEED

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
        cocotb.start_soon(self._ar_capture_and_respond())

    def _drive_idle(self) -> None:
        self.dut.cfg_start_addr.value       = 0
        self.dut.cfg_addr_stride_0.value    = 0
        self.dut.cfg_addr_stride_1.value    = 0
        self.dut.cfg_addr_wrap_mask_0.value = 0
        self.dut.cfg_addr_wrap_mask_1.value = 0
        self.dut.cfg_burst_len.value        = 1
        self.dut.cfg_txn_count.value        = 0
        self.dut.cfg_axi_id.value           = 0
        self.dut.cfg_axi_size.value         = 3
        self.dut.cfg_axi_burst.value        = 1
        self.dut.cfg_lfsr_seed.value        = 0
        self.dut.cfg_start.value            = 0
        self.dut.m_axi_arready.value        = 1
        self.dut.m_axi_rid.value            = 0
        self.dut.m_axi_rdata.value          = 0
        self.dut.m_axi_rresp.value          = 0
        self.dut.m_axi_ruser.value          = 0
        self.dut.m_axi_rlast.value          = 0
        self.dut.m_axi_rvalid.value         = 0

    # ---- background responder ----

    def _advance_lfsr(self) -> int:
        v = self._slave_lfsr_state
        N = self.LFSR_WIDTH
        feedback = 0
        for t in self.LFSR_TAPS:
            feedback ^= (v >> (t - 1)) & 1
        self._slave_lfsr_state = (
            ((feedback << (N - 1)) | (v >> 1)) & self.MASK_LFSR
        )
        return v   # returns the CURRENT word, then advances state

    def _replicate(self, lfsr_word: int) -> int:
        rep = (self.AXI_DATA_WIDTH + 31) // 32
        out = 0
        w = lfsr_word & 0xFFFFFFFF
        for k in range(rep):
            out |= w << (k * 32)
        return out & self.MASK_DATA

    async def _ar_capture_and_respond(self) -> None:
        """Capture each AR and immediately stream (arlen+1) R beats."""
        while True:
            await RisingEdge(self.dut.aclk)
            try:
                v = int(self.dut.m_axi_arvalid.value)
                r = int(self.dut.m_axi_arready.value)
            except Exception:
                return
            if v and r:
                ar = CapturedAr(
                    addr  = int(self.dut.m_axi_araddr.value),
                    axid  = int(self.dut.m_axi_arid.value),
                    arlen = int(self.dut.m_axi_arlen.value),
                )
                self.ar_log.append(ar)
                cocotb.start_soon(self._drive_r_burst(ar))

    async def _drive_r_burst(self, ar: CapturedAr) -> None:
        beats = ar.arlen + 1
        for k in range(beats):
            if self.return_lfsr_data:
                lfsr_word = self._advance_lfsr()
                data = self._replicate(lfsr_word)
            else:
                data = self.garbage_word & self.MASK_DATA
            is_last = (k == beats - 1)
            self.dut.m_axi_rvalid.value = 1
            self.dut.m_axi_rid.value    = ar.axid
            self.dut.m_axi_rdata.value  = data
            self.dut.m_axi_rresp.value  = self.rresp_override
            self.dut.m_axi_rlast.value  = 1 if is_last else 0
            # Wait for handshake
            while True:
                await RisingEdge(self.dut.aclk)
                await Timer(_NBA_SETTLE_PS, units="ps")
                if int(self.dut.m_axi_rready.value):
                    break
            self.dut.m_axi_rvalid.value = 0
            self.dut.m_axi_rlast.value  = 0

    # ---- cfg drive helpers ----

    async def program(self, *, start_addr: int, stride_0: int = 0,
                      stride_1: int = 0, wrap_mask_0: int = 0,
                      wrap_mask_1: int = 0, burst_len: int = 1,
                      txn_count: int = 1, axi_id: int = 0,
                      axi_size: int = 3, axi_burst: int = 1,
                      lfsr_seed: int = 0) -> None:
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
        # Mirror the DUT's seed selection so the slave-side LFSR stays
        # phase-locked when return_lfsr_data is on.
        self.lfsr_seed = (lfsr_seed if lfsr_seed != 0
                          else self.LFSR_DEFAULT_SEED)
        self._slave_lfsr_state = self.lfsr_seed
        await RisingEdge(self.dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")

    async def pulse_start(self) -> None:
        self.dut.cfg_start.value = 1
        await RisingEdge(self.dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")
        self.dut.cfg_start.value = 0
        # Reset the slave LFSR mirror to the seed *now* so its first
        # advance matches the DUT's first advance (DUT loads seed at
        # cfg_start, advances on each R beat).
        self._slave_lfsr_state = self.lfsr_seed
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

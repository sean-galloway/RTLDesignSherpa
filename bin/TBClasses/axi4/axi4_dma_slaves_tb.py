# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: axi4_dma_slaves_tb
# Purpose: Direct FUB TB for axi4_dma_slaves -- the bundle wrapper that
#          combines axi4_slave_rd_pattern_gen (AR/R) and
#          axi4_slave_wr_crc_check (AW/W/B) behind one aclk/aresetn.

"""TB for `axi4_dma_slaves`.

Drives BOTH sides of the one DUT with framework AXI4 master BFMs on the
shared ``s_axi_*`` prefix: ``AXI4MasterRead`` for AR/R (against the
read-side LFSR pattern generator) and ``AXI4MasterWrite`` for AW/W/B
(against the write-side CRC accumulator). The two BFMs bind to disjoint
signal sets (ar/r vs aw/w/b) so they coexist on one DUT without
conflict.

Integration contract under test (from the module header comment): "the
master writes back the same LFSR data it read, so both sides compute
against the same CRC" -- read the pattern generator's stream, write it
straight back to the CRC checker, and the two sides' per-channel CRCs
must match. A corrupted echo (one beat flipped before write-back) must
make them diverge -- that's the end-to-end integrity check this module
exists to support; axi4_slave_wr_crc_check has no error output of its
own (see that TB's docstring).
"""

from __future__ import annotations

import logging
import os
from typing import List, Optional

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase

from CocoTBFramework.components.axi4.axi4_interfaces import (
    AXI4MasterRead, AXI4MasterWrite,
)

from TBClasses.axi4.axi4_slave_rd_pattern_gen_tb import SlaveRdPatternGenTB
from TBClasses.axi4.axi4_slave_wr_crc_check_tb import SlaveWrCrcCheckTB


_NBA_SETTLE_PS = 100


class DmaSlavesTB(TBBase):
    CLK = 10

    LFSR_DEFAULT_SEED = SlaveRdPatternGenTB.LFSR_DEFAULT_SEED
    LFSR_TAPS = SlaveRdPatternGenTB.LFSR_TAPS
    LFSR_WIDTH = 32

    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.dut = dut
        self.log = logging.getLogger("dma_slaves_tb")
        self.log.setLevel(logging.INFO)

        self.AXI_DATA_WIDTH = self.convert_to_int(
            os.environ.get("AXI_DATA_WIDTH", "64"))
        self.AXI_ID_WIDTH = self.convert_to_int(
            os.environ.get("AXI_ID_WIDTH", "8"))
        self.NUM_CHANNELS = self.convert_to_int(
            os.environ.get("NUM_CHANNELS", "1"))

        self.MASK_DATA = (1 << self.AXI_DATA_WIDTH) - 1
        self.BYTES_PER_BEAT = self.AXI_DATA_WIDTH // 8
        self._size = (self.BYTES_PER_BEAT).bit_length() - 1

        self.rd_master: Optional[AXI4MasterRead] = None
        self.wr_master: Optional[AXI4MasterWrite] = None

    # ---- three-method contract (GLOBAL_REQUIREMENTS 2.2) ----

    async def setup_clocks_and_reset(self):
        cocotb.start_soon(Clock(self.dut.aclk, self.CLK, units="ns").start())
        self._drive_idle()
        await self.assert_reset()
        for _ in range(10):
            await RisingEdge(self.dut.aclk)
        await self.deassert_reset()
        for _ in range(5):
            await RisingEdge(self.dut.aclk)

        self.rd_master = AXI4MasterRead(
            dut=self.dut, clock=self.dut.aclk, prefix="s_axi_",
            log=self.log, data_width=self.AXI_DATA_WIDTH,
            id_width=self.AXI_ID_WIDTH, addr_width=32, user_width=1,
            multi_sig=True, timeout_cycles=20_000,
        )
        self.wr_master = AXI4MasterWrite(
            dut=self.dut, clock=self.dut.aclk, prefix="s_axi_",
            log=self.log, data_width=self.AXI_DATA_WIDTH,
            id_width=self.AXI_ID_WIDTH, addr_width=32, user_width=1,
            multi_sig=True, timeout_cycles=20_000,
        )
        await self.reset_both()

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self) -> None:
        self.dut.aresetn.value = 0
        self.dut.read_lfsr_reset.value = 0
        self.dut.write_crc_reset.value = 0

    async def reset_both(self) -> None:
        self.dut.read_lfsr_reset.value = 1
        self.dut.write_crc_reset.value = 1
        await RisingEdge(self.dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")
        self.dut.read_lfsr_reset.value = 0
        self.dut.write_crc_reset.value = 0
        await RisingEdge(self.dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")

    async def settle(self, cycles: int = 4) -> None:
        """Wait a few clocks after the last handshake before sampling
        read_/write_crc_value etc. -- see the per-block TBs' settle()
        for the registered-pipeline rationale."""
        for _ in range(cycles):
            await RisingEdge(self.dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")

    # ---- stimulus ----

    async def read_burst(self, addr: int, burst_len: int,
                         axi_id: int = 0) -> List[int]:
        return await self.rd_master.read_transaction(
            address=addr, burst_len=burst_len, id=axi_id,
            size=self._size, burst_type=1)

    async def write_burst(self, addr: int, data_list: List[int],
                          axi_id: int = 0) -> dict:
        return await self.wr_master.write_transaction(
            address=addr, data=data_list, burst_len=len(data_list),
            id=axi_id, size=self._size, burst_type=1)

    # ---- per-channel telemetry (packed-array slicing) ----

    def _slice_field(self, whole: int, channel: int, width: int) -> int:
        return (whole >> (channel * width)) & ((1 << width) - 1)

    def read_crc_value(self, channel: int = 0) -> int:
        return self._slice_field(int(self.dut.read_crc_value.value), channel, 32)

    def read_crc_valid(self, channel: int = 0) -> int:
        return self._slice_field(int(self.dut.read_crc_valid.value), channel, 1)

    def read_beat_count(self, channel: int = 0) -> int:
        return self._slice_field(int(self.dut.read_beat_count.value), channel, 32)

    def write_crc_value(self, channel: int = 0) -> int:
        return self._slice_field(int(self.dut.write_crc_value.value), channel, 32)

    def write_crc_valid(self, channel: int = 0) -> int:
        return self._slice_field(int(self.dut.write_crc_valid.value), channel, 1)

    def write_beat_count(self, channel: int = 0) -> int:
        return self._slice_field(int(self.dut.write_beat_count.value), channel, 32)

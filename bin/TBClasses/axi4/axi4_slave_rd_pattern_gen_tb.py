# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: axi4_slave_rd_pattern_gen_tb
# Purpose: Direct FUB TB for axi4_slave_rd_pattern_gen. This block IS an
#          AXI4 slave (LFSR pattern source + per-channel CRC-32
#          accumulator), so the TB drives it with the framework's
#          AXI4MasterRead BFM on the s_axi_* port -- never a hand-rolled
#          AR/R poke.

"""TB for `axi4_slave_rd_pattern_gen`.

Drives the DUT's ``s_axi_*`` (AR/R) port with the framework's
``AXI4MasterRead`` interface (``CocoTBFramework.components.axi4.axi4_interfaces``).

Per-channel LFSR + CRC mirror:
  - Channel N's LFSR is seeded with ``LFSR_SEED ^ N`` (RTL default
    ``LFSR_SEED = 32'hDEADBEEF``), taps ``{23,3,2,1}`` -- delegates to the
    canonical ``TBClasses.common.lfsr_mirror.simulate_xor_lfsr`` shared
    with the sibling master-side pattern-gen/CRC-check TBs.
  - CRC config is ``REFIN=1, REFOUT=1`` (the slave module's parameter
    defaults -- note this differs from the MASTER-side pattern-gen/
    crc-check blocks, which hardwire ``REFIN=0, REFOUT=0`` into their
    dataint_crc instances). REFIN=1/REFOUT=1/POLY=0x04C11DB7/
    INIT=XOROUT=0xFFFFFFFF is the *standard* CRC-32 (verified against the
    canonical check value 0xCBF43926 for ASCII "123456789"). Byte order
    into the CRC is little-endian per 32-bit LFSR word (cascade stage 0
    processes ``data[7:0]`` -- the LSB byte -- first; REFIN only flips
    bits *within* a byte, it doesn't change which byte goes first).

Per-channel telemetry (``read_crc_value``/``read_crc_valid``/
``read_beat_count``) are SystemVerilog packed 2D arrays
(``logic [NUM_CHANNELS-1:0][31:0] ...``), which Verilator/cocotb expose
as ONE flat vector -- there is no ``dut.read_crc_value[ch]`` sub-handle
(confirmed empirically: indexing raises "contains no object at index").
Per-channel values are extracted by slicing the flat integer in Python.
"""

from __future__ import annotations

import logging
import os
from typing import List, Optional

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase
from TBClasses.common.lfsr_mirror import simulate_xor_lfsr as _shared_lfsr

from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterRead


_NBA_SETTLE_PS = 100


class SlaveRdPatternGenTB(TBBase):
    CLK = 10

    LFSR_DEFAULT_SEED = 0xDEADBEEF
    LFSR_TAPS = (23, 3, 2, 1)
    LFSR_WIDTH = 32

    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.dut = dut
        self.log = logging.getLogger("slave_rd_pattern_gen_tb")
        self.log.setLevel(logging.INFO)

        self.AXI_DATA_WIDTH = self.convert_to_int(
            os.environ.get("AXI_DATA_WIDTH", "64"))
        self.AXI_ID_WIDTH = self.convert_to_int(
            os.environ.get("AXI_ID_WIDTH", "8"))
        self.NUM_CHANNELS = self.convert_to_int(
            os.environ.get("NUM_CHANNELS", "1"))
        self.CIW = max(1, (self.NUM_CHANNELS - 1).bit_length()) \
            if self.NUM_CHANNELS > 1 else 1

        self.MASK_DATA = (1 << self.AXI_DATA_WIDTH) - 1
        self.BYTES_PER_BEAT = self.AXI_DATA_WIDTH // 8
        self._arsize = (self.BYTES_PER_BEAT).bit_length() - 1

        self.master: Optional[AXI4MasterRead] = None

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

        self.master = AXI4MasterRead(
            dut=self.dut, clock=self.dut.aclk,
            prefix="s_axi_",
            log=self.log,
            data_width=self.AXI_DATA_WIDTH,
            id_width=self.AXI_ID_WIDTH,
            addr_width=32,
            user_width=1,
            multi_sig=True,
            timeout_cycles=20_000,
        )
        await self.reset_lfsr()

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self) -> None:
        self.dut.aresetn.value = 0
        self.dut.crc_lfsr_reset.value = 0

    # ---- LFSR reset ----

    async def reset_lfsr(self) -> None:
        """Pulse crc_lfsr_reset for one cycle -- reseeds every channel's
        LFSR to LFSR_SEED ^ channel and clears CRC/beat-count state."""
        self.dut.crc_lfsr_reset.value = 1
        await RisingEdge(self.dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")
        self.dut.crc_lfsr_reset.value = 0
        await RisingEdge(self.dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")

    async def settle(self, cycles: int = 4) -> None:
        """Wait a few clocks after the last R handshake before sampling
        read_crc_value/read_crc_valid/read_beat_count. dataint_crc has 2
        cycles of latency (cascade + registered output) and the
        wrapper's own per-channel valid/beat-count registers add
        another -- read_transaction() returns as soon as the last R
        beat is popped from the BFM's callback-fed deque, which can be
        a delta or two ahead of those registers settling."""
        for _ in range(cycles):
            await RisingEdge(self.dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")

    # ---- stimulus ----

    def channel_of(self, axi_id: int) -> int:
        if self.NUM_CHANNELS == 1:
            return 0
        return axi_id & ((1 << self.CIW) - 1)

    async def read_burst(self, addr: int, burst_len: int,
                         axi_id: int = 0) -> List[int]:
        return await self.master.read_transaction(
            address=addr, burst_len=burst_len, id=axi_id,
            size=self._arsize, burst_type=1)

    # ---- Python LFSR/data mirror (per channel) ----

    def expected_lfsr_words(self, count: int, channel: int = 0) -> List[int]:
        seed = self.LFSR_DEFAULT_SEED ^ channel
        return _shared_lfsr(seed=seed, taps=self.LFSR_TAPS,
                            cycles=count - 1, width=self.LFSR_WIDTH,
                            include_seed=True)

    def expected_data_words(self, count: int, channel: int = 0) -> List[int]:
        lfsr_words = self.expected_lfsr_words(count, channel)
        rep = (self.AXI_DATA_WIDTH + 31) // 32
        out = []
        for w in lfsr_words:
            full = 0
            for k in range(rep):
                full |= (w & 0xFFFFFFFF) << (k * 32)
            out.append(full & self.MASK_DATA)
        return out

    # ---- Python CRC mirror: standard CRC-32 (REFIN=1, REFOUT=1) ----

    def expected_crc32(self, count: int, channel: int = 0) -> int:
        from crc import Calculator, Configuration
        cfg = Configuration(width=32, polynomial=0x04C11DB7,
                            init_value=0xFFFFFFFF, final_xor_value=0xFFFFFFFF,
                            reverse_input=True, reverse_output=True)
        data = bytearray()
        for w in self.expected_lfsr_words(count, channel):
            data += int(w).to_bytes(4, "little")
        return Calculator(cfg).checksum(bytes(data))

    # ---- per-channel telemetry (packed-array slicing; see module docstring) ----

    def _slice_field(self, whole: int, channel: int, width: int) -> int:
        return (whole >> (channel * width)) & ((1 << width) - 1)

    def crc_value(self, channel: int = 0) -> int:
        return self._slice_field(int(self.dut.read_crc_value.value), channel, 32)

    def crc_valid(self, channel: int = 0) -> int:
        return self._slice_field(int(self.dut.read_crc_valid.value), channel, 1)

    def beat_count(self, channel: int = 0) -> int:
        return self._slice_field(int(self.dut.read_beat_count.value), channel, 32)

    def beat_count_total(self) -> int:
        return int(self.dut.read_beat_count_total.value)

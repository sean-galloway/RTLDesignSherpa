# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: axi4_slave_wr_crc_check_tb
# Purpose: Direct FUB TB for axi4_slave_wr_crc_check. This block IS an
#          AXI4 slave (per-channel CRC-32 accumulator over received W
#          data), so the TB drives it with the framework's
#          AXI4MasterWrite BFM on the s_axi_* port -- never a hand-rolled
#          AW/W/B poke.

"""TB for `axi4_slave_wr_crc_check`.

IMPORTANT ARCHITECTURAL NOTE (verified by reading the RTL, not assumed):
this module has NO internal "expected data" regeneration and NO error
output. It is a pure CRC-32 accumulator over whatever it receives on W,
per channel (demuxed off the low bits of the captured AWID) -- see
``read_crc_value``/``read_crc_valid``/``read_beat_count`` on the sibling
read-side module and ``write_crc_value``/``write_crc_valid``/
``write_beat_count`` here. There is no ``o_data_error`` port.

The module header of the bundling wrapper (``axi4_dma_slaves.sv``) spells
out the actual integrity architecture: "the master writes back the same
LFSR data it read, so both sides compute against the same CRC" -- i.e.
corruption is detected EXTERNALLY, by comparing this module's
``write_crc_value`` against the read-side ``axi4_slave_rd_pattern_gen``'s
``read_crc_value`` (that comparison is exercised in
``test_axi4_dma_slaves.py``, which drives both sides of one DUT).

This TB's own "corrupted beat" scenario proves the accumulation-over-
actual-data contract directly: CRC over a stream with one beat flipped
must (a) match the software CRC computed over that same corrupted
stream, and (b) differ from the CRC computed over the clean stream --
i.e. a single-beat corruption is guaranteed visible to whatever
compares this CRC against a golden reference.

CRC config: REFIN=1, REFOUT=1 (this module's parameter defaults) =
standard CRC-32 (verified against the canonical check value
0xCBF43926 for ASCII "123456789"), little-endian byte order per 32-bit
word -- same convention as the sibling read-side TB.
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
from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS

from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterWrite
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer


_NBA_SETTLE_PS = 100


class SlaveWrCrcCheckTB(TBBase):
    CLK = 10

    # Not an RTL parameter here (this module has no seed input) -- just
    # the seed the TB uses to synthesize a representative LFSR-shaped
    # write stream, matching the convention the read-side pattern
    # generator and the master-side pattern-gen/crc-check blocks use.
    LFSR_DEFAULT_SEED = 0xDEADBEEF
    LFSR_TAPS = (23, 3, 2, 1)
    LFSR_WIDTH = 32

    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.dut = dut
        self.log = logging.getLogger("slave_wr_crc_check_tb")
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
        self._awsize = (self.BYTES_PER_BEAT).bit_length() - 1

        self.master: Optional[AXI4MasterWrite] = None

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

        self.master = AXI4MasterWrite(
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
        await self.reset_crc()

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self) -> None:
        self.dut.aresetn.value = 0
        self.dut.crc_reset.value = 0

    async def reset_crc(self) -> None:
        """Pulse crc_reset for one cycle -- clears every channel's CRC
        accumulator/beat-count state."""
        self.dut.crc_reset.value = 1
        await RisingEdge(self.dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")
        self.dut.crc_reset.value = 0
        await RisingEdge(self.dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")

    async def settle(self, cycles: int = 4) -> None:
        """Wait a few clocks after the last B handshake before sampling
        write_crc_value/write_crc_valid/write_beat_count -- same
        registered-pipeline rationale as the read-side TB's settle()."""
        for _ in range(cycles):
            await RisingEdge(self.dut.aclk)
        await Timer(_NBA_SETTLE_PS, units="ps")

    # ---- B-channel timing ----

    def set_bready_delay_profile(self, profile: str) -> None:
        """Apply a ready_delay randomizer to the B channel (our master's
        B_Slave sub-component, which drives s_axi_bready)."""
        if profile not in AXI_RANDOMIZER_CONFIGS:
            raise ValueError(f"unknown profile {profile!r}")
        cfg = AXI_RANDOMIZER_CONFIGS[profile]["slave"]
        self.master.b_channel.set_randomizer(FlexRandomizer(cfg))

    # ---- stimulus ----

    def channel_of(self, axi_id: int) -> int:
        if self.NUM_CHANNELS == 1:
            return 0
        return axi_id & ((1 << self.CIW) - 1)

    def _replicate(self, word32: int) -> int:
        rep = (self.AXI_DATA_WIDTH + 31) // 32
        full = 0
        w = word32 & 0xFFFFFFFF
        for k in range(rep):
            full |= w << (k * 32)
        return full & self.MASK_DATA

    async def write_burst(self, addr: int, words: List[int],
                          axi_id: int = 0) -> dict:
        """Write `words` (32-bit values, one per beat), each replicated
        across AXI_DATA_WIDTH the same way the read-side pattern
        generator does. Returns the write_transaction() result dict."""
        data_list = [self._replicate(w) for w in words]
        return await self.master.write_transaction(
            address=addr, data=data_list, burst_len=len(words),
            id=axi_id, size=self._awsize, burst_type=1)

    # ---- Python LFSR mirror (synthesized write stream) ----

    def channel_words(self, count: int, channel: int = 0) -> List[int]:
        seed = self.LFSR_DEFAULT_SEED ^ channel
        return _shared_lfsr(seed=seed, taps=self.LFSR_TAPS,
                            cycles=count - 1, width=self.LFSR_WIDTH,
                            include_seed=True)

    # ---- Python CRC mirror: standard CRC-32 (REFIN=1, REFOUT=1) over an
    # arbitrary 32-bit word list (so callers can compute the CRC of both
    # a clean stream and a corrupted variant of it) ----

    def expected_crc32_over_words(self, words: List[int]) -> int:
        from crc import Calculator, Configuration
        cfg = Configuration(width=32, polynomial=0x04C11DB7,
                            init_value=0xFFFFFFFF, final_xor_value=0xFFFFFFFF,
                            reverse_input=True, reverse_output=True)
        data = bytearray()
        for w in words:
            data += (int(w) & 0xFFFFFFFF).to_bytes(4, "little")
        return Calculator(cfg).checksum(bytes(data))

    # ---- per-channel telemetry (packed-array slicing) ----

    def _slice_field(self, whole: int, channel: int, width: int) -> int:
        return (whole >> (channel * width)) & ((1 << width) - 1)

    def crc_value(self, channel: int = 0) -> int:
        return self._slice_field(int(self.dut.write_crc_value.value), channel, 32)

    def crc_valid(self, channel: int = 0) -> int:
        return self._slice_field(int(self.dut.write_crc_valid.value), channel, 1)

    def beat_count(self, channel: int = 0) -> int:
        return self._slice_field(int(self.dut.write_beat_count.value), channel, 32)

    def beat_count_total(self) -> int:
        return int(self.dut.write_beat_count_total.value)

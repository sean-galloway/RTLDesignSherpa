# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: axi3_loopback_tb
# Purpose: Testbench for AXI4 -> AXI3 -> AXI4 loopback equivalence chain
#
# Author: RTL Design Sherpa
# Created: 2026-10-10

"""Testbench for the AXI4/AXI3 loopback equivalence chain.

Topology:
  AXI4MasterRead/Write (s_axi_) -> axi4_to_axi3 -> axi3_to_axi4
                                    -> AXI4SlaveRead/Write (m_axi_, shared memory)

The integration proof verifies that legal AXI4 traffic is unchanged by the
converter pair.  The write side serializes because axi3_to_axi4_wr enforces a
single-active-write contract; the read side pipelines.
"""

import asyncio
import os
import random
import sys
from collections import deque

import cocotb
from cocotb.triggers import Lock, RisingEdge

from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

repo_root = get_repo_root()
sys.path.insert(0, repo_root)
from CocoTBFramework.components.axi4.axi4_interfaces import (
    AXI4MasterRead,
    AXI4MasterWrite,
    AXI4SlaveRead,
    AXI4SlaveWrite,
)
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer


class AXI3LoopbackTB(TBBase):
    """Combined testbench for the AXI4 -> AXI3 -> AXI4 loopback chain."""

    def __init__(self, dut):
        super().__init__(dut)

        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        self.data_width = self.convert_to_int(os.environ.get('AXI_DATA_WIDTH', '32'))
        self.addr_width = self.convert_to_int(os.environ.get('AXI_ADDR_WIDTH', '32'))
        self.id_width = self.convert_to_int(os.environ.get('AXI_ID_WIDTH', '8'))
        self.bytes_per_beat = self.data_width // 8
        self.strb_width = self.bytes_per_beat
        self.addr_mask = (1 << self.addr_width) - 1
        self.data_mask = (1 << self.data_width) - 1

        self.stats = {
            'errors': 0,
            'read_errors': 0,
            'write_errors': 0,
            'read_bursts': 0,
            'write_bursts': 0,
            'read_beats': 0,
            'write_beats': 0,
        }

        # Sent-record map for far-side identity checks: (txn_id, base_addr) -> [(data, strb), ...]
        self.sent_records = {}

        # Serializes write-and-check sequences so far-side beat slices stay
        # unambiguous even when multiple Python tasks issue writes concurrently.
        self.write_check_lock = Lock(name="write_check_lock")

        # AXI4 masters drive the near (slave) side of the chain
        self.axi4_rd_master = AXI4MasterRead(
            dut=dut,
            clock=self.clk,
            prefix="s_axi_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True,
        )

        self.axi4_wr_master = AXI4MasterWrite(
            dut=dut,
            clock=self.clk,
            prefix="s_axi_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True,
        )

        # Shared memory model backing both far-side AXI4 slaves
        self.memory_lines = 4096
        self.memory_model = MemoryModel(
            num_lines=self.memory_lines,
            bytes_per_line=self.bytes_per_beat,
            log=self.log
        )
        # Pre-fill memory with address-as-data pattern so read-only identity
        # checks do not depend on prior writes.
        self._init_memory_address_pattern()

        self.axi4_rd_slave = AXI4SlaveRead(
            dut=dut,
            clock=self.clk,
            prefix="m_axi_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True,
            response_delay=1,
            memory_model=self.memory_model,
            base_addr=0,
        )
        self.axi4_rd_slave.ar_channel.set_ready_policy('always')

        self.axi4_wr_slave = AXI4SlaveWrite(
            dut=dut,
            clock=self.clk,
            prefix="m_axi_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True,
            response_delay=1,
            memory_model=self.memory_model,
            base_addr=0,
        )
        self.axi4_wr_slave.aw_channel.set_ready_policy('always')
        self.axi4_wr_slave.w_channel.set_ready_policy('always')

        # Far-side AXI4 transaction monitors
        self.far_ar_beats = []
        self.far_r_beats = []
        self.far_aw_beats = []
        self.far_w_beats = []
        self.far_b_beats = []

        self.outstanding_reads = {}
        self.outstanding_writes = {}
        self.pending_b_responses = {}
        self.early_w_count = 0
        self.early_w_last_seen = False

        self.log.info(
            f"AXI3 loopback TB: dw={self.data_width} aw={self.addr_width} id={self.id_width}"
        )

    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Reset sequence complete")

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    def _ensure_id_queue(self, container, id_value):
        """Return a deque for id_value in container, creating it if needed."""
        if id_value not in container:
            container[id_value] = deque()
        return container[id_value]

    def _init_memory_address_pattern(self):
        """Fill memory so each bus-aligned word reads back as its address."""
        for word_addr in range(0, self.memory_model.size, self.bytes_per_beat):
            data = word_addr & self.data_mask
            data_bytes = self.memory_model.integer_to_bytearray(data, self.bytes_per_beat)
            self.memory_model.write(word_addr, data_bytes, (1 << self.bytes_per_beat) - 1)

    async def far_side_monitor(self):
        """Record every far-side AXI4 handshake and assert protocol basics.

        Tracks outstanding reads/writes by ID so out-of-order responses across
        different IDs are handled correctly.  Buffers early W beats (legal when
        W is driven before AW under the converter's single-active-write contract)
        and associates them with the next AW.
        """
        self.log.info("Starting far-side AXI4 monitor")
        while True:
            await RisingEdge(self.clk)

            if (int(self.dut.m_axi_arvalid.value) == 1 and
                    int(self.dut.m_axi_arready.value) == 1):
                ar_id = int(self.dut.m_axi_arid.value)
                ar_len = int(self.dut.m_axi_arlen.value)
                self.far_ar_beats.append({
                    'id': ar_id,
                    'addr': int(self.dut.m_axi_araddr.value),
                    'len': ar_len,
                })
                self._ensure_id_queue(self.outstanding_reads, ar_id).append({
                    'beats_remaining': ar_len + 1,
                })

            if (int(self.dut.m_axi_rvalid.value) == 1 and
                    int(self.dut.m_axi_rready.value) == 1):
                r_id = int(self.dut.m_axi_rid.value)
                r_last = int(self.dut.m_axi_rlast.value)
                self.far_r_beats.append({
                    'id': r_id,
                    'data': int(self.dut.m_axi_rdata.value),
                    'resp': int(self.dut.m_axi_rresp.value),
                    'last': r_last,
                })

                if (r_id not in self.outstanding_reads or
                        not self.outstanding_reads[r_id]):
                    self.log.error(
                        f"R channel beat with no outstanding read (rid={r_id})"
                    )
                    self.stats['read_errors'] += 1
                    self.stats['errors'] += 1
                else:
                    expected = self.outstanding_reads[r_id][0]
                    expected_last = 1 if expected['beats_remaining'] == 1 else 0
                    if r_last != expected_last:
                        self.log.error(
                            f"RLAST mismatch for id={r_id}: "
                            f"got {r_last}, expected {expected_last} "
                            f"(beats_remaining={expected['beats_remaining']})"
                        )
                        self.stats['read_errors'] += 1
                        self.stats['errors'] += 1
                    expected['beats_remaining'] -= 1
                    if expected['beats_remaining'] == 0:
                        self.outstanding_reads[r_id].popleft()

            if (int(self.dut.m_axi_awvalid.value) == 1 and
                    int(self.dut.m_axi_awready.value) == 1):
                aw_id = int(self.dut.m_axi_awid.value)
                aw_len = int(self.dut.m_axi_awlen.value)
                self.far_aw_beats.append({
                    'id': aw_id,
                    'addr': int(self.dut.m_axi_awaddr.value),
                    'len': aw_len,
                })

                total_beats = aw_len + 1 - self.early_w_count
                if total_beats < 0:
                    self.log.error(
                        f"AW for id={aw_id}: more early W beats ({self.early_w_count}) "
                        f"than burst length ({aw_len + 1})"
                    )
                    self.stats['write_errors'] += 1
                    self.stats['errors'] += 1
                    total_beats = 0
                if self.early_w_last_seen and self.early_w_count != aw_len + 1:
                    self.log.error(
                        f"AW for id={aw_id}: early WLAST seen but early beat count "
                        f"({self.early_w_count}) != burst length ({aw_len + 1})"
                    )
                    self.stats['write_errors'] += 1
                    self.stats['errors'] += 1

                if total_beats > 0:
                    self._ensure_id_queue(self.outstanding_writes, aw_id).append({
                        'beats_remaining': total_beats,
                    })
                self._ensure_id_queue(self.pending_b_responses, aw_id).append({})

                self.early_w_count = 0
                self.early_w_last_seen = False

            if (int(self.dut.m_axi_wvalid.value) == 1 and
                    int(self.dut.m_axi_wready.value) == 1):
                w_last = int(self.dut.m_axi_wlast.value)
                self.far_w_beats.append({
                    'data': int(self.dut.m_axi_wdata.value),
                    'strb': int(self.dut.m_axi_wstrb.value),
                    'last': w_last,
                })

                active_write = None
                for q in self.outstanding_writes.values():
                    if q:
                        active_write = q[0]
                        break

                if active_write is None:
                    self.early_w_count += 1
                    if w_last:
                        self.early_w_last_seen = True
                else:
                    expected_last = 1 if active_write['beats_remaining'] == 1 else 0
                    if w_last != expected_last:
                        self.log.error(
                            f"WLAST mismatch: got {w_last}, expected {expected_last} "
                            f"(beats_remaining={active_write['beats_remaining']})"
                        )
                        self.stats['write_errors'] += 1
                        self.stats['errors'] += 1
                    active_write['beats_remaining'] -= 1
                    if active_write['beats_remaining'] == 0:
                        for q in self.outstanding_writes.values():
                            if q and q[0] is active_write:
                                q.popleft()
                                break

            if (int(self.dut.m_axi_bvalid.value) == 1 and
                    int(self.dut.m_axi_bready.value) == 1):
                b_id = int(self.dut.m_axi_bid.value)
                b_resp = int(self.dut.m_axi_bresp.value)
                self.far_b_beats.append({
                    'id': b_id,
                    'resp': b_resp,
                })
                if (b_id not in self.pending_b_responses or
                        not self.pending_b_responses[b_id]):
                    self.log.error(
                        f"B channel response with no outstanding write (bid={b_id})"
                    )
                    self.stats['write_errors'] += 1
                    self.stats['errors'] += 1
                else:
                    expected = self.pending_b_responses[b_id].popleft()
                    if b_resp != 0:
                        self.log.error(
                            f"BRESP mismatch for id={b_id}: got {b_resp}, expected 0"
                        )
                        self.stats['write_errors'] += 1
                        self.stats['errors'] += 1

    # ------------------------------------------------------------------
    # Identity helpers
    # ------------------------------------------------------------------

    def _addr_as_data(self, addr):
        """Expected read data for an unwritten address (memory model returns address)."""
        return addr & self.data_mask

    def _expected_readback(self, base_addr, write_data, strb):
        """Expected full-width data after writing write_data with strobe strb.

        Unstrobed bytes keep the value already in memory at that byte lane.
        """
        expected = []
        for i, wdata in enumerate(write_data):
            addr = (base_addr + (i * self.bytes_per_beat)) & self.addr_mask
            # Memory model is byte-addressed; read current content at bus-aligned word
            bus_aligned = addr & ~(self.bytes_per_beat - 1)
            if self.memory_model.in_range(bus_aligned, self.bytes_per_beat):
                prior_bytes = self.memory_model.read(bus_aligned, self.bytes_per_beat)
                prior = self.memory_model.bytearray_to_integer(prior_bytes)
            else:
                prior = 0

            merged = 0
            for b in range(self.bytes_per_beat):
                if (strb >> b) & 1:
                    merged |= ((wdata >> (b * 8)) & 0xFF) << (b * 8)
                else:
                    merged |= ((prior >> (b * 8)) & 0xFF) << (b * 8)
            expected.append(merged & self.data_mask)
        return expected

    async def _write_and_readback(self, base_addr, write_data, txn_id, strb=None):
        """Write a burst through the chain and read it back, verifying identity."""
        burst_len = len(write_data)
        size = self.bytes_per_beat.bit_length() - 1
        if strb is None:
            strb = (1 << self.strb_width) - 1

        self.log.info(
            f"Write/readback id={txn_id} addr=0x{base_addr:08X} len={burst_len} strb=0x{strb:02X}"
        )

        expected = self._expected_readback(base_addr, write_data, strb)

        async with self.write_check_lock:
            self.sent_records[(txn_id, base_addr)] = [
                (d & self.data_mask, strb) for d in write_data
            ]
            initial_w_count = len(self.far_w_beats)

            write_result = await self.axi4_wr_master.write_transaction(
                address=base_addr,
                data=write_data,
                burst_type=1,
                size=size,
                id=txn_id,
                strb=strb,
            )

            if not write_result.get('success', False):
                self.log.error(
                    f"write id={txn_id} @0x{base_addr:08X} failed: {write_result}"
                )
                self.stats['write_errors'] += 1
                self.stats['errors'] += 1
                return False

            self.stats['write_bursts'] += 1
            self.stats['write_beats'] += burst_len

            # Wait for the far-side W beats to arrive, with a small timeout.
            timeout_cycles = 0
            while len(self.far_w_beats) - initial_w_count < burst_len:
                await self.wait_clocks('aclk', 1)
                timeout_cycles += 1
                if timeout_cycles > 1000:
                    self.log.error(
                        f"write id={txn_id} @0x{base_addr:08X}: far-side W beats missing "
                        f"(got {len(self.far_w_beats) - initial_w_count}, expected {burst_len})"
                    )
                    self.stats['write_errors'] += 1
                    self.stats['errors'] += 1
                    return False

            # Compare far-side W beats against the sent record.
            w_slice = self.far_w_beats[initial_w_count:initial_w_count + burst_len]
            for i, (sent_data, sent_strb) in enumerate(self.sent_records[(txn_id, base_addr)]):
                got = w_slice[i]
                if got['data'] != sent_data or got['strb'] != sent_strb:
                    self.log.error(
                        f"far-side W beat {i} id={txn_id} "
                        f"@0x{base_addr + i * self.bytes_per_beat:08X}: "
                        f"got data=0x{got['data']:0{self.bytes_per_beat * 2}X} "
                        f"strb=0x{got['strb']:02X}, "
                        f"expected data=0x{sent_data:0{self.bytes_per_beat * 2}X} "
                        f"strb=0x{sent_strb:02X}"
                    )
                    self.stats['write_errors'] += 1
                    self.stats['errors'] += 1
                    return False

        read_data = await self.axi4_rd_master.read_transaction(
            address=base_addr,
            burst_len=burst_len,
            burst_type=1,
            size=size,
            id=txn_id,
        )

        self.stats['read_bursts'] += 1
        self.stats['read_beats'] += burst_len

        if len(read_data) != burst_len:
            self.log.error(
                f"readback id={txn_id}: expected {burst_len} beats, got {len(read_data)}"
            )
            self.stats['read_errors'] += 1
            self.stats['errors'] += 1
            return False

        success = True
        for i, (got, exp) in enumerate(zip(read_data, expected)):
            if got != exp:
                self.log.error(
                    f"readback id={txn_id} beat {i} @0x{base_addr + i * self.bytes_per_beat:08X}: "
                    f"got 0x{got:0{self.bytes_per_beat * 2}X}, expected 0x{exp:0{self.bytes_per_beat * 2}X}"
                )
                self.stats['read_errors'] += 1
                self.stats['errors'] += 1
                success = False

        return success

    async def _read_identity(self, base_addr, burst_len, txn_id):
        """Issue a read burst and verify each beat equals its byte address."""
        size = self.bytes_per_beat.bit_length() - 1
        self.log.info(
            f"Read identity id={txn_id} addr=0x{base_addr:08X} len={burst_len}"
        )

        read_data = await self.axi4_rd_master.read_transaction(
            address=base_addr,
            burst_len=burst_len,
            burst_type=1,
            size=size,
            id=txn_id,
        )

        self.stats['read_bursts'] += 1
        self.stats['read_beats'] += burst_len

        if len(read_data) != burst_len:
            self.log.error(
                f"read identity id={txn_id}: expected {burst_len} beats, got {len(read_data)}"
            )
            self.stats['read_errors'] += 1
            self.stats['errors'] += 1
            return False

        success = True
        for i, got in enumerate(read_data):
            exp_addr = (base_addr + (i * self.bytes_per_beat)) & self.addr_mask
            exp = self._addr_as_data(exp_addr)
            if got != exp:
                self.log.error(
                    f"read identity id={txn_id} beat {i}: got 0x{got:08X}, expected 0x{exp:08X}"
                )
                self.stats['read_errors'] += 1
                self.stats['errors'] += 1
                success = False

        return success

    # ------------------------------------------------------------------
    # Test scenarios
    # ------------------------------------------------------------------

    async def loopback_identity_len1_to_64(self, lengths=None):
        """Sweep burst lengths and verify data/address/strb identity."""
        if lengths is None:
            lengths = [1, 2, 15, 16, 17, 31, 32, 33, 64]

        self.log.info("=" * 80)
        self.log.info(f"LOOPBACK IDENTITY: lengths {lengths}")
        self.log.info("=" * 80)

        self._init_memory_address_pattern()

        success = True
        base = 0x1000
        spacing = 0x300
        read_offset = 0x1000

        for idx, blen in enumerate(lengths):
            write_addr = base + (idx * spacing)
            read_addr = write_addr + read_offset

            write_data = [
                (0xA000_0000 + (idx << 16) + (i * 0x0101_0101)) & self.data_mask
                for i in range(blen)
            ]

            # Vary strobe: full, then a random non-trivial strobe per burst
            if idx == 0:
                strb = (1 << self.strb_width) - 1
            else:
                # Ensure at least one byte enabled but not all
                while True:
                    strb = random.randint(1, (1 << self.strb_width) - 1)
                    if strb != (1 << self.strb_width) - 1:
                        break

            if not await self._write_and_readback(write_addr, write_data, idx + 1, strb):
                success = False

            if not await self._read_identity(read_addr, blen, idx + 0x10):
                success = False

        return success

    async def loopback_stall_pattern(self, seed=None):
        """Apply seeded random ready/valid stalls and verify identity."""
        if seed is None:
            seed = int(os.environ.get('SEED', '42')) + 1
        rng = random.Random(seed)
        self.log.info("=" * 80)
        self.log.info(f"LOOPBACK STALL PATTERN (seed={seed})")
        self.log.info("=" * 80)

        self._init_memory_address_pattern()

        # Moderate random delays on both master-valid and slave-ready directions.
        stall_profile = FlexRandomizer({
            'valid_delay': ([(0, 0), (1, 3)], [7, 3]),
            'ready_delay': ([(0, 0), (1, 3)], [7, 3]),
        })

        # Channels that drive valid (master side or slave response side).
        master_valid_channels = [
            self.axi4_rd_master.ar_channel,
            self.axi4_wr_master.aw_channel,
            self.axi4_wr_master.w_channel,
            self.axi4_rd_slave.r_channel,
            self.axi4_wr_slave.b_channel,
        ]
        # Channels that drive ready (far-side slave receiving channels).
        slave_ready_channels = [
            self.axi4_rd_slave.ar_channel,
            self.axi4_wr_slave.aw_channel,
            self.axi4_wr_slave.w_channel,
        ]

        # Save original randomizers and slave ready policies so they can be restored.
        original_randomizers = {ch: ch.randomizer for ch in master_valid_channels + slave_ready_channels}
        original_ready_policies = {ch: ch.ready_policy for ch in slave_ready_channels}

        # Apply the stall profile to every channel.
        for ch in master_valid_channels + slave_ready_channels:
            ch.set_randomizer(stall_profile)

        # Switch slave-ready channels to valid_first so the ready_delay field
        # of the stall profile actually gates acceptance.
        for ch in slave_ready_channels:
            ch.set_ready_policy('valid_first')

        try:
            success = True
            base = 0x1000
            spacing = 0x300
            read_offset = 0x400
            for trial in range(4):
                blen = rng.choice([1, 2, 8, 16, 17, 32])
                write_addr = base + (trial * spacing)
                read_addr = write_addr + read_offset
                txn_id = trial + 1

                write_data = [
                    (0xB000_0000 + (trial << 20) + (i * 0x0202_0202)) & self.data_mask
                    for i in range(blen)
                ]
                strb = rng.randint(1, (1 << self.strb_width) - 1)

                if not await self._write_and_readback(write_addr, write_data, txn_id, strb):
                    success = False
                if not await self._read_identity(read_addr, blen, txn_id + 0x10):
                    success = False
        finally:
            # Restore original randomizers and ready policies for later scenarios.
            for ch, orig in original_randomizers.items():
                ch.set_randomizer(orig)
            for ch, orig in original_ready_policies.items():
                ch.set_ready_policy(orig)

        return success

    async def loopback_multi_id(self, ids=None, txn_count=8):
        """Issue concurrent reads/writes with mixed IDs and lengths."""
        if ids is None:
            ids = [1, 2, 3, 4]

        self.log.info("=" * 80)
        self.log.info(f"LOOPBACK MULTI-ID: ids={ids}, txns={txn_count}")
        self.log.info("=" * 80)

        self._init_memory_address_pattern()

        rng = random.Random(int(os.environ.get('SEED', '42')) + 2)
        base = 0x1000
        id_spacing = 0x200
        # Each transaction-index block must span the full ID range so no
        # (id, txn_index) pair aliases to the same address as another pair.
        intra_spacing = len(ids) * id_spacing
        # Reads must land in a separate region from all writes because the
        # write/read tasks run concurrently and read_identity expects the
        # address-as-data pattern.
        read_offset = 0x1000

        # Build a list of descriptors; keep per-ID and per-transaction addresses apart.
        descriptors = []
        for i in range(txn_count):
            txn_id = ids[i % len(ids)]
            blen = rng.choice([1, 2, 8, 16, 17, 31])
            txn_index = i // len(ids)
            write_addr = base + (txn_id * id_spacing) + (txn_index * intra_spacing)
            read_addr = write_addr + read_offset
            descriptors.append({
                'id': txn_id,
                'write_addr': write_addr,
                'read_addr': read_addr,
                'len': blen,
                'data': [
                    (0xC000_0000 + (txn_id << 24) + (i << 16) + (j * 0x0303_0303)) & self.data_mask
                    for j in range(blen)
                ],
                'strb': rng.randint(1, (1 << self.strb_width) - 1),
            })

        # Dispatch all writes and reads concurrently; the chain serializes writes
        # but pipelines reads and different IDs.
        tasks = []
        for desc in descriptors:
            tasks.append(cocotb.start_soon(self._write_and_readback(
                desc['write_addr'], desc['data'], desc['id'], desc['strb']
            )))
            tasks.append(cocotb.start_soon(self._read_identity(
                desc['read_addr'], desc['len'], desc['id'] + 0x10
            )))

        results = []
        for t in tasks:
            results.append(await t)

        return all(results)

    # ------------------------------------------------------------------
    # Suites
    # ------------------------------------------------------------------

    async def run_gate_suite(self):
        """Gate-level suite: required identity sweep only."""
        self.log.info("=" * 80)
        self.log.info("GATE SUITE")
        self.log.info("=" * 80)
        success = True
        if not await self.loopback_identity_len1_to_64():
            success = False
        return success

    async def run_func_suite(self):
        """Func-level suite: identity + stall pattern."""
        self.log.info("=" * 80)
        self.log.info("FUNC SUITE")
        self.log.info("=" * 80)
        success = True
        if not await self.loopback_identity_len1_to_64():
            success = False
        if not await self.loopback_stall_pattern():
            success = False
        return success

    async def run_full_suite(self):
        """Full suite: identity + stall + multi-id."""
        self.log.info("=" * 80)
        self.log.info("FULL SUITE")
        self.log.info("=" * 80)
        success = True
        if not await self.loopback_identity_len1_to_64():
            success = False
        if not await self.loopback_stall_pattern():
            success = False
        if not await self.loopback_multi_id():
            success = False
        return success

    def get_statistics(self):
        return dict(self.stats)

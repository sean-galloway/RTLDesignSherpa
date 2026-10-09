# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: AXI4DWidthConverterReadTB
# Purpose: AXI4 Read Data Width Converter Testbench (READ-ONLY)
#
# Documentation: cocotb-framework PyPI package
# Subsystem: framework
#
# Author: RTL Design Sherpa
# Created: 2025-10-18

"""
AXI4 Read Data Width Converter Testbench - READ-ONLY

Reusable testbench infrastructure for testing AXI4 WRITE data width conversion.
Uses GAXI BFMs for protocol-agnostic testing of both upsize and downsize modes.

Tests ONLY the read path (AR, R channels).
For write path testing, see axi4_dwidth_converter_wr_tb.py.

Architecture:
- Slave side (narrow in upsize, wide in downsize): GAXI Master drives read transactions
- Master side (wide in upsize, narrow in downsize): GAXI Slave responds to reads
- Queue-based verification for read data integrity checking

This is infrastructure only - test intelligence resides in test runner.
"""

import os
import random
import cocotb
from cocotb.triggers import RisingEdge

# Framework imports
from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel

# AXI4 components
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_master_rd,
    create_axi4_slave_rd
)


class AXI4DWidthConverterReadTB(TBBase):
    """
    AXI4 Read Data Width Converter Testbench - Infrastructure Only (READ-ONLY)

    Provides reusable testing infrastructure for AXI4 WRITE data width converter.
    Supports both upsize (narrow→wide) and downsize (wide→narrow) write testing.

    Uses GAXI BFMs:
    - Slave side: GAXI Master to drive transactions
    - Master side: GAXI Slave to respond
    - Shared memory model for data integrity verification

    Test intelligence and scenarios reside in val/amba/test_axi4_dwidth_converter.py
    """

    def __init__(self, dut, aclk=None, aresetn=None):
        """
        Initialize AXI4 Data Width Converter Testbench

        Args:
            dut: Device under test (axi4_dwidth_converter)
            aclk: Clock signal (optional, defaults to dut.aclk)
            aresetn: Reset signal (optional, defaults to dut.aresetn)
        """
        super().__init__(dut)

        # Get test parameters from environment
        self.S_AXI_DATA_WIDTH = self.convert_to_int(os.environ.get('S_AXI_DATA_WIDTH', '32'))
        self.M_AXI_DATA_WIDTH = self.convert_to_int(os.environ.get('M_AXI_DATA_WIDTH', '128'))
        self.AXI_ID_WIDTH = self.convert_to_int(os.environ.get('AXI_ID_WIDTH', '8'))
        self.AXI_ADDR_WIDTH = self.convert_to_int(os.environ.get('AXI_ADDR_WIDTH', '32'))
        self.AXI_USER_WIDTH = self.convert_to_int(os.environ.get('AXI_USER_WIDTH', '1'))
        self.TEST_CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TIMEOUT_CYCLES = self.convert_to_int(os.environ.get('TIMEOUT_CYCLES', '2000'))

        # BUG-009 TDD: beat-level R interleave and burst-atomic OOO-R tests
        self.interleave_test = os.environ.get('DWIDTH_RD_INTERLEAVE_TEST', '0') == '1'
        self.ooo_r_test = os.environ.get('DWIDTH_RD_OOO_R_TEST', '0') == '1'

        # Calculate derived parameters
        self.WIDTH_RATIO = max(self.S_AXI_DATA_WIDTH, self.M_AXI_DATA_WIDTH) // \
                          min(self.S_AXI_DATA_WIDTH, self.M_AXI_DATA_WIDTH)
        self.UPSIZE = 1 if self.S_AXI_DATA_WIDTH < self.M_AXI_DATA_WIDTH else 0
        self.DOWNSIZE = 1 if self.S_AXI_DATA_WIDTH > self.M_AXI_DATA_WIDTH else 0
        self.S_STRB_WIDTH = self.S_AXI_DATA_WIDTH // 8
        self.M_STRB_WIDTH = self.M_AXI_DATA_WIDTH // 8

        # Initialize random generator
        random.seed(self.SEED)

        # Setup clock and reset signals
        self.aclk = aclk if aclk is not None else dut.aclk
        self.aclk_name = self.aclk._name if hasattr(self.aclk, '_name') else 'aclk'
        self.aresetn = aresetn if aresetn is not None else dut.aresetn

        # Log configuration
        mode_str = "UPSIZE" if self.UPSIZE else "DOWNSIZE"
        msg = '\n'
        msg += '='*80 + "\n"
        msg += f' AXI4 Data Width Converter Test Configuration:\n'
        msg += '-'*80 + "\n"
        msg += f' Mode:              {mode_str}\n'
        msg += f' Slave Data Width:  {self.S_AXI_DATA_WIDTH} bits\n'
        msg += f' Master Data Width: {self.M_AXI_DATA_WIDTH} bits\n'
        msg += f' Width Ratio:       {self.WIDTH_RATIO}:1\n'
        msg += f' ID Width:          {self.AXI_ID_WIDTH}\n'
        msg += f' Addr Width:        {self.AXI_ADDR_WIDTH}\n'
        msg += f' Clock Period:      {self.TEST_CLK_PERIOD} ns\n'
        msg += f' Seed:              {self.SEED}\n'
        msg += '='*80 + "\n"
        self.log.info(msg)

        # No memory model - use direct queue access per framework guidelines
        # Queue-based verification is simpler and more reliable for this test

        # Simple data store to track written data (address -> list of narrow beats)
        self.data_store = {}

        # Captured master-side data (for verification)
        # Need our own capture because AXI4SlaveWrite callbacks consume the _recvQ
        self.captured_ar_packets = []
        self.captured_r_packets = []

        # Initialize AXI4 components (to be created in setup_clocks_and_reset)
        self.slave_read_master = None   # AXI4 Master Read on slave side (drives s_axi_ar*, monitors s_axi_r*)
        self.master_read_slave = None   # AXI4 Slave Read on master side (monitors m_axi_ar*, drives m_axi_r*)

        # Statistics tracking
        self.transactions_sent = 0
        self.transactions_received = 0
        self.errors = 0

        self.log.info("AXI4 Data Width Converter TB initialized")

    async def setup_clocks_and_reset(self):
        """
        Complete initialization - starts clocks and performs reset.

        MANDATORY METHOD: Required by TBBase pattern.
        """
        # Start clock
        await self.start_clock(self.aclk_name, freq=self.TEST_CLK_PERIOD, units='ns')

        # Create AXI4 Master Write on slave side (drives s_axi_ar*, s_axi_r*, monitors (no B channel))
        try:
            self.slave_read_master = create_axi4_master_rd(
                dut=self.dut,
                clock=self.aclk,
                prefix='s_axi_',
                log=self.log,
                data_width=self.S_AXI_DATA_WIDTH,
                id_width=self.AXI_ID_WIDTH,
                addr_width=self.AXI_ADDR_WIDTH,
                super_debug=True  # Enable super_debug to validate signal connections
            )
            # Add callback to capture R on slave side (monitor)
            self.slave_read_master['R'].add_callback(self._capture_r_callback)

            self.log.info("Created AXI4 Master Read on slave side (s_axi_ar*, s_axi_r*) - with R callback")
        except Exception as e:
            self.log.error(f"Failed to create slave-side read master: {e}")
            raise

        # Create AXI4 Slave Read on master side (monitors m_axi_ar*, drives m_axi_r*)
        # NO MEMORY MODEL - using queue-based verification
        try:
            slave_kwargs = {
                'dut': self.dut,
                'clock': self.aclk,
                'prefix': 'm_axi_',
                'log': self.log,
                'data_width': self.M_AXI_DATA_WIDTH,
                'id_width': self.AXI_ID_WIDTH,
                'addr_width': self.AXI_ADDR_WIDTH,
                'super_debug': True,  # Enable super_debug to validate signal connections
            }
            if self.interleave_test or self.ooo_r_test:
                # BUG-009 TDD: drive R responses manually so we can force beat-level
                # interleaving or whole-burst OOO that the BFM's in-order scheduler
                # cannot produce while staying AXI4-compliant.
                slave_kwargs['response_delay'] = 1000000
                self.log.info("BUG-009 test: master-side slave BFM response disabled; R driven manually")
            else:
                slave_kwargs['response_delay'] = 1  # Add 1 cycle delay for response

            self.master_read_slave = create_axi4_slave_rd(**slave_kwargs)

            # Add callback to capture AR on master side (monitor)
            self.master_read_slave['AR'].add_callback(self._capture_ar_callback)

            self.log.info("Created AXI4 Slave Read on master side (m_axi_ar*, m_axi_r*) - with AR callback")
            self.log.info(f"Master-side slave R channel type: {type(self.master_read_slave['R'])}")
            self.log.info(f"Master-side slave AR channel type: {type(self.master_read_slave['AR'])}")
        except Exception as e:
            self.log.error(f"Failed to create master-side read slave: {e}")
            raise

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.aclk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.aclk_name, 5)

        # Enable VCD dumping for debug
        import os
        if os.environ.get('COCOTB_ENABLE_PROFILING', '0') == '1':
            self.log.info("VCD dumping enabled via COCOTB_ENABLE_PROFILING")

        self.log.info("Clock and reset setup complete")

    async def assert_reset(self):
        """
        Assert reset signal (active-low).

        MANDATORY METHOD: Required by TBBase pattern.
        """
        self.aresetn.value = 0
        self.log.debug("Reset asserted")

    async def deassert_reset(self):
        """
        Deassert reset signal.

        MANDATORY METHOD: Required by TBBase pattern.
        """
        self.aresetn.value = 1
        self.log.debug("Reset deasserted")

    def _capture_ar_callback(self, ar_pkt):
        """Capture AR packets for verification (called BEFORE AXI4SlaveRead processes them)"""
        # Create a copy with the data we need (packet object may be reused by BFM)
        pkt_copy = type('obj', (object,), {
            'addr': int(getattr(ar_pkt, 'addr', 0)),
            'len': int(getattr(ar_pkt, 'len', 0)),
            'id': int(getattr(ar_pkt, 'id', 0))
        })()
        self.captured_ar_packets.append(pkt_copy)
        self.log.info(f"AR CALLBACK TRIGGERED: addr=0x{pkt_copy.addr:08X}, len={pkt_copy.len}, id={pkt_copy.id}")

    def _capture_r_callback(self, r_pkt):
        """Capture R packets for verification (called BEFORE AXI4SlaveRead processes them)"""
        # Create a copy with the data we need (packet object may be reused by BFM)
        pkt_copy = type('obj', (object,), {
            'data': int(getattr(r_pkt, 'data', 0)),
            'last': int(getattr(r_pkt, 'last', 0)),
            'resp': int(getattr(r_pkt, 'resp', 0)),  # R has resp, not strb
            'id': int(getattr(r_pkt, 'id', 0))
        })()
        self.captured_r_packets.append(pkt_copy)

        # CRITICAL DEBUG: Check queue state and object identity
        queue_len = len(self.slave_read_master['R']._recvQ)
        interface_queue_len = len(self.slave_read_master['interface'].r_channel._recvQ)
        same_object = (self.slave_read_master['R'] is self.slave_read_master['interface'].r_channel)

        self.log.info(f"R CALLBACK TRIGGERED #{len(self.captured_r_packets)}: data=0x{pkt_copy.data:X}, last={pkt_copy.last}, resp={pkt_copy.resp}, id={pkt_copy.id}")
        self.log.info(f"   Queue state: dict['R']._recvQ={queue_len}, interface.r_channel._recvQ={interface_queue_len}, same_object={same_object}")

    async def clear_bfm_state(self):
        """Clear BFM internal queues to prevent stale data from affecting subsequent tests."""
        # Clear our capture lists
        self.captured_ar_packets.clear()
        self.captured_r_packets.clear()

        # Clear BFM internal queues
        if hasattr(self.master_read_slave['interface'], 'orphaned_bursts'):
            self.master_read_slave['interface'].orphaned_bursts.clear()
            self.log.debug("Cleared orphaned_bursts")

        # Clear any pending transactions in the AXI4SlaveWrite queues
        if hasattr(self.master_read_slave['interface'], 'pending_writes'):
            self.master_read_slave['interface'].pending_writes.clear()
            self.log.debug("Cleared pending_writes")

        # Wait a few cycles to let any in-flight transactions complete
        await self.wait_clocks(self.aclk_name, 10)
        self.log.info("BFM state cleared")

    def generate_traceable_data(self, txn_id, burst_len):
        """
        Generate traceable data patterns for waveform debugging.

        For downsize (wide→narrow):
        - Each wide beat is composed of multiple narrow beats
        - Pattern: 0xTT_BB_DD_SS where:
          - TT = transaction ID (0x00-0xFF)
          - BB = beat number within burst (0x00-0xFF)
          - DD = 0xDD (marker byte)
          - SS = sub-beat index (0, 1, 2, 3 for 4:1 ratio)

        For upsize (narrow→wide):
        - Multiple narrow beats combine into wide beat
        - Pattern: 0xTT_BB_DD_NN where NN = narrow beat number

        Args:
            txn_id: Transaction ID (0-255)
            burst_len: Number of beats on SLAVE side

        Returns:
            List of data values for slave side
        """
        data_list = []

        for beat_num in range(burst_len):
            if self.DOWNSIZE:
                # Downsize: Create wide beat with traceable sub-beats
                # For 128→32 (4:1), create 128-bit value with 4 distinct 32-bit lanes
                wide_value = 0
                for sub_beat in range(self.WIDTH_RATIO):
                    # Pattern: TT_BB_DD_SS (transaction, beat, marker, sub-beat)
                    lane_value = ((txn_id & 0xFF) << 24) | \
                                ((beat_num & 0xFF) << 16) | \
                                (0xDD << 8) | \
                                (sub_beat & 0xFF)
                    # Place in appropriate 32-bit lane
                    wide_value |= (lane_value << (sub_beat * self.M_AXI_DATA_WIDTH))
                data_list.append(wide_value)
            else:
                # Upsize: Create narrow beat with traceable pattern
                # Pattern: TT_BB_DD_NN (transaction, beat, marker, narrow beat number)
                narrow_value = ((txn_id & 0xFF) << 24) | \
                               ((beat_num & 0xFF) << 16) | \
                               (0xDD << 8) | \
                               (beat_num & 0xFF)
                data_list.append(narrow_value)

        return data_list

    def _build_interleave_r_beats(self, addr, slave_beats, txn_id, ar_records):
        """Build master R beats and expected slave R beats for one transaction.

        Uses the captured master AR records to set master-burst RLAST boundaries
        (downsize split) and to compute the expected slave-side data/RLAST.

        For downsize, master R beats are only generated for master AR splits that
        have already been captured.  Sending beats before their split AR is issued
        would land in the DUT reassembly layer with no record and with the wrong
        RLAST, causing the burst to stall forever.
        """
        id_records = [a for a in ar_records if int(getattr(a, 'id', 0)) == txn_id]
        if not id_records:
            return [], []

        if self.DOWNSIZE:
            # Each slave wide beat becomes WIDTH_RATIO narrow master beats.
            # The master AR records describe how the slave burst was split.
            covered_narrow_beats = sum(
                (int(getattr(a, 'len', 0)) + 1) for a in id_records)
            covered_slave_beats = covered_narrow_beats // self.WIDTH_RATIO
            master_beats = []
            for b in range(covered_slave_beats):
                for s in range(self.WIDTH_RATIO):
                    data = ((txn_id & 0xFF) << 24) | \
                           ((b & 0xFF) << 16) | \
                           (0xDD << 8) | \
                           (s & 0xFF)
                    master_beats.append({'data': data, 'last': 0})

            # Apply RLAST at the end of each master burst.
            pos = 0
            for ar in id_records:
                blen = int(getattr(ar, 'len', 0)) + 1
                master_beats[pos + blen - 1]['last'] = 1
                pos += blen

            # Expected slave beats: reconstruct wide data from narrow order.
            expected = []
            for b in range(covered_slave_beats):
                wide = 0
                for s in range(self.WIDTH_RATIO):
                    narrow = master_beats[b * self.WIDTH_RATIO + s]['data']
                    wide |= narrow << (s * self.M_AXI_DATA_WIDTH)
                expected.append({'data': wide, 'last': 1 if b == covered_slave_beats - 1 else 0})
            return master_beats, expected
        else:
            # Upsize: each master wide beat carries WIDTH_RATIO narrow beats.
            # The first wide beat may start at a non-zero lane for unaligned
            # addresses; ar_records carries the computed start lane implicitly
            # through the addressed byte positions in the wide word.
            lane = (addr % self.M_STRB_WIDTH) // self.S_STRB_WIDTH
            wide_beats = (lane + slave_beats + self.WIDTH_RATIO - 1) // self.WIDTH_RATIO
            master_beats = []
            for w in range(wide_beats):
                data = 0
                for s in range(self.WIDTH_RATIO):
                    nb = w * self.WIDTH_RATIO + s - lane
                    if 0 <= nb < slave_beats:
                        narrow = ((txn_id & 0xFF) << 24) | \
                                 ((nb & 0xFF) << 16) | \
                                 (0xDD << 8) | \
                                 (nb & 0xFF)
                        data |= narrow << (s * self.S_AXI_DATA_WIDTH)
                master_beats.append({
                    'data': data,
                    'last': 1 if w == wide_beats - 1 else 0,
                })

            # Expected slave beats are just the narrow pattern in order.
            expected = []
            for b in range(slave_beats):
                narrow = ((txn_id & 0xFF) << 24) | \
                         ((b & 0xFF) << 16) | \
                         (0xDD << 8) | \
                         (b & 0xFF)
                expected.append({'data': narrow, 'last': 1 if b == slave_beats - 1 else 0})
            return master_beats, expected

    async def _issue_ar_burst(self, addr, slave_beats, arid):
        """Issue a single slave AR burst without waiting for R responses."""
        arsize = (self.S_AXI_DATA_WIDTH // 8).bit_length() - 1
        ar_packet = self.slave_read_master['interface'].create_ar_packet(
            addr=addr,
            len=slave_beats - 1,
            id=arid,
            size=arsize,
            burst=1
        )
        await self.slave_read_master['AR'].send(ar_packet)

    async def read_transaction(self, addr, burst_len, arid=0, arsize=None, arburst=1):
        """
        Perform read transaction.

        For read converter testing:
        1. Issue AR transaction on slave side
        2. DUT forwards AR to master side, converts width
        3. Master-side slave provides R data (generated by test setup)
        4. DUT converts R data back to slave width
        5. Slave-side master receives converted R data

        Args:
            addr: Start address
            burst_len: Number of beats to read (on SLAVE side)
            arid: Transaction ID
            arsize: Bytes per beat (defaults to slave data width / 8)
            arburst: Burst type (0=FIXED, 1=INCR, 2=WRAP)

        Returns:
            List of read data values received on slave side
        """
        if arsize is None:
            arsize = (self.S_AXI_DATA_WIDTH // 8).bit_length() - 1

        self.log.info(f"ISSUING READ: addr=0x{addr:08X}, burst_len={burst_len}, id={arid}, size={arsize}")

        # Clear captured packets before transaction
        self.captured_ar_packets.clear()
        self.captured_r_packets.clear()

        # SOLUTION: Use callback-based verification instead of read_transaction() return value
        # Issue AR transaction (sends AR, but we'll collect R via callbacks)
        ar_packet = self.slave_read_master['interface'].create_ar_packet(
            addr=addr,
            len=burst_len - 1,
            id=arid,
            size=arsize,
            burst=arburst
        )

        self.log.info(f"Sending AR via slave_read_master...")
        await self.slave_read_master['AR'].send(ar_packet)

        # Wait for R responses via our callbacks (not via read_transaction)
        timeout_cycles = 2000
        cycles_waited = 0

        while len(self.captured_r_packets) < burst_len:
            await self.wait_clocks('aclk', 1)
            cycles_waited += 1

            if cycles_waited > timeout_cycles:
                self.log.error(f"READ TIMEOUT: got {len(self.captured_r_packets)}/{burst_len} R packets after {cycles_waited} cycles")
                self.log.error(f"   AR packets captured: {len(self.captured_ar_packets)}")
                raise TimeoutError(f"Callback-based read timeout: got {len(self.captured_r_packets)}/{burst_len} responses")

        # Extract data from callback-captured packets
        result = [pkt.data for pkt in self.captured_r_packets]

        self.log.info(f"READ COMPLETE: received {len(result)} data beats via callbacks")
        self.transactions_sent += 1
        return result

    def get_statistics(self):
        """
        Get testbench statistics.

        Returns:
            Dictionary with transaction counts and error counts
        """
        return {
            'transactions_sent': self.transactions_sent,
            'transactions_received': self.transactions_received,
            'errors': self.errors,
            'width_ratio': self.WIDTH_RATIO,
            'mode': 'UPSIZE' if self.UPSIZE else 'DOWNSIZE'
        }

    async def run_basic_test(self):
        """
        Basic smoke test - single write transaction with queue-based verification.

        Uses unique data patterns and collects converted data from master-side
        queues using popleft() when LAST flag occurs (per user request).

        NO READS - DUT is data width converter, not memory!

        Returns:
            True if test passes, False otherwise
        """
        self.log.info("=== Running Basic Smoke Test ===")

        # Scenario marker for testplan traceability
        if self.UPSIZE:
            self.log.info("=== Scenario DWIDTH-RD-01: Upsize single read ===")
        else:
            self.log.info("=== Scenario DWIDTH-RD-02: Downsize single read ===")

        # Write test - use unique data per beat to detect misalignment
        addr = 0x1000

        # Generate unique data pattern based on slave width
        # Each 32-bit word gets a unique replicated byte value
        words_per_beat = self.S_AXI_DATA_WIDTH // 32
        data = []
        word_counter = 1
        for beat in range(2):
            beat_data = 0
            for word_idx in range(words_per_beat):
                byte_value = word_counter & 0xFF
                # Replicate byte across 32-bit word (e.g., 0x01 → 0x01010101)
                word_value = (byte_value << 24) | (byte_value << 16) | (byte_value << 8) | byte_value
                beat_data |= (word_value << (word_idx * 32))
                word_counter += 1
            data.append(beat_data)

        # Clear captured packets before starting
        self.captured_ar_packets.clear()
        self.captured_r_packets.clear()

        # Send read request (reads don't send data, they request it)
        burst_len = len(data)  # Number of beats to read on SLAVE SIDE
        result = await self.read_transaction(addr, burst_len)
        self.log.info(f"Sent read request for {burst_len} beats at address 0x{addr:X}")

        # For reads, the result should match the requested burst_len
        # (callbacks capture R packets on slave side, so we get burst_len packets)
        expected_beats = burst_len  # We capture on SLAVE SIDE, not master side

        self.log.info(f"Captured {len(result)} R beats (expected {expected_beats})")

        # Verify we got the right number of beats
        captured_count = len(result)

        # Verify captured data matches expected
        success = (captured_count == expected_beats)
        if success:
            self.log.info(f"Basic test PASSED - collected {captured_count}/{expected_beats} beats")
            self.log.info(f"   Read data: {[hex(d) for d in result]}")
        else:
            self.log.error(f"Basic test FAILED - collected {captured_count}/{expected_beats} beats")
            if len(result) > 0:
                self.log.error(f"   Read data: {[hex(d) for d in result]}")
            self.errors += 1

        # Mid-wide-word burst start (projects/components/utility-ip/converters TASK-001, was CONV-006) -- addressed-lane data.
        if not await self.test_unaligned_wide_start():
            success = False

        return success

    async def test_unaligned_wide_start(self):
        """UPSIZE: a read burst starting mid-wide-word returns the ADDRESSED bytes.

        The converter aligns the issued wide address DOWN (the slave
        returns whole wide words); the R slicer must then start at the
        addressed lane of the FIRST wide word, so the master receives
        the bytes it asked for -- not the bytes at the aligned-down
        address (CONV-006). Also checks the wide ARLEN counts the lane
        offset: ceil((lane + narrow_beats) / RATIO) wide beats.

        Drives a byte-addressed pattern memory behind the master-side
        slave BFM so lane correctness is checkable by address.
        """
        if not self.UPSIZE:
            return True  # downsize fetches from the exact addresses

        ratio = self.WIDTH_RATIO
        s_bytes = self.S_STRB_WIDTH
        k = max(1, ratio // 2)
        addr = 0xB000 + k * s_bytes      # narrow-aligned, wide-UNALIGNED
        n_beats = 2 if ratio >= 2 else 1
        exp_wide = (k + n_beats + ratio - 1) // ratio
        span = 0xC000

        pat = bytearray(((0x5A ^ o ^ (o >> 7)) & 0xFF) for o in range(span))
        mm = MemoryModel(num_lines=span // self.M_STRB_WIDTH,
                         bytes_per_line=self.M_STRB_WIDTH,
                         preset_values=list(pat), log=self.log)
        iface = self.master_read_slave['interface']
        saved_mm = getattr(iface, 'memory_model', None)
        iface.memory_model = mm

        ok = True
        try:
            got = await self.read_transaction(addr, n_beats)

            exp = [int.from_bytes(
                       pat[addr + i * s_bytes: addr + (i + 1) * s_bytes],
                       'little')
                   for i in range(n_beats)]
            for i, (g, e) in enumerate(zip(got, exp)):
                if int(g) != e:
                    self.log.error(
                        f"unaligned-start: narrow beat {i} data 0x{int(g):X} "
                        f"!= 0x{e:X} -- the slicer must start at lane {k} of "
                        f"the first wide word (bytes of 0x{addr + i*s_bytes:X})")
                    self.errors += 1
                    ok = False

            if self.captured_ar_packets:
                ar = self.captured_ar_packets[0]
                got_len = int(getattr(ar, 'len', -1))
                if got_len != exp_wide - 1:
                    self.log.error(
                        f"unaligned-start: wide ARLEN {got_len} != "
                        f"{exp_wide - 1} (lane offset must count toward the "
                        f"wide beat total)")
                    self.errors += 1
                    ok = False

            if ok:
                self.log.info(
                    f"unaligned-start: {n_beats} narrow beats from lane {k} "
                    f"returned the addressed bytes across {exp_wide} wide "
                    f"beat(s)")
            return ok
        finally:
            iface.memory_model = saved_mm

    async def do_read_and_verify(self, addr, burst_len, debug=False):
        """Helper to read and verify using captured packets (like basic test)."""
        # Clear captured packets
        self.captured_ar_packets.clear()
        self.captured_r_packets.clear()

        if debug:
            self.log.info(f"Starting read: addr=0x{addr:08X}, beats={burst_len}")

        # Send read transaction (issues AR, waits for R responses via callbacks)
        result = await self.read_transaction(addr, burst_len)

        # For reads, callbacks capture on SLAVE SIDE, so we expect burst_len packets
        expected_beats = burst_len

        if debug:
            self.log.info(f"   Read completed at {cocotb.utils.get_sim_time('ns')}ns, received {len(result)}/{expected_beats} beats")

        # Result already contains the data from callbacks
        collected_data = result
        success = (len(collected_data) == expected_beats)

        if not success:
            self.log.error(f"Read FAILED - collected {len(collected_data)}/{expected_beats} beats at {cocotb.utils.get_sim_time('ns')}ns")
            if debug:
                self.log.error(f"   Data captured: {[f'0x{d:X}' for d in collected_data]}")
                # Check what's on the bus right now
                m_rvalid = int(self.dut.m_axi_rvalid.value) if hasattr(self.dut, 'm_axi_rvalid') else -1
                m_rready = int(self.dut.m_axi_rready.value) if hasattr(self.dut, 'm_axi_rready') else -1
                m_rlast = int(self.dut.m_axi_rlast.value) if hasattr(self.dut, 'm_axi_rlast') else -1
                self.log.error(f"   Current bus state: m_axi_rvalid={m_rvalid}, m_axi_rready={m_rready}, m_axi_rlast={m_rlast}")
            self.errors += 1
        elif debug:
            self.log.info(f"   Verification PASSED")

        return success

    async def verify_read_conversion(self, addr, burst_len, timeout_cycles=1000):
        """
        Verify read data conversion using direct queue monitoring.

        Args:
            addr: Read address
            burst_len: Number of beats to read on slave side
            timeout_cycles: Maximum cycles to wait

        Returns:
            True if verification passes, False otherwise
        """
        # Record initial queue lengths (don't clear - transactions may already be there)
        initial_ar_count = len(self.master_read_slave['interface'].ar_channel._recvQ)
        initial_r_count = len(self.master_read_slave['interface'].r_channel._recvQ)

        # Initiate read on slave side
        await self.read_transaction(addr, burst_len)

        # Calculate expected master-side beats
        if self.UPSIZE:
            # Upsize: Multiple slave beats → Single master beat
            expected_master_beats = (burst_len + self.WIDTH_RATIO - 1) // self.WIDTH_RATIO
        else:
            # Downsize: Single slave beat → Multiple master beats
            expected_master_beats = burst_len * self.WIDTH_RATIO

        # Calculate expected final queue lengths
        expected_ar_count = initial_ar_count + 1
        expected_r_count = initial_r_count + expected_master_beats

        # Wait for AR transaction on master side
        cycles = 0
        while len(self.master_read_slave['interface'].ar_channel._recvQ) < expected_ar_count and cycles < timeout_cycles:
            await self.wait_clocks(self.aclk_name, 1)
            cycles += 1

        if len(self.master_read_slave['interface'].ar_channel._recvQ) < expected_ar_count:
            actual = len(self.master_read_slave['interface'].ar_channel._recvQ)
            self.log.error(f"Timeout waiting for master AR transaction (expected {expected_ar_count}, got {actual})")
            return False

        # Wait for all R beats on master side
        cycles = 0
        while len(self.master_read_slave['interface'].r_channel._recvQ) < expected_r_count and cycles < timeout_cycles:
            await self.wait_clocks(self.aclk_name, 1)
            cycles += 1

        if len(self.master_read_slave['interface'].r_channel._recvQ) < expected_r_count:
            actual_beats = len(self.master_read_slave['interface'].r_channel._recvQ) - initial_r_count
            self.log.error(f"Expected {expected_master_beats} new master beats, got {actual_beats}")
            return False

        # Get AR packet (the new one at index initial_ar_count)
        ar_pkt = self.master_read_slave['interface'].ar_channel._recvQ[initial_ar_count]
        master_addr = getattr(ar_pkt, 'addr', 0)

        # Verify address
        if master_addr != addr:
            self.log.error(f"Address mismatch: Expected 0x{addr:X}, got 0x{master_addr:X}")
            return False

        # Get R packets (the new ones starting at initial_r_count)
        master_data = []
        for i in range(expected_master_beats):
            r_pkt = self.master_read_slave['interface'].r_channel._recvQ[initial_r_count + i]
            data_value = getattr(r_pkt, 'data', 0)
            master_data.append(data_value)

        self.log.info(f"Read verification passed: {burst_len} slave beats → {expected_master_beats} master beats")
        return True


    async def test_max_length_burst(self):
        """A maximum-length slave read must survive downsizing.

        Downsizing multiplies the beat count, and the product overflows the
        8-bit ARLEN exactly as it did AWLEN on the write side (CONV-004): a
        slave burst longer than 256/WIDTH_RATIO beats wraps the field and
        the master returns only a fraction of the data -- the read here
        simply times out short. The fix splits one slave burst into several
        master bursts, and the slave must then see ONE RLAST, on the true
        final beat, not one per master burst.
        """
        self.log.info("--- Max-length read burst (ARLEN overflow) ---")
        if not self.DOWNSIZE:
            self.log.info("  upsize: beat count divides, nothing to overflow")
            return True

        ok = True
        safe = 256 // self.WIDTH_RATIO
        for beats in (safe, safe * 2):
            addr = 0x40000
            needed = beats * self.WIDTH_RATIO
            self.log.info(f"  slave read {beats} beats -> {needed} narrow "
                          f"beats ({'fits' if needed <= 256 else 'needs splitting'})")
            try:
                data = await self.read_transaction(addr, beats)
            except TimeoutError:
                self.log.error(f"  max-length read TIMED OUT at {beats} slave "
                               f"beats ({needed} narrow) -- ARLEN truncated")
                self.errors += 1
                ok = False
                continue
            if len(data) != beats:
                self.log.error(f"  max-length read: {len(data)}/{beats} beats")
                self.errors += 1
                ok = False
                continue

            # Framing: the slave must see exactly one RLAST, on the final
            # beat. A split without RLAST masking delivers one per master
            # burst instead.
            lasts = [i for i, pkt in enumerate(self.captured_r_packets)
                     if int(getattr(pkt, 'last', 0)) == 1]
            if lasts != [beats - 1]:
                self.log.error(f"  RLAST framing: asserted at {lasts}, "
                               f"expected [{beats - 1}] only")
                self.errors += 1
                ok = False
                continue
            self.log.info(f"  framing OK: {beats} beats, single RLAST on "
                          f"the final beat")
        return ok


    async def test_rresp_severity_fold(self):
        """Mixed sub-beat responses must fold by SEVERITY, not bitwise OR.

        A wide beat is assembled from WIDTH_RATIO narrow beats, each with
        its own RRESP. With AXI encoding (OKAY=00, EXOKAY=01, SLVERR=10,
        DECERR=11) a bitwise OR is not worst-case:

            SLVERR | EXOKAY = 2'b10 | 2'b01 = 2'b11 = DECERR

        so an exclusive-read beat mixed with a slave error inflates the
        reported class. EXOKAY is reachable: ARLOCK passes through this
        converter. The write side's B fold already uses numeric max; this
        pins the read side to the same semantics (CONV-005).
        """
        if not self.DOWNSIZE:
            return True

        self.log.info("--- RRESP severity fold (projects/components/utility-ip/converters BUG-005, was CONV-005) ---")
        addr = 0x50000
        narrow_bytes = self.M_AXI_DATA_WIDTH // 8
        # sub-beat 0 -> EXOKAY, sub-beat 1 -> SLVERR, rest OKAY
        special = {addr: 1, addr + narrow_bytes: 2}
        self.master_read_slave['interface'].resp_override = \
            lambda a: special.get(a)
        try:
            data = await self.read_transaction(addr, 1)   # one wide beat
        except TimeoutError:
            self.log.error("  RRESP fold: read timed out")
            self.errors += 1
            return False
        finally:
            self.master_read_slave['interface'].resp_override = None

        resps = [pkt['resp'] if isinstance(pkt, dict) else
                 int(getattr(pkt, 'resp', 0)) for pkt in self.captured_r_packets]
        if not resps:
            self.log.error("  RRESP fold: no R beats captured")
            self.errors += 1
            return False
        got = resps[0]
        if got == 2:
            self.log.info("  RRESP fold OK: EXOKAY+SLVERR sub-beats -> "
                          "SLVERR (severity max)")
            return True
        name = {0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}.get(got, hex(got))
        self.log.error(f"  RRESP fold WRONG: EXOKAY+SLVERR sub-beats -> "
                       f"{name} -- bitwise OR inflates the error class")
        self.errors += 1
        return False

    async def run_medium_test(self):
        """
        Medium test - multiple transactions with different patterns.

        Uses unique non-zero data patterns to detect byte/word swapping.

        Includes:
        - Multiple write/read transaction pairs
        - Different burst lengths (1, 2, 4, 8 beats)
        - Sequential and random addresses

        Returns:
            True if all tests pass, False otherwise
        """
        self.log.info("=== Running Medium Test Suite ===")
        if self.UPSIZE:
            self.log.info("=== Scenarios DWIDTH-RD-03,05,06,09,10: Burst upsize, ID/RLAST generation, buffers ===")
        else:
            self.log.info("=== Scenarios DWIDTH-RD-04,05,06,09,10: Burst downsize, ID/RLAST generation, buffers ===")

        all_success = True
        num_transactions = 10
        words_per_beat = self.S_AXI_DATA_WIDTH // 32

        def generate_unique_data(start_value, num_beats):
            """Generate unique data pattern where each 32-bit word is different."""
            data = []
            word_counter = start_value
            for beat in range(num_beats):
                beat_data = 0
                for word_idx in range(words_per_beat):
                    # Each word gets unique replicated byte value
                    byte_value = (word_counter % 255) + 1  # 1-255, avoid 0
                    # Replicate byte across 32-bit word for visual identification
                    word_value = (byte_value << 24) | (byte_value << 16) | (byte_value << 8) | byte_value
                    beat_data |= (word_value << (word_idx * 32))
                    word_counter += 1
                data.append(beat_data)
            return data

        # Test 1: Sequential read transactions (read-only converter)
        self.log.info("--- Test 1: Sequential Read Transactions ---")
        base_addr = 0x1000

        for i in range(num_transactions):
            addr = base_addr + (i * 0x100)
            # For reads, we specify burst length, not data
            burst_len = 2

            # Read and verify on slave side
            self.log.info(f"  Starting transaction {i} at 0x{addr:X}")
            success = await self.do_read_and_verify(addr, burst_len)

            if not success:
                self.log.error(f"  Transaction {i} at 0x{addr:X} FAILED")
                all_success = False
            else:
                self.log.info(f"  Transaction {i} at 0x{addr:X} PASSED")

        # Test 2: Different burst lengths
        self.log.info("--- Test 2: Variable Burst Lengths ---")
        addr = 0x2000
        for burst_len in [1, 2, 4, 8]:
            self.log.info(f"  Testing burst length {burst_len}")
            success = await self.do_read_and_verify(addr, burst_len)

            if not success:
                self.log.error(f"  Burst length {burst_len} test FAILED")
                all_success = False
            else:
                self.log.info(f"  Burst length {burst_len} test PASSED")
            addr += 0x100

        # Test 2b: maximum-length bursts -- see test_max_length_burst
        if not await self.test_max_length_burst():
            all_success = False

        # Test 2c: response severity folding -- see test_rresp_severity_fold
        if not await self.test_rresp_severity_fold():
            all_success = False

        # Test 3: Random addresses and burst lengths
        self.log.info("--- Test 3: Random Address/Burst Length Patterns ---")
        for i in range(5):
            addr = random.randint(0x1000, 0xF000) & 0xFFF0  # Align to 16-byte
            burst_len = random.choice([2, 4])

            self.log.info(f"  Random test {i} at 0x{addr:X}, len={burst_len}")
            success = await self.do_read_and_verify(addr, burst_len)

            if not success:
                self.log.error(f"  Random test at 0x{addr:X} FAILED")
                all_success = False
            else:
                self.log.info(f"  Random test at 0x{addr:X} PASSED")

        if all_success:
            self.log.info("All Medium tests PASSED")
        else:
            self.log.error("Some Medium tests FAILED")

        return all_success

    async def _drive_interleave_r_beats(self, ids, slave_beats_list, addrs, timeout):
        """Drive master R beats round-robin across IDs as their ARs are captured.

        The reservation-based reassembly layer serializes master AR issue per
        ID for downsize, so this helper rebuilds each ID's master beat list
        from the currently captured ARs and drives the next available beat
        every iteration.  Splits of a downsize burst are therefore emitted as
        soon as their AR is captured, unlocking the next split's issue.
        """
        r_ch = self.master_read_slave['R']
        expected_master_beats = {}
        for addr, beats, arid in zip(addrs, slave_beats_list, ids):
            if self.DOWNSIZE:
                expected_master_beats[arid] = beats * self.WIDTH_RATIO
            else:
                lane = (addr % self.M_STRB_WIDTH) // self.S_STRB_WIDTH
                expected_master_beats[arid] = (
                    (lane + beats + self.WIDTH_RATIO - 1) // self.WIDTH_RATIO)

        beats_by_id = {arid: [] for arid in ids}
        next_idx = {arid: 0 for arid in ids}
        waited = 0
        pending = set(ids)

        while pending and waited < timeout:
            any_sent = False
            for arid in ids:
                idx = ids.index(arid)
                m_beats, _ = self._build_interleave_r_beats(
                    addrs[idx], slave_beats_list[idx], arid,
                    self.captured_ar_packets)
                beats_by_id[arid] = m_beats

                if next_idx[arid] < len(beats_by_id[arid]):
                    beat = beats_by_id[arid][next_idx[arid]]
                    pkt = r_ch.create_packet(
                        id=arid,
                        data=beat['data'],
                        resp=0,
                        last=beat['last']
                    )
                    await r_ch.send(pkt)
                    next_idx[arid] += 1
                    any_sent = True

                if next_idx[arid] >= expected_master_beats[arid]:
                    pending.discard(arid)

            if not any_sent:
                await self.wait_clocks(self.aclk_name, 1)
                waited += 1

        if pending:
            self.log.error(
                f"BUG-009 interleave driver: timed out waiting for beats for IDs {pending}")
            self.errors += 1

    async def _collect_r_responses(self, ids, expected_total, timeout):
        """Return per-ID response lists by polling the R-channel callback captures.

        Direct sampling of s_axi_rvalid/rready is fragile here because the GAXI
        consumer deasserts ready shortly after the handshake, so an edge-based
        sampler can miss transfers.  The registered R callback fires exactly once
        per completed beat, so we wait until it has recorded the expected number
        of responses and then group them by ID.
        """
        resp_by_id = {arid: [] for arid in ids}
        waited = 0
        while (len(self.captured_r_packets) < expected_total
               and waited < timeout):
            await RisingEdge(self.aclk)
            if len(self.captured_r_packets) >= expected_total:
                break
            waited += 1

        for pkt in self.captured_r_packets:
            if pkt.id in resp_by_id:
                resp_by_id[pkt.id].append(pkt)
        return resp_by_id

    async def _drive_ooo_r_beats(self, ids, slave_beats_list, addrs, drive_order, timeout):
        """Drive whole master R bursts in drive_order as their ARs are captured.

        For downsize, splits of the same slave burst issue sequentially, so
        beats are emitted incrementally as each split's AR is captured while
        still respecting the per-ID drive_order.
        """
        r_ch = self.master_read_slave['R']
        expected_master_beats = {}
        for addr, beats, arid in zip(addrs, slave_beats_list, ids):
            if self.DOWNSIZE:
                expected_master_beats[arid] = beats * self.WIDTH_RATIO
            else:
                lane = (addr % self.M_STRB_WIDTH) // self.S_STRB_WIDTH
                expected_master_beats[arid] = (
                    (lane + beats + self.WIDTH_RATIO - 1) // self.WIDTH_RATIO)

        for arid in drive_order:
            idx = ids.index(arid)
            next_idx = 0
            waited = 0
            while next_idx < expected_master_beats[arid] and waited < timeout:
                m_beats, _ = self._build_interleave_r_beats(
                    addrs[idx], slave_beats_list[idx], arid,
                    self.captured_ar_packets)

                if next_idx < len(m_beats):
                    beat = m_beats[next_idx]
                    pkt = r_ch.create_packet(
                        id=arid,
                        data=beat['data'],
                        resp=0,
                        last=beat['last']
                    )
                    await r_ch.send(pkt)
                    next_idx += 1
                    waited = 0
                else:
                    await self.wait_clocks(self.aclk_name, 1)
                    waited += 1

            if next_idx < expected_master_beats[arid]:
                self.log.error(
                    f"BUG-009 OOO-R driver: timed out waiting for beats for ID {arid}")
                self.errors += 1
                return

    async def run_interleave_test(self):
        """BUG-009 TDD: beat-level R interleaving across IDs must not corrupt data.

        Two or three ARIDs are issued concurrently.  The master-side slave BFM
        auto-response is disabled; the test drives the returning R beats one at
        a time in round-robin ID order, with RLAST only on each master burst's
        true last beat.  The old RTL feeds the raw interleaved stream into the
        data primitive, so wide beats mix IDs and RID attribution follows the
        most recent beat.  The fixed reassembly layer must deliver every slave
        beat with the correct data, RID, and RLAST.
        """
        self.log.info("=== BUG-009 beat-level R interleave test ===")

        ids = [0, 1, 2]
        if self.DOWNSIZE:
            # ID0 is split-eligible; the others are short single master bursts.
            slave_beats_list = [(256 // self.WIDTH_RATIO) + 1, 2, 2]
        else:
            slave_beats_list = [4, 2, 3]
        addrs = [0x1000, 0x2000, 0x3000]

        self.captured_ar_packets.clear()
        self.captured_r_packets.clear()

        iface = self.master_read_slave['interface']
        saved_response_delay = iface.response_delay_cycles
        ok = True
        try:
            iface.response_delay_cycles = 1000000
            # Consume slave-side R continuously so long bursts don't stall on
            # the default valid-first ready policy.
            self.slave_read_master['R'].set_ready_policy('always')

            # Issue all slave ARs concurrently.
            ar_tasks = []
            for addr, beats, arid in zip(addrs, slave_beats_list, ids):
                ar_tasks.append(cocotb.start_soon(
                    self._issue_ar_burst(addr, beats, arid)))
            for t in ar_tasks:
                await t

            timeout = self.TIMEOUT_CYCLES * 10

            # Drive R beats incrementally as master ARs are captured.  The
            # reservation-based downsize reassembly serializes AR issue per ID,
            # so we cannot wait for all ARs before driving responses.
            driver = cocotb.start_soon(
                self._drive_interleave_r_beats(ids, slave_beats_list, addrs, timeout))

            # Wait until all master AR records are captured.
            expected_ar = 0
            for addr, beats, arid in zip(addrs, slave_beats_list, ids):
                if self.DOWNSIZE:
                    expected_ar += (beats * self.WIDTH_RATIO + 255) // 256
                else:
                    expected_ar += 1
            waited = 0
            while len(self.captured_ar_packets) < expected_ar and waited < timeout:
                await self.wait_clocks(self.aclk_name, 1)
                waited += 1
            if len(self.captured_ar_packets) < expected_ar:
                self.log.error(f"BUG-009 interleave: only {len(self.captured_ar_packets)}/"
                               f"{expected_ar} master ARs captured")
                self.errors += 1
                return False

            # Build expected slave R beats per ID now that all ARs are known.
            expected_by_id = {}
            for addr, beats, arid in zip(addrs, slave_beats_list, ids):
                _, exp = self._build_interleave_r_beats(
                    addr, beats, arid, self.captured_ar_packets)
                expected_by_id[arid] = exp

            # Wait for the driver and all slave R responses.
            expected_total = sum(len(v) for v in expected_by_id.values())
            collector = cocotb.start_soon(
                self._collect_r_responses(ids, expected_total, timeout))
            await driver
            recv_by_id = await collector
            if sum(len(v) for v in recv_by_id.values()) != expected_total:
                self.log.error(f"BUG-009 interleave: expected {expected_total} slave R "
                               f"beats, got {sum(len(v) for v in recv_by_id.values())}")
                self.errors += 1
                ok = False

            for arid in ids:
                exp = expected_by_id[arid]
                got = recv_by_id[arid]
                if len(got) != len(exp):
                    self.log.error(f"BUG-009 interleave: ID {arid} expected {len(exp)} "
                                   f"slave beats, got {len(got)}")
                    self.errors += 1
                    ok = False
                    continue
                for i, (g, e) in enumerate(zip(got, exp)):
                    g_data = int(getattr(g, 'data', 0))
                    g_last = int(getattr(g, 'last', 0))
                    if g_data != e['data'] or g_last != e['last']:
                        self.log.error(
                            f"BUG-009 interleave: ID {arid} beat {i} mismatch "
                            f"data=0x{g_data:X}/0x{e['data']:X} last={g_last}/{e['last']}")
                        self.errors += 1
                        ok = False

            if ok:
                self.log.info("BUG-009 beat-level interleave test PASSED")
            else:
                self.log.error("BUG-009 beat-level interleave test FAILED")
            return ok
        finally:
            iface.response_delay_cycles = saved_response_delay

    async def run_ooo_r_burst_test(self):
        """BUG-009 follow-up: whole master R bursts completing out of order across IDs.

        The reassembly layer feeds one burst at a time to the primitive, so
        completing ID1's entire burst before ID0's must still produce correct
        per-ID data and RID on the slave side.
        """
        self.log.info("=== BUG-009 burst-atomic OOO R test ===")

        ids = [0, 1]
        if self.DOWNSIZE:
            slave_beats_list = [2, (256 // self.WIDTH_RATIO) + 1]
        else:
            slave_beats_list = [2, 4]
        addrs = [0x4000, 0x5000]
        # Drive the shorter ID first, then the longer ID (opposite of issue order).
        drive_order = [1, 0]

        self.captured_ar_packets.clear()
        self.captured_r_packets.clear()

        iface = self.master_read_slave['interface']
        saved_response_delay = iface.response_delay_cycles
        ok = True
        try:
            iface.response_delay_cycles = 1000000
            # Consume slave-side R continuously so long bursts don't stall on
            # the default valid-first ready policy.
            self.slave_read_master['R'].set_ready_policy('always')

            ar_tasks = []
            for addr, beats, arid in zip(addrs, slave_beats_list, ids):
                ar_tasks.append(cocotb.start_soon(
                    self._issue_ar_burst(addr, beats, arid)))
            for t in ar_tasks:
                await t

            timeout = self.TIMEOUT_CYCLES * 10

            # Drive whole bursts in drive_order as each ID's ARs are captured.
            driver = cocotb.start_soon(
                self._drive_ooo_r_beats(ids, slave_beats_list, addrs, drive_order, timeout))

            # Wait until all master AR records are captured.
            expected_ar = 0
            for addr, beats, arid in zip(addrs, slave_beats_list, ids):
                if self.DOWNSIZE:
                    expected_ar += (beats * self.WIDTH_RATIO + 255) // 256
                else:
                    expected_ar += 1
            waited = 0
            while len(self.captured_ar_packets) < expected_ar and waited < timeout:
                await self.wait_clocks(self.aclk_name, 1)
                waited += 1
            if len(self.captured_ar_packets) < expected_ar:
                self.log.error(f"BUG-009 OOO-R: only {len(self.captured_ar_packets)}/"
                               f"{expected_ar} master ARs captured")
                self.errors += 1
                return False

            # Build expected slave R beats per ID now that all ARs are known.
            expected_by_id = {}
            for addr, beats, arid in zip(addrs, slave_beats_list, ids):
                _, exp = self._build_interleave_r_beats(
                    addr, beats, arid, self.captured_ar_packets)
                expected_by_id[arid] = exp

            # Wait for the driver and all slave R responses.
            expected_total = sum(len(v) for v in expected_by_id.values())
            collector = cocotb.start_soon(
                self._collect_r_responses(ids, expected_total, timeout))
            await driver
            recv_by_id = await collector
            if sum(len(v) for v in recv_by_id.values()) != expected_total:
                self.log.error(f"BUG-009 OOO-R: expected {expected_total} slave R "
                               f"beats, got {sum(len(v) for v in recv_by_id.values())}")
                self.errors += 1
                ok = False

            for arid in ids:
                exp = expected_by_id[arid]
                got = recv_by_id[arid]
                if len(got) != len(exp):
                    self.log.error(f"BUG-009 OOO-R: ID {arid} expected {len(exp)} "
                                   f"slave beats, got {len(got)}")
                    self.errors += 1
                    ok = False
                    continue
                for i, (g, e) in enumerate(zip(got, exp)):
                    g_data = int(getattr(g, 'data', 0))
                    g_last = int(getattr(g, 'last', 0))
                    if g_data != e['data'] or g_last != e['last']:
                        self.log.error(
                            f"BUG-009 OOO-R: ID {arid} beat {i} mismatch "
                            f"data=0x{g_data:X}/0x{e['data']:X} last={g_last}/{e['last']}")
                        self.errors += 1
                        ok = False

            if ok:
                self.log.info("BUG-009 burst-atomic OOO R test PASSED")
            else:
                self.log.error("BUG-009 burst-atomic OOO R test FAILED")
            return ok
        finally:
            iface.response_delay_cycles = saved_response_delay

    async def run_full_test(self):
        """
        Full test suite - comprehensive coverage.

        Includes:
        - All medium test scenarios
        - Longer bursts (16, 32 beats)
        - Stress testing with many transactions
        - Mixed read/write patterns
        - Address boundary conditions

        Returns:
            True if all tests pass, False otherwise
        """
        self.log.info("=== Running Full Test Suite ===")
        self.log.info("=== Scenarios DWIDTH-RD-07,08,11,12,13,14,15: RRESP/backpressure/burst/addr/reset/data ===")

        all_success = True

        # Test 1: Run medium tests first
        self.log.info("--- Test 1: Medium Test Suite (baseline) ---")
        if not await self.run_medium_test():
            all_success = False

        # Test 2: Long bursts
        self.log.info("--- Test 2: Long Burst Transactions ---")
        addr = 0x10000
        for burst_len in [16, 32]:
            self.log.info(f"  Testing {burst_len}-beat burst at 0x{addr:X}")
            success = await self.do_read_and_verify(addr, burst_len)

            if not success:
                self.log.error(f"  Long burst test ({burst_len} beats) FAILED")
                all_success = False
            else:
                self.log.info(f"  Long burst test ({burst_len} beats) PASSED")
            addr += 0x1000

        # Test 3: Stress test with many read transactions
        num_stress_txns = 20  # Reduced to make debug tractable
        self.log.info(f"--- Test 3: Stress Test ({num_stress_txns} read transactions) ---")

        # CRITICAL: Clear BFM state before stress test to prevent orphaned data from previous tests
        await self.clear_bfm_state()

        base_addr = 0x20000
        failed = 0
        failed_txns = []

        for i in range(num_stress_txns):
            addr = base_addr + (i * 0x80)
            burst_len = random.randint(2, 8)

            # Enable debug to see what's happening
            debug = True
            success = await self.do_read_and_verify(addr, burst_len, debug=debug)
            if not success:
                failed += 1
                failed_txns.append((i, burst_len, addr))
                self.log.error(f"  Transaction #{i} FAILED: {burst_len} beats at 0x{addr:08X}")

            # Delay between transactions to ensure complete packet capture
            # and let skid buffers drain
            await self.wait_clocks(self.aclk_name, 50)

            if i % 10 == 0:
                self.log.info(f"  Progress: {i}/{num_stress_txns} transactions")

        if failed > 0:
            self.log.error(f"  Stress test: {failed}/{num_stress_txns} transactions FAILED")
            self.log.error(f"     Failed transactions: {failed_txns}")
            self.errors += failed
            all_success = False
        else:
            self.log.info(f"  Stress test: All {num_stress_txns} transactions PASSED")

        # Test 4: Multiple reads from same address
        self.log.info("--- Test 4: Sequential Reads from Same Address ---")
        addr = 0x40000
        burst_len = 4
        # First read
        success = await self.do_read_and_verify(addr, burst_len)

        if not success:
            self.log.error(f"  Initial read FAILED")
            all_success = False

        # Second read from same address
        success = await self.do_read_and_verify(addr, burst_len)

        if not success:
            self.log.error(f"  Second read FAILED")
            all_success = False
        else:
            self.log.info(f"  Sequential reads from same address PASSED")

        # Test 5: Address boundary conditions
        self.log.info("--- Test 5: Address Boundary Conditions ---")
        boundary_addrs = [
            0x0000,      # Start of memory
            0xFFF0,      # Near 4KB boundary
            0x10000,     # 64KB boundary
            0xFFFF0,     # Near 1MB boundary
        ]

        for addr in boundary_addrs:
            burst_len = 4
            success = await self.do_read_and_verify(addr, burst_len)

            if not success:
                self.log.error(f"  Boundary test at 0x{addr:X} FAILED")
                all_success = False
            else:
                self.log.info(f"  Boundary test at 0x{addr:X} PASSED")

        # Final result
        if all_success:
            self.log.info("All Full tests PASSED")
        else:
            self.log.error("Some Full tests FAILED")

        return all_success

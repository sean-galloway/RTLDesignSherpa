# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: axi4_to_axil4_wr_tb
# Purpose: Testbench class for axi4_to_axil4_wr converter (WRITE-ONLY)
#
# Author: RTL Design Sherpa
# Created: 2025-11-05

"""
Testbench for axi4_to_axil4_wr converter - WRITE-ONLY

Tests AXI4 → AXI4-Lite protocol downgrade for write path with burst decomposition:
- Multi-beat AXI4 AW/W bursts decomposed into multiple single-beat AXIL4 writes
- Address incrementing for INCR bursts
- FIXED burst support (same address)
- Response aggregation (worst-case)
- ID preservation through burst

Architecture:
- AXI4MasterWrite drives slave side (sends AW/W bursts, receives B responses)
- AXIL4 responder on master side (responds to single-beat AXIL4 writes)
- Monitor AXIL4 master outputs for burst decomposition validation
"""

import os
import sys
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.clock import Clock
import random

# Import framework utilities (PYTHONPATH includes bin/)
from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterWrite
from CocoTBFramework.components.axil4.axil4_interfaces import AXIL4SlaveWrite


class AXI4ToAXIL4WriteTB(TBBase):
    """
    Testbench for axi4_to_axil4_wr converter.

    Tests protocol downgrade from AXI4 → AXI4-Lite for write path with burst decomposition.

    Key Validations:
    - Burst decomposition (multi-beat → multiple single-beat)
    - Address incrementing (INCR burst type)
    - FIXED burst support (same address)
    - Response aggregation (worst-case error)
    - ID preservation through burst
    """

    def __init__(self, dut):
        super().__init__(dut)

        # Clock and reset
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        # Extract parameters from DUT or environment
        self.data_width = self.convert_to_int(os.environ.get('AXI_DATA_WIDTH', '32'))
        self.addr_width = self.convert_to_int(os.environ.get('AXI_ADDR_WIDTH', '32'))
        self.id_width = self.convert_to_int(os.environ.get('AXI_ID_WIDTH', '8'))

        # Statistics
        self.stats = {
            'bursts_sent': 0,
            'beats_expected': 0,
            'axil_writes_received': 0,
            'bursts_completed': 0,
            'errors': 0,
            'address_errors': 0,
            'decomposition_errors': 0,
            'data_errors': 0,
        }

        # Bytes per transfer
        self.bytes_per_beat = self.data_width // 8

        # Initialize AXI4 master (drives slave side of converter)
        self.axi4_master = AXI4MasterWrite(
            dut=dut,
            clock=self.clk,
            prefix="s_axi_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True
        )

        # Initialize AXIL4 slave (responds on master side of converter)
        self.axil4_slave = AXIL4SlaveWrite(
            dut=dut,
            clock=self.clk,
            prefix="m_axil_",
            log=self.log,
            data_width=self.data_width,
            addr_width=self.addr_width,
            multi_sig=True,
            response_delay=1
        )

        # Storage for monitoring AXIL4 transactions (track from slave BFM queues)
        self.axil_transactions = []  # (type, addr, data, strb)

        self.log.info(f"Initialized AXI4→AXIL4 Write TB: "
                     f"data_width={self.data_width}, "
                     f"addr_width={self.addr_width}, "
                     f"id_width={self.id_width}")

    # =========================================================================
    # MANDATORY METHODS - Required by TBBase
    # =========================================================================

    async def setup_clocks_and_reset(self, period_ns=10):
        """Complete initialization - start clocks and perform reset"""
        # Start clock
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')

        # BFM handles awready, wready, bvalid automatically - don't override!

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

        self.log.info("Reset sequence complete")

    async def assert_reset(self):
        """Assert reset signal (active-low)"""
        self.rst_n.value = 0
        self.log.debug("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset signal (active-low)"""
        self.rst_n.value = 1
        self.log.debug("Reset deasserted")

    # =========================================================================
    # AXIL4 MASTER SIDE TRANSACTION MONITOR
    # =========================================================================

    async def axil4_transaction_monitor(self):
        """
        Monitor AXIL4 write transactions by watching handshakes.

        Since the BFM processes transactions immediately, we monitor the
        actual AXIL protocol handshakes on the DUT signals. For writes,
        we track both AW and W handshakes and match them up.

        Note: this monitor assumes AW + W handshakes are paired within a
        small window (the AXIL slave BFM enforces this). For pipelined
        b2b cases with many AWs outstanding, beat counts/data may be off —
        treat any monitor-side mismatch as a SIGNAL that the b2b scenario
        triggered timing where AW and W desynchronize on the wire, which
        is the page-probe class of bug we want to surface.
        """
        self.log.info("Starting AXIL4 transaction monitor")

        # Track pending addresses
        pending_addr = None

        while True:
            await RisingEdge(self.clk)

            # Monitor AW channel handshakes
            if (int(self.dut.m_axil_awvalid.value) == 1 and
                int(self.dut.m_axil_awready.value) == 1):
                pending_addr = int(self.dut.m_axil_awaddr.value)
                self.log.debug(f"AXIL4 AW handshake: addr=0x{pending_addr:08X}")

            # Monitor W channel handshakes
            if (int(self.dut.m_axil_wvalid.value) == 1 and
                int(self.dut.m_axil_wready.value) == 1):
                w_data = int(self.dut.m_axil_wdata.value)
                w_strb = int(self.dut.m_axil_wstrb.value)

                # Match with pending address
                if pending_addr is not None:
                    self.axil_transactions.append(('W', pending_addr, w_data, w_strb))
                    self.stats['axil_writes_received'] += 1
                    self.log.debug(f"AXIL4 Write complete: addr=0x{pending_addr:08X}, data=0x{w_data:08X}")
                    pending_addr = None

    # =========================================================================
    # TEST SCENARIO METHODS
    # =========================================================================

    async def test_write_burst(self, address, data_list, burst_type=1, size=None):
        """
        Test AXI4 write burst through converter.

        Args:
            address: Starting write address
            data_list: List of write data values
            burst_type: 0=FIXED, 1=INCR, 2=WRAP
            size: AWSIZE value (None = full width)

        Returns:
            True if test passed, False otherwise
        """
        if size is None:
            size = (self.data_width // 8).bit_length() - 1

        burst_len = len(data_list)

        # Calculate address increment
        addr_incr = 1 << size

        self.log.debug(f"Testing write burst: addr=0x{address:08X}, len={burst_len}, "
                      f"burst_type={burst_type}, size={size}")

        # Clear AXIL transaction log
        initial_axil_count = len(self.axil_transactions)

        # Send AXI4 write burst
        try:
            await self.axi4_master.write_transaction(
                address=address,
                data=data_list,
                size=size,
                burst_type=burst_type
            )

            # Wait for all AXIL transactions to complete
            await self.wait_clocks(self.clk_name, 20)

            # Verify number of AXIL4 writes
            axil_writes = len(self.axil_transactions) - initial_axil_count

            if axil_writes != burst_len:
                self.log.error(f"Burst decomposition FAILED: got {axil_writes} AXIL writes, "
                             f"expected {burst_len}")
                self.stats['decomposition_errors'] += 1
                self.stats['errors'] += 1
                return False

            # Verify addresses and data (for INCR bursts)
            if burst_type == 1:  # INCR
                expected_addr = address
                for i in range(axil_writes):
                    txn_type, txn_addr, txn_data, txn_strb = self.axil_transactions[initial_axil_count + i]

                    if txn_addr != expected_addr:
                        self.log.error(f"Address increment FAILED: beat {i}, "
                                     f"got 0x{txn_addr:08X}, expected 0x{expected_addr:08X}")
                        self.stats['address_errors'] += 1
                        self.stats['errors'] += 1
                        return False

                    if txn_data != data_list[i]:
                        self.log.error(f"Data mismatch: beat {i}, "
                                     f"got 0x{txn_data:08X}, expected 0x{data_list[i]:08X}")
                        self.stats['data_errors'] += 1
                        self.stats['errors'] += 1
                        return False

                    expected_addr += addr_incr

            elif burst_type == 0:  # FIXED
                # All beats should have same address
                for i in range(axil_writes):
                    txn_type, txn_addr, txn_data, txn_strb = self.axil_transactions[initial_axil_count + i]

                    if txn_addr != address:
                        self.log.error(f"FIXED burst FAILED: beat {i}, "
                                     f"got 0x{txn_addr:08X}, expected 0x{address:08X}")
                        self.stats['address_errors'] += 1
                        self.stats['errors'] += 1
                        return False

                    if txn_data != data_list[i]:
                        self.log.error(f"Data mismatch: beat {i}, "
                                     f"got 0x{txn_data:08X}, expected 0x{data_list[i]:08X}")
                        self.stats['data_errors'] += 1
                        self.stats['errors'] += 1
                        return False

            self.log.debug(f"Burst test PASSED: {burst_len} beats decomposed correctly")
            self.stats['bursts_sent'] += 1
            self.stats['beats_expected'] += burst_len
            self.stats['bursts_completed'] += 1
            return True

        except Exception as e:
            self.log.error(f"Write burst transaction failed: {e}")
            self.stats['errors'] += 1
            return False

    async def test_b2b_bursts(self, bursts, size=None):
        """
        Issue N write bursts back-to-back with NO test-level cooldown.

        Each burst is launched via cocotb.start_soon so the AXI4 master BFM
        queues them and the AW/W beats can flow on the wire as fast as the
        bridge accepts. We then await each task in issue order.

        Args:
            bursts: List of (address, data_list) tuples to issue back-to-back.
                    All bursts use INCR (burst_type=1).
            size: AWSIZE for every burst (None = full data width).

        Returns:
            True if total beats and per-burst (addr, data, strb) tuples match
            the expected issue order.
        """
        if size is None:
            size = (self.data_width // 8).bit_length() - 1
        addr_incr = 1 << size

        # Build the expected AXIL beat sequence in issue order
        expected = []  # list of (addr, data, strb)
        strb_width = self.data_width // 8
        default_strb = (1 << strb_width) - 1
        for (start_addr, data_list) in bursts:
            addr = start_addr
            for data in data_list:
                expected.append((addr, data, default_strb))
                addr += addr_incr

        total_expected_beats = len(expected)
        initial_axil_count = len(self.axil_transactions)

        self.log.info(f"B2B WRITE BURSTS: issuing {len(bursts)} bursts "
                      f"({total_expected_beats} total beats) with NO inter-burst cooldown")

        # Launch all bursts as concurrent tasks (no awaits between launches)
        tasks = []
        for (start_addr, data_list) in bursts:
            task = cocotb.start_soon(self.axi4_master.write_transaction(
                address=start_addr,
                data=data_list,
                size=size,
                burst_type=1,  # INCR
            ))
            tasks.append(task)

        # Wait for every burst's B response to come back, in issue order
        for i, task in enumerate(tasks):
            await task

        # Drain remaining AXIL beats (do NOT wait between bursts above —
        # only here, at the end, to let the last B propagate).
        await self.wait_clocks(self.clk_name, 50)

        # Verify total beat count
        actual_beats = len(self.axil_transactions) - initial_axil_count
        if actual_beats != total_expected_beats:
            self.log.error(f"B2B beat count MISMATCH: got {actual_beats}, "
                          f"expected {total_expected_beats}")
            self.stats['decomposition_errors'] += 1
            self.stats['errors'] += 1
            return False

        # Verify the AXIL beat sequence matches the expected tuples in order
        for i, (exp_addr, exp_data, exp_strb) in enumerate(expected):
            _, got_addr, got_data, got_strb = self.axil_transactions[initial_axil_count + i]
            if got_addr != exp_addr:
                self.log.error(f"B2B addr MISMATCH at beat {i}: "
                              f"got 0x{got_addr:08X}, expected 0x{exp_addr:08X}")
                self.stats['address_errors'] += 1
                self.stats['errors'] += 1
                return False
            if got_data != exp_data:
                self.log.error(f"B2B data MISMATCH at beat {i} (addr=0x{exp_addr:08X}): "
                              f"got 0x{got_data:08X}, expected 0x{exp_data:08X}")
                self.stats['data_errors'] += 1
                self.stats['errors'] += 1
                return False

        self.log.info(f"B2B WRITE BURSTS PASSED: {len(bursts)} bursts, "
                      f"{total_expected_beats} beats verified in issue order")
        self.stats['bursts_sent'] += len(bursts)
        self.stats['beats_expected'] += total_expected_beats
        self.stats['bursts_completed'] += len(bursts)
        return True

    async def test_b2b_mixed_lengths(self):
        """
        B2B bursts with interleaved lengths to exercise WR_IDLE↔WR_BURST↔WR_LAST_BEAT
        transitions in adjacent cycles.
        """
        bursts = []
        base = 0x10000
        lengths = [1, 4, 1, 2, 8, 1, 16, 1]
        for i, blen in enumerate(lengths):
            addr = base + (i * 0x1000)
            data_list = [((0xA000_0000 | (i << 16) | j) & ((1 << self.data_width) - 1))
                         for j in range(blen)]
            bursts.append((addr, data_list))
        return await self.test_b2b_bursts(bursts)

    async def test_partial_strobe(self):
        """
        Single-beat and 2-beat bursts with non-trivial wstrb patterns.
        Verifies wstrb propagates correctly through to AXIL.

        Note: This scenario is most meaningful at 32b. For wider buses we
        still exercise low-byte strobe patterns to confirm pass-through.
        """
        strb_width = self.data_width // 8
        # Build strobe patterns: for 32b → 0x3, 0xC, 0x5, 0xA, 0xF
        # For wider, just use the low nibble pattern in the bottom of the bus.
        patterns = [0x3, 0xC, 0x5, 0xA, (1 << strb_width) - 1]
        success = True

        for i, base_strb in enumerate(patterns):
            # Mask to legal strb width
            strb = base_strb & ((1 << strb_width) - 1)
            if strb == 0:
                continue  # skip degenerate

            addr = 0x20000 + (i * 0x100)
            data = 0xCAFE0000 | (i & 0xFF)
            data &= (1 << self.data_width) - 1

            initial_axil_count = len(self.axil_transactions)

            self.log.debug(f"Partial strobe: addr=0x{addr:08X} data=0x{data:08X} strb=0x{strb:0X}")

            try:
                await self.axi4_master.write_transaction(
                    address=addr,
                    data=[data, data ^ 0xFFFFFFFF],  # 2-beat
                    strb=strb,
                )
                await self.wait_clocks(self.clk_name, 20)

                got = self.axil_transactions[initial_axil_count:]
                if len(got) != 2:
                    self.log.error(f"Partial strobe: got {len(got)} beats, expected 2")
                    self.stats['errors'] += 1
                    success = False
                    continue

                for beat_idx, (_, _, _, got_strb) in enumerate(got):
                    if got_strb != strb:
                        self.log.error(f"Partial strobe MISMATCH beat {beat_idx}: "
                                      f"got 0x{got_strb:0X}, expected 0x{strb:0X}")
                        self.stats['errors'] += 1
                        success = False
            except Exception as e:
                self.log.error(f"Partial strobe burst raised: {e}")
                self.stats['errors'] += 1
                success = False

        return success

    async def test_narrow_within_wide(self):
        """
        Bursts with awsize < full data width on a wider bus.
        E.g. size=2 (4 bytes) on a 64b/128b DUT. Verifies the shim handles
        narrow transfers within a wider bus correctly (address increment
        matches the narrower size).
        """
        if self.data_width <= 32:
            self.log.info("test_narrow_within_wide: data_width<=32, skipping (no narrower size available)")
            return True

        success = True
        # Pick a size smaller than full width: log2(data_width/8) - 1
        full_size = (self.data_width // 8).bit_length() - 1
        narrow_size = full_size - 1  # one step narrower

        bursts = [
            (0x30000, [0x1111_2222 & ((1 << self.data_width) - 1)] * 1),
            (0x30100, [(0x3333_4444 + i) & ((1 << self.data_width) - 1) for i in range(4)]),
            (0x30200, [(0x5555_6666 + i) & ((1 << self.data_width) - 1) for i in range(8)]),
        ]

        for addr, data_list in bursts:
            initial_axil_count = len(self.axil_transactions)
            try:
                await self.axi4_master.write_transaction(
                    address=addr,
                    data=data_list,
                    size=narrow_size,
                    burst_type=1,
                )
                await self.wait_clocks(self.clk_name, 20)

                got = self.axil_transactions[initial_axil_count:]
                if len(got) != len(data_list):
                    self.log.error(f"narrow_within_wide: got {len(got)} beats, "
                                  f"expected {len(data_list)}")
                    self.stats['errors'] += 1
                    success = False
                    continue

                # Verify address increment matches the narrower size
                expected_addr = addr
                addr_incr = 1 << narrow_size
                for i, (_, got_addr, _, _) in enumerate(got):
                    if got_addr != expected_addr:
                        self.log.error(f"narrow_within_wide addr beat {i}: "
                                      f"got 0x{got_addr:08X}, expected 0x{expected_addr:08X}")
                        self.stats['address_errors'] += 1
                        self.stats['errors'] += 1
                        success = False
                    expected_addr += addr_incr
            except Exception as e:
                self.log.error(f"narrow_within_wide burst raised: {e}")
                self.stats['errors'] += 1
                success = False

        return success

    async def test_max_burst(self):
        """
        AWLEN = 255 (256-beat burst). The medium test caps at 16, full at 32;
        neither hits the AXI4 maximum. This scenario exercises the full burst
        counter range in the shim.
        """
        burst_len = 256
        addr = 0x40000
        data_list = [(0xBEEF_0000 + i) & ((1 << self.data_width) - 1)
                     for i in range(burst_len)]
        return await self.test_write_burst(addr, data_list, burst_type=1)


    async def test_error_response(self, address, beats=1, last_only=False,
                                  label=""):
        """A non-OKAY B response from the AXIL4 slave must reach the master.

        A write burst becomes N single AXIL4 writes, each with its own B,
        which the converter folds into the ONE B response AXI expects. The
        fold is registered but `s_axi_bresp` is read on the same handshake
        that emits it, so the FINAL beat's own response is never folded in.

        Two shapes, because they fail differently:

        * every beat errors -- an early beat is already in the accumulator,
          so only a single-beat write (where the only beat is the final one)
          loses it;
        * only the LAST beat errors -- nothing else was ever accumulated, so
          the error is lost at any burst length.

        `write_transaction` catches its own error and RETURNS
        {'success': False, ...}; it does not propagate. Passing means
        success is False with SLVERR named.
        """
        tag = f"[{label}] " if label else ""
        size = (self.data_width // 8).bit_length() - 1
        last_addr = address + (beats - 1) * (1 << size)
        if last_only:
            self.axil4_slave.resp_override = lambda a: 2 if a == last_addr else None
        else:
            self.axil4_slave.resp_override = lambda a: 2
        data_list = [0xA5A50000 + i for i in range(beats)]
        try:
            result = await self.axi4_master.write_transaction(
                address=address, data=data_list, size=size, burst_type=1)
            err = (result or {}).get('error', '') or ''
            if not (result or {}).get('success', True) and 'SLVERR' in err:
                self.log.info(f"@ {get_sim_time('ns')}ns: {tag}beats={beats}: "
                              f"SLVERR propagated correctly")
                return True
            self.log.error(
                f"@ {get_sim_time('ns')}ns: {tag}beats={beats}: SLVERR from the "
                f"AXIL4 slave was reported to the AXI master as OKAY -- the "
                f"error was silently dropped (result={result})")
            self.stats['errors'] += 1
            return False
        except Exception as exc:
            self.log.error(f"@ {get_sim_time('ns')}ns: {tag}beats={beats}: "
                           f"unexpected failure: {exc!r}")
            self.stats['errors'] += 1
            return False
        finally:
            # Isolate: stop forcing errors, let any tail land, drop it, reset.
            self.axil4_slave.resp_override = None
            await self.wait_clocks(self.clk_name, 40)
            for q in getattr(self.axi4_master, '_response_by_id', {}).values():
                q.clear()
            await self.assert_reset()
            await self.wait_clocks(self.clk_name, 5)
            await self.deassert_reset()
            await self.wait_clocks(self.clk_name, 5)

    async def test_error_responses(self):
        """Error propagation across burst lengths and error placement."""
        ok = True
        for beats in (1, 2, 4):
            if not await self.test_error_response(0xB000 + beats * 0x100,
                                                  beats=beats,
                                                  label=f"{beats}beat-all"):
                ok = False
        for beats in (2, 4):
            if not await self.test_error_response(0xC000 + beats * 0x100,
                                                  beats=beats, last_only=True,
                                                  label=f"{beats}beat-last-only"):
                ok = False
        return ok


    async def test_pipelined_aw_identity(self, label=""):
        """Two single-beat writes accepted back-to-back keep their own IDs.

        The write path mirrors the read path: r_b_id / r_b_len /
        r_b_beat_count are a SINGLE-entry record of the burst in flight, and
        `s_axi_awready = !r_aw_active && ...` never sets r_aw_active for
        awlen==0. A second single-beat AW can therefore be accepted while the
        first write's B is still outstanding, overwriting the identity of the
        write already in flight.

        Driven on the AW/W channels directly, not via two overlapping
        `write_transaction` calls -- pipelining BFM traffic with parallel
        tasks races on its own account, and the DUT is what is under test.
        """
        tag = f"[{label}] " if label else ""
        saved_delay = self.axil4_slave.response_delay_cycles
        self.axil4_slave.response_delay_cycles = 8
        size = (self.data_width // 8).bit_length() - 1
        strb = (1 << (self.data_width // 8)) - 1
        ids = (3, 5)
        addrs = (0xF000, 0xF100)

        for q in getattr(self.axi4_master, '_response_by_id', {}).values():
            q.clear()

        try:
            for axid, addr in zip(ids, addrs):
                aw = self.axi4_master.aw_channel.create_packet(
                    addr=addr, len=0, id=axid, size=size, burst=1,
                    lock=0, cache=0, prot=0, qos=0, region=0)
                await self.axi4_master.aw_channel.send(aw)
                w = self.axi4_master.w_channel.create_packet(
                    data=0xC0DE0000 + axid, last=1, strb=strb)
                await self.axi4_master.w_channel.send(w)

            await self.wait_clocks(self.clk_name, 120)

            ok = True
            for axid in ids:
                q = self.axi4_master._response_by_id.get(axid)
                got = len(q) if q else 0
                if got != 1:
                    self.log.error(
                        f"@ {get_sim_time('ns')}ns: {tag}id={axid}: expected 1 "
                        f"B response, got {got} -- the in-flight write's "
                        f"identity was overwritten by the next AW")
                    self.stats['errors'] += 1
                    ok = False
            if ok:
                self.log.info(f"@ {get_sim_time('ns')}ns: {tag}pipelined AWs "
                              f"kept their IDs")
            return ok
        finally:
            self.axil4_slave.response_delay_cycles = saved_delay
            await self.wait_clocks(self.clk_name, 40)
            for q in getattr(self.axi4_master, '_response_by_id', {}).values():
                q.clear()
            await self.assert_reset()
            await self.wait_clocks(self.clk_name, 5)
            await self.deassert_reset()
            await self.wait_clocks(self.clk_name, 5)


    async def test_pending_w_blocked_by_waiting_burst_aw(self, label=""):
        """A waiting burst AW must not block the outstanding write's W beat.

        Sequence: a single-beat AW is accepted (its W deliberately late),
        then a BURST AW (awlen>0) is presented and parks on the wire --
        the one-outstanding guard holds awready low. `w_burst_capture`
        gated only on `s_axi_awvalid && awlen>0`, so the PARKED burst AW
        blocked the W path of the write already in flight: W never
        forwarded, B never generated, outstanding never cleared, the
        parked AW never accepted -- permanent deadlock. The gate needs
        the `s_axi_awready` qualifier (capture only happens on the accept
        cycle).

        Found by the DV bridge parallel_storm: multi-master arbitration
        presents the next master's burst AW while the previous master's
        single-beat W is still crossing the fabric. A lone BFM serializes
        AW+W, which is why the FUB tests never hit this window.

        Driven on the raw AW/W channels (a write_transaction call
        serializes AW+W and cannot park a second AW).
        """
        tag = f"[{label}] " if label else ""
        size = (self.data_width // 8).bit_length() - 1
        strb = (1 << (self.data_width // 8)) - 1
        ok = True

        for q in getattr(self.axi4_master, '_response_by_id', {}).values():
            q.clear()

        t_aw2 = None
        t_w1 = None
        try:
            # Single-beat AW, id=3 -- accepted via passthrough.
            aw1 = self.axi4_master.aw_channel.create_packet(
                addr=0xE000, len=0, id=3, size=size, burst=1,
                lock=0, cache=0, prot=0, qos=0, region=0)
            await self.axi4_master.aw_channel.send(aw1)

            # W deliberately late.
            await self.wait_clocks(self.clk_name, 6)

            # Burst AW, id=5 -- parks on the wire (outstanding guard).
            aw2 = self.axi4_master.aw_channel.create_packet(
                addr=0xE100, len=3, id=5, size=size, burst=1,
                lock=0, cache=0, prot=0, qos=0, region=0)
            t_aw2 = cocotb.start_soon(self.axi4_master.aw_channel.send(aw2))
            await self.wait_clocks(self.clk_name, 4)

            # Now the late W for the single-beat write.
            w1 = self.axi4_master.w_channel.create_packet(
                data=0xC0DE0003, last=1, strb=strb)
            t_w1 = cocotb.start_soon(self.axi4_master.w_channel.send(w1))
            await self.wait_clocks(self.clk_name, 60)

            got = len(self.axi4_master._response_by_id.get(3) or ())
            if got != 1:
                self.log.error(
                    f"@ {get_sim_time('ns')}ns: {tag}single-beat write id=3 "
                    f"got {got} B responses -- its W beat was blocked by the "
                    f"PARKED burst AW (w_burst_capture missing the awready "
                    f"qualifier)")
                self.stats['errors'] += 1
                ok = False
            else:
                # Drain the burst so the DUT isn't left mid-transaction:
                # its AW should now have been accepted; feed its 4 beats.
                for i in range(4):
                    w = self.axi4_master.w_channel.create_packet(
                        data=0xC0DE0500 + i, last=1 if i == 3 else 0,
                        strb=strb)
                    await self.axi4_master.w_channel.send(w)
                await self.wait_clocks(self.clk_name, 40)
                got5 = len(self.axi4_master._response_by_id.get(5) or ())
                if got5 != 1:
                    self.log.error(
                        f"@ {get_sim_time('ns')}ns: {tag}burst id=5 got "
                        f"{got5} B responses after unblocking")
                    self.stats['errors'] += 1
                    ok = False
            if ok:
                self.log.info(f"@ {get_sim_time('ns')}ns: {tag}pending W "
                              f"completed despite a waiting burst AW")
            return ok
        finally:
            for t in (t_aw2, t_w1):
                if t is not None and not t.done():
                    t.kill()
            for q in getattr(self.axi4_master, '_response_by_id', {}).values():
                q.clear()
            await self.assert_reset()
            await self.wait_clocks(self.clk_name, 5)
            await self.deassert_reset()
            await self.wait_clocks(self.clk_name, 5)

    async def test_wrap_burst(self, address, beats, label=""):
        """A WRAP write must wrap inside its aligned window.

        Same defect as the read path: the RTL advances the address for every
        burst type except FIXED, so WRAP is written as INCR and the beats
        that should fold back run past the window. WRAP is never exercised
        elsewhere -- the random burst-type picks are FIXED or INCR only.
        """
        tag = f"[{label}] " if label else ""
        size = (self.data_width // 8).bit_length() - 1
        incr = 1 << size
        window = beats * incr
        base = address & ~(window - 1)

        expected, addr = [], address
        for _ in range(beats):
            expected.append(addr)
            addr = base | ((addr + incr) & (window - 1))

        start = len(self.axil_transactions)
        data_list = [0x5A5A0000 + i for i in range(beats)]
        try:
            await self.axi4_master.write_transaction(
                address=address, data=data_list, size=size, burst_type=2)
        except Exception as exc:
            self.log.error(f"@ {get_sim_time('ns')}ns: {tag}WRAP write raised: "
                           f"{exc!r}")
            self.stats['errors'] += 1
            return False
        await self.wait_clocks(self.clk_name, 20)

        got = [a for _, a, _, _ in self.axil_transactions[start:]]
        if got == expected:
            self.log.info(f"@ {get_sim_time('ns')}ns: {tag}WRAP beats={beats} "
                          f"wrapped correctly: "
                          f"{' '.join(f'0x{a:X}' for a in got)}")
            return True
        self.log.error(
            f"@ {get_sim_time('ns')}ns: {tag}WRAP beats={beats} from "
            f"0x{address:X} (window 0x{base:X}..0x{base + window - 1:X}): "
            f"expected {' '.join(f'0x{a:X}' for a in expected)}, "
            f"got {' '.join(f'0x{a:X}' for a in got)} -- the burst ran past "
            f"the window instead of wrapping")
        self.stats['errors'] += 1
        return False

    async def test_wrap_bursts(self):
        ok = True
        incr = 1 << ((self.data_width // 8).bit_length() - 1)
        for beats in (2, 4):
            base = 0x3000
            if not await self.test_wrap_burst(base + (beats - 1) * incr, beats,
                                              label=f"wrap-{beats}beat"):
                ok = False
        return ok

    async def run_basic_test(self):
        """Run basic write burst test suite"""
        self.log.info("=" * 80)
        self.log.info("BASIC WRITE BURST TEST SUITE")
        self.log.info("=" * 80)
        self.log.info("=== Scenarios AXI2AXIL-WR-01,02,03: Single write passthrough, burst decomposition, ID preservation ===")

        success = True

        # Test single-beat and small bursts
        test_cases = [
            (0x1000, [0x11111111]),                                    # Single beat
            (0x2000, [0x22222222, 0x33333333]),                       # 2-beat burst
            (0x3000, [0x44444444, 0x55555555, 0x66666666, 0x77777777]), # 4-beat burst
            (0x4000, [0xDEADBEEF]),                                    # Another single beat
        ]

        # Error propagation (BRESP) -- see test_error_response.
        if not await self.test_error_responses():
            success = False

        # Outstanding-burst identity -- see test_pipelined_aw_identity.
        if not await self.test_pipelined_aw_identity(label='b2b-ids'):
            success = False

        # Waiting burst AW must not deadlock a pending W -- see
        # test_pending_w_blocked_by_waiting_burst_aw.
        if not await self.test_pending_w_blocked_by_waiting_burst_aw(
                label='parked-aw'):
            success = False

        # WRAP bursts -- see test_wrap_burst.
        if not await self.test_wrap_bursts():
            success = False

        for addr, data_list in test_cases:
            if not await self.test_write_burst(addr, data_list):
                success = False

        # Lightweight b2b smoke: two short bursts with no inter-burst cooldown
        b2b_smoke = [
            (0x5000, [0xAA0000, 0xAA0001]),
            (0x5010, [0xBB0000, 0xBB0001]),
        ]
        if not await self.test_b2b_bursts(b2b_smoke):
            success = False

        return success

    async def run_medium_test(self):
        """Run medium write burst test suite"""
        self.log.info("=" * 80)
        self.log.info("MEDIUM WRITE BURST TEST SUITE")
        self.log.info("=" * 80)
        self.log.info("=== Scenarios AXI2AXIL-WR-04,05,06,08,09: WSTRB, BRESP, AW/W coordination, FIXED/INCR bursts ===")

        success = True

        # Test various burst lengths with random data
        for i in range(10):
            addr = random.randint(0, (1 << self.addr_width) - 1) & ~0x3
            burst_len = random.randint(1, 16)
            data_list = [random.randint(0, (1 << self.data_width) - 1) for _ in range(burst_len)]
            burst_type = random.choice([0, 1])  # FIXED or INCR

            if not await self.test_write_burst(addr, data_list, burst_type):
                success = False

        # B2B scenarios — exercises the page-probe class of bug
        b2b_bursts = []
        base = 0x80000
        for i in range(8):
            blen = random.randint(1, 8)
            addr = base + (i * 0x1000)
            data_list = [random.randint(0, (1 << self.data_width) - 1) for _ in range(blen)]
            b2b_bursts.append((addr, data_list))
        if not await self.test_b2b_bursts(b2b_bursts):
            success = False

        if not await self.test_b2b_mixed_lengths():
            success = False

        return success

    async def run_full_test(self):
        """Run full write burst test suite"""
        self.log.info("=" * 80)
        self.log.info("FULL WRITE BURST TEST SUITE")
        self.log.info("=" * 80)
        self.log.info("=== Scenario AXI2AXIL-WR-07: Write state machine comprehensive coverage ===")

        success = True

        # Comprehensive testing with various burst lengths and types
        for i in range(30):
            addr = random.randint(0, (1 << self.addr_width) - 1) & ~0x3
            burst_len = random.randint(1, 32)
            data_list = [random.randint(0, (1 << self.data_width) - 1) for _ in range(burst_len)]
            burst_type = random.choice([0, 1])  # FIXED or INCR

            if not await self.test_write_burst(addr, data_list, burst_type):
                success = False

        # All the medium b2b scenarios too
        b2b_bursts = []
        base = 0x90000
        for i in range(16):
            blen = random.randint(1, 16)
            addr = base + (i * 0x1000)
            data_list = [random.randint(0, (1 << self.data_width) - 1) for _ in range(blen)]
            b2b_bursts.append((addr, data_list))
        if not await self.test_b2b_bursts(b2b_bursts):
            success = False

        if not await self.test_b2b_mixed_lengths():
            success = False

        # FULL-only scenarios
        if not await self.test_partial_strobe():
            success = False

        if not await self.test_narrow_within_wide():
            success = False

        if not await self.test_max_burst():
            success = False

        return success

    def get_statistics(self):
        """Return test statistics"""
        return dict(self.stats)

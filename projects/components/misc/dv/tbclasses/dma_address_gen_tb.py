"""
DMA Address Generator Testbench

Reusable testbench class for validating dma_address_gen.sv module.
Tests 2D strided address generation with signed strides, per-dimension
wrap masks, and valid/ready backpressure on the 2-stage pipeline.

Key Features:
- Linear, row-major, column-major addressing modes
- Signed stride (reverse traversal) verification
- Per-dimension wrap mask (circular buffer) testing
- Pipeline backpressure and stall testing
- Tag pass-through verification

Design Pattern:
- Testbench: Infrastructure and stimulus (this file)
- Test Runner: Test intelligence and parameters

Author: RTL Design Sherpa
Created: 2025-04-08
"""

import cocotb
from cocotb.triggers import RisingEdge
from cocotb.clock import Clock
import random
import ctypes

# Framework imports
import os
import sys

from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

repo_root = get_repo_root()
sys.path.insert(0, repo_root)


def to_signed(val: int, width: int) -> int:
    """Convert unsigned integer to signed (two's complement)."""
    if val >= (1 << (width - 1)):
        return val - (1 << width)
    return val


def to_unsigned(val: int, width: int) -> int:
    """Convert signed integer to unsigned (two's complement)."""
    return val & ((1 << width) - 1)


class DMAAddressGenTB(TBBase):
    """
    Testbench class for DMA Address Generator (dma_address_gen.sv)

    Provides:
    - Configuration programming (base, strides, wrap masks)
    - Request submission with valid/ready handshaking
    - Result collection with expected-address checking
    - Backpressure injection on result interface
    - Comprehensive address computation model
    """

    def __init__(self, dut, **kwargs):
        """Initialize testbench."""
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        valid_levels = ['gate', 'func', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(
                f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'. "
                f"Valid: {valid_levels}"
            )
            self.TEST_LEVEL = 'gate'

        # Clock and reset
        self.clk = dut.i_clk
        self.clk_name = 'i_clk'
        self.rst_n = dut.i_rst_n

        # Get parameters from DUT
        self.addr_width = int(dut.ADDR_WIDTH.value)
        self.index_width = int(dut.INDEX_WIDTH.value)
        self.stride_width = int(dut.STRIDE_WIDTH.value)
        self.tag_width = int(dut.TAG_WIDTH.value)

        # Derived masks
        self.addr_mask = (1 << self.addr_width) - 1
        self.index_mask = (1 << self.index_width) - 1
        self.stride_mask = (1 << self.stride_width) - 1
        self.tag_mask = (1 << self.tag_width) - 1

        # Statistics
        self.requests_sent = 0
        self.results_received = 0
        self.mismatches = 0

        # Test level configuration
        self.test_configs = {
            'gate': {
                'linear_count': 16,
                'row_major_rows': 4,
                'row_major_cols': 4,
                'wrap_count': 16,
                'backpressure_count': 16,
                'stress_count': 32,
                'description': 'Quick smoke test (~30s)'
            },
            'func': {
                'linear_count': 64,
                'row_major_rows': 8,
                'row_major_cols': 8,
                'wrap_count': 64,
                'backpressure_count': 64,
                'stress_count': 128,
                'description': 'Functional validation (~90s)'
            },
            'full': {
                'linear_count': 256,
                'row_major_rows': 16,
                'row_major_cols': 16,
                'wrap_count': 256,
                'backpressure_count': 256,
                'stress_count': 512,
                'description': 'Comprehensive validation (~180s)'
            }
        }
        self.config = self.test_configs[self.TEST_LEVEL]
        self.log.info(
            f"Test level: {self.TEST_LEVEL.upper()} - "
            f"{self.config['description']}"
        )

    # ===================================================================
    # MANDATORY METHODS
    # ===================================================================

    async def setup_clocks_and_reset(self):
        """Complete initialization - start clocks and perform reset."""
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Initialize all inputs before reset
        self.dut.i_cfg_base_addr.value = 0
        self.dut.i_cfg_stride_0.value = 0
        self.dut.i_cfg_stride_1.value = 0
        self.dut.i_cfg_wrap_mask_0.value = 0
        self.dut.i_cfg_wrap_mask_1.value = 0
        self.dut.i_req_valid.value = 0
        self.dut.i_req_index_0.value = 0
        self.dut.i_req_index_1.value = 0
        self.dut.i_req_tag.value = 0
        self.dut.i_result_ready.value = 1

        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        """Assert reset signal."""
        self.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset signal."""
        self.rst_n.value = 1

    # ===================================================================
    # CONFIGURATION
    # ===================================================================

    def configure(self, base_addr: int, stride_0: int, stride_1: int,
                  wrap_mask_0: int = 0, wrap_mask_1: int = 0):
        """Program configuration ports (from descriptor fields)."""
        self.dut.i_cfg_base_addr.value = base_addr & self.addr_mask
        self.dut.i_cfg_stride_0.value = to_unsigned(stride_0, self.stride_width)
        self.dut.i_cfg_stride_1.value = to_unsigned(stride_1, self.stride_width)
        self.dut.i_cfg_wrap_mask_0.value = wrap_mask_0 & self.addr_mask
        self.dut.i_cfg_wrap_mask_1.value = wrap_mask_1 & self.addr_mask

        # Store for reference model
        self._base_addr = base_addr & self.addr_mask
        self._stride_0 = stride_0
        self._stride_1 = stride_1
        self._wrap_mask_0 = wrap_mask_0 & self.addr_mask
        self._wrap_mask_1 = wrap_mask_1 & self.addr_mask

        self.log.info(
            f"Config: base=0x{self._base_addr:010x} "
            f"stride_0={stride_0} stride_1={stride_1} "
            f"wrap_0=0x{self._wrap_mask_0:x} wrap_1=0x{self._wrap_mask_1:x}"
        )

    # ===================================================================
    # REFERENCE MODEL
    # ===================================================================

    def compute_expected_addr(self, index_0: int, index_1: int) -> int:
        """Compute expected address matching RTL behavior."""
        # Signed multiply (index is unsigned, stride is signed)
        raw_offset_0 = index_0 * self._stride_0
        raw_offset_1 = index_1 * self._stride_1

        # Truncate to ADDR_WIDTH
        offset_0 = raw_offset_0 & self.addr_mask
        offset_1 = raw_offset_1 & self.addr_mask

        # Apply wrap masks
        if self._wrap_mask_0 != 0:
            offset_0 = offset_0 & self._wrap_mask_0
        if self._wrap_mask_1 != 0:
            offset_1 = offset_1 & self._wrap_mask_1

        addr = (self._base_addr + offset_0 + offset_1) & self.addr_mask
        return addr

    # ===================================================================
    # REQUEST / RESULT INTERFACE
    # ===================================================================

    async def send_request(self, index_0: int, index_1: int, tag: int):
        """Send a single request with valid/ready handshaking."""
        self.dut.i_req_valid.value = 1
        self.dut.i_req_index_0.value = index_0 & self.index_mask
        self.dut.i_req_index_1.value = index_1 & self.index_mask
        self.dut.i_req_tag.value = tag & self.tag_mask

        # Wait for handshake
        while True:
            await RisingEdge(self.clk)
            if int(self.dut.o_req_ready.value) == 1:
                break

        self.dut.i_req_valid.value = 0
        self.requests_sent += 1

    async def collect_result(self, timeout: int = 100) -> dict:
        """Collect a single result with timeout."""
        self.dut.i_result_ready.value = 1

        for _ in range(timeout):
            await RisingEdge(self.clk)
            if int(self.dut.o_result_valid.value) == 1:
                result = {
                    'addr': int(self.dut.o_result_addr.value),
                    'tag': int(self.dut.o_result_tag.value),
                }
                self.results_received += 1
                return result

        self.log.error("Timeout waiting for result")
        return None

    async def send_and_check(self, index_0: int, index_1: int, tag: int) -> bool:
        """Send request, collect result, verify address and tag."""
        expected_addr = self.compute_expected_addr(index_0, index_1)

        await self.send_request(index_0, index_1, tag)
        result = await self.collect_result()

        if result is None:
            self.mismatches += 1
            return False

        addr_ok = result['addr'] == expected_addr
        tag_ok = result['tag'] == (tag & self.tag_mask)

        if not addr_ok:
            self.log.error(
                f"ADDR MISMATCH: idx=({index_0},{index_1}) "
                f"expected=0x{expected_addr:010x} got=0x{result['addr']:010x}"
            )
            self.mismatches += 1
        if not tag_ok:
            self.log.error(
                f"TAG MISMATCH: expected={tag & self.tag_mask} "
                f"got={result['tag']}"
            )
            self.mismatches += 1

        if self.DEBUG and addr_ok and tag_ok:
            self.log.info(
                f"  OK: idx=({index_0},{index_1}) "
                f"addr=0x{result['addr']:010x} tag={result['tag']}"
            )

        return addr_ok and tag_ok

    # ===================================================================
    # TEST SCENARIOS
    # ===================================================================

    async def run_linear_test(self, base_addr: int, stride: int,
                              count: int) -> bool:
        """Test linear/incremental addressing: addr = base + i * stride."""
        self.log.info(
            f"Linear test: base=0x{base_addr:x} stride={stride} "
            f"count={count}"
        )
        self.configure(base_addr, stride_0=stride, stride_1=0)
        await RisingEdge(self.clk)

        ok = True
        for i in range(count):
            if not await self.send_and_check(i, 0, i & self.tag_mask):
                ok = False
        return ok

    async def run_row_major_test(self, base_addr: int, elem_size: int,
                                 row_pitch: int, rows: int,
                                 cols: int) -> bool:
        """Test 2D row-major addressing."""
        self.log.info(
            f"Row-major test: base=0x{base_addr:x} elem={elem_size} "
            f"pitch={row_pitch} {rows}x{cols}"
        )
        self.configure(base_addr, stride_0=elem_size, stride_1=row_pitch)
        await RisingEdge(self.clk)

        ok = True
        for row in range(rows):
            for col in range(cols):
                tag = (row * cols + col) & self.tag_mask
                if not await self.send_and_check(col, row, tag):
                    ok = False
        return ok

    async def run_reverse_test(self, base_addr: int, stride: int,
                               count: int) -> bool:
        """Test reverse traversal with negative stride."""
        neg_stride = -stride
        self.log.info(
            f"Reverse test: base=0x{base_addr:x} stride={neg_stride} "
            f"count={count}"
        )
        self.configure(base_addr, stride_0=neg_stride, stride_1=0)
        await RisingEdge(self.clk)

        ok = True
        for i in range(count):
            if not await self.send_and_check(i, 0, i & self.tag_mask):
                ok = False
        return ok

    async def run_wrap_test(self, base_addr: int, stride: int,
                            wrap_size: int, count: int) -> bool:
        """Test circular buffer with wrap mask."""
        wrap_mask = wrap_size - 1  # Power-of-2 assumed
        self.log.info(
            f"Wrap test: base=0x{base_addr:x} stride={stride} "
            f"wrap=0x{wrap_mask:x} count={count}"
        )
        self.configure(
            base_addr, stride_0=stride, stride_1=0,
            wrap_mask_0=wrap_mask
        )
        await RisingEdge(self.clk)

        ok = True
        for i in range(count):
            if not await self.send_and_check(i, 0, i & self.tag_mask):
                ok = False
        return ok

    async def run_wrap_2d_test(self, base_addr: int, stride_0: int,
                               stride_1: int, wrap_0: int, wrap_1: int,
                               dim0_count: int, dim1_count: int) -> bool:
        """Test 2D wrap (both dimensions)."""
        self.log.info(
            f"Wrap 2D test: base=0x{base_addr:x} "
            f"stride=({stride_0},{stride_1}) "
            f"wrap=(0x{wrap_0:x},0x{wrap_1:x}) "
            f"size=({dim0_count},{dim1_count})"
        )
        self.configure(
            base_addr, stride_0=stride_0, stride_1=stride_1,
            wrap_mask_0=wrap_0, wrap_mask_1=wrap_1
        )
        await RisingEdge(self.clk)

        ok = True
        for d1 in range(dim1_count):
            for d0 in range(dim0_count):
                tag = (d1 * dim0_count + d0) & self.tag_mask
                if not await self.send_and_check(d0, d1, tag):
                    ok = False
        return ok

    async def run_fixed_addr_test(self, base_addr: int,
                                  count: int) -> bool:
        """Test fixed address mode (FIFO drain): stride=0."""
        self.log.info(
            f"Fixed addr test: base=0x{base_addr:x} count={count}"
        )
        self.configure(base_addr, stride_0=0, stride_1=0)
        await RisingEdge(self.clk)

        ok = True
        for i in range(count):
            if not await self.send_and_check(i, i, i & self.tag_mask):
                ok = False
        return ok

    async def run_backpressure_test(self, count: int) -> bool:
        """Test pipeline with random backpressure on result interface."""
        self.log.info(f"Backpressure test: count={count}")
        self.configure(0x1000, stride_0=8, stride_1=256)
        await RisingEdge(self.clk)

        rng = random.Random(self.SEED)
        ok = True

        # Interleave send and collect with random backpressure
        for i in range(count):
            idx0 = i % 8
            idx1 = i // 8
            tag = i & self.tag_mask
            expected_addr = self.compute_expected_addr(idx0, idx1)

            # Randomly stall result_ready before sending
            if rng.random() < 0.3:
                self.dut.i_result_ready.value = 0
                stall_cycles = rng.randint(1, 3)
                for _ in range(stall_cycles):
                    await RisingEdge(self.clk)
                self.dut.i_result_ready.value = 1

            await self.send_request(idx0, idx1, tag)

            # Randomly stall result_ready before collecting
            if rng.random() < 0.3:
                self.dut.i_result_ready.value = 0
                stall_cycles = rng.randint(1, 3)
                for _ in range(stall_cycles):
                    await RisingEdge(self.clk)
                self.dut.i_result_ready.value = 1

            result = await self.collect_result(timeout=200)
            if result is None:
                self.log.error(f"Timeout on result {i}")
                self.mismatches += 1
                ok = False
                continue

            if result['addr'] != expected_addr:
                self.log.error(
                    f"BP ADDR MISMATCH [{i}]: "
                    f"expected=0x{expected_addr:010x} "
                    f"got=0x{result['addr']:010x}"
                )
                self.mismatches += 1
                ok = False
            if result['tag'] != (tag & self.tag_mask):
                self.log.error(
                    f"BP TAG MISMATCH [{i}]: "
                    f"expected={tag & self.tag_mask} got={result['tag']}"
                )
                self.mismatches += 1
                ok = False

        return ok

    async def run_pipeline_throughput_test(self, count: int) -> bool:
        """Verify back-to-back throughput (1 addr/cycle when full)."""
        self.log.info(f"Pipeline throughput test: count={count}")
        self.configure(0x0, stride_0=4, stride_1=0)
        await RisingEdge(self.clk)

        # Keep result_ready always high
        self.dut.i_result_ready.value = 1

        expected = []
        results = []

        # Interleave: send requests and collect results concurrently
        # The pipeline is 2-deep, so we can have up to 2 in-flight
        send_idx = 0
        done_sending = False

        for cycle in range(count * 4 + 20):
            # Collect any available result
            await RisingEdge(self.clk)
            if int(self.dut.o_result_valid.value) == 1:
                results.append(int(self.dut.o_result_addr.value))

            # Send next request if pipeline can accept
            if not done_sending and int(self.dut.o_req_ready.value) == 1:
                expected.append(self.compute_expected_addr(send_idx, 0))
                self.dut.i_req_valid.value = 1
                self.dut.i_req_index_0.value = send_idx & self.index_mask
                self.dut.i_req_index_1.value = 0
                self.dut.i_req_tag.value = send_idx & self.tag_mask
                send_idx += 1
                if send_idx >= count:
                    done_sending = True
            elif done_sending:
                self.dut.i_req_valid.value = 0

            if len(results) >= count:
                break

        self.dut.i_req_valid.value = 0

        ok = True
        for i, (exp, got) in enumerate(zip(expected, results)):
            if exp != got:
                self.log.error(
                    f"Throughput [{i}]: expected=0x{exp:010x} "
                    f"got=0x{got:010x}"
                )
                ok = False

        if len(results) < count:
            self.log.error(
                f"Only received {len(results)}/{count} results"
            )
            ok = False
        else:
            self.log.info(
                f"Throughput OK: {len(results)}/{count} results in "
                f"{cycle+1} cycles"
            )

        return ok

    # ===================================================================
    # REPORTING
    # ===================================================================

    def get_test_report(self) -> dict:
        """Return test statistics."""
        return {
            'requests_sent': self.requests_sent,
            'results_received': self.results_received,
            'mismatches': self.mismatches,
            'test_level': self.TEST_LEVEL,
            'pass': self.mismatches == 0,
        }

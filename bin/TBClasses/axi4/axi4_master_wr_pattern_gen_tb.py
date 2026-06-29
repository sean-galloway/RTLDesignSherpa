# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: axi4_master_wr_pattern_gen_tb
# Purpose: Direct FUB TB for axi4_master_wr_pattern_gen. Drives the cfg
#          interface and acts as a minimal AXI4 slave on the M side so
#          the FSM exercises end-to-end (cfg_start -> AW/W/B -> cfg_done).

"""TB for `axi4_master_wr_pattern_gen`.

Terminates the M-side AXI with the framework's ``AXI4SlaveWrite`` BFM
backed by a shared ``MemoryModel``:
  * BFM drives ``awready`` / ``wready`` per ``slave_profile`` (default
    ``backtoback`` = 0-delay).
  * BFM commits each W beat into the MemoryModel at the AW's base addr +
    beat-stride.
  * BFM emits B responses; ``bresp_override`` injects a sticky error
    for the bresp_error_sticky scenario.

aw_log / w_log are populated from the BFM's channel callbacks so the
existing scenario assertions keep working unchanged.

A Python LFSR mirror in ``expected_data_words()`` delegates to the
canonical ``TBClasses.common.lfsr_mirror.simulate_xor_lfsr`` so the test
can compare per-beat data against ground truth — no per-TB drift.
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
from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
from TBClasses.common.lfsr_mirror import simulate_xor_lfsr as _shared_lfsr

from CocoTBFramework.components.axi4.axi4_interfaces import AXI4SlaveWrite
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.memory_model import MemoryModel


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


class _Axi4SlaveWriteWithBrespOverride(AXI4SlaveWrite):
    """AXI4SlaveWrite that lets the test inject a non-OKAY bresp.

    AXI4SlaveWrite hardcodes ``resp=0`` in its B-response packet. We
    wrap ``b_channel.create_packet`` to splice in ``bresp_override``
    so existing tests that set ``tb.bresp_override = 2`` (SLVERR) keep
    working without forking the framework class.
    """

    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.bresp_override: int = 0
        _orig_create = self.b_channel.create_packet
        outer = self

        def _wrapped(**kw):
            pkt = _orig_create(**kw)
            pkt.resp = outer.bresp_override
            return pkt
        self.b_channel.create_packet = _wrapped


class WrPatternGenTB(TBBase):
    CLK = 10

    LFSR_DEFAULT_SEED = 0xDEADBEEF
    # Matches LFSR_TAPS = {12'd32, 12'd22, 12'd2, 12'd1} (Fibonacci taps)
    LFSR_TAPS = (32, 22, 2, 1)
    DEFAULT_MEM_BYTES = 64 * 1024   # 64 KiB — covers kb32 (32 KiB) headroom

    def __init__(self, dut, *, mem_bytes: int = DEFAULT_MEM_BYTES) -> None:
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
        self.BYTES_PER_BEAT = self.AXI_DATA_WIDTH // 8

        # External assertion surface — populated by BFM channel callbacks.
        self.aw_log: List[CapturedAw] = []
        self.w_log:  List[CapturedW] = []

        # MemoryModel sized to cover the largest workload (kb32 = 32 KiB).
        self._mem_bytes = mem_bytes
        self.memory = MemoryModel(
            num_lines=mem_bytes // self.BYTES_PER_BEAT,
            bytes_per_line=self.BYTES_PER_BEAT,
            log=self.log,
        )
        self.slave: Optional[_Axi4SlaveWriteWithBrespOverride] = None

    # ---- bresp override convenience ----

    @property
    def bresp_override(self) -> int:
        return self.slave.bresp_override if self.slave else 0

    @bresp_override.setter
    def bresp_override(self, v: int) -> None:
        if self.slave is None:
            raise RuntimeError("bresp_override set before setup_clocks_and_reset()")
        self.slave.bresp_override = int(v) & 0x3

    @property
    def b_outstanding(self) -> List[int]:
        """Compat shim for legacy scenarios that introspected the old
        stub's outstanding-B FIFO. Reports IDs awaiting a B response
        from the AXI4SlaveWrite BFM. Empty list at cfg_done == all
        writes acknowledged."""
        if self.slave is None:
            return []
        pending = getattr(self.slave, "pending_transactions", {}) or {}
        out: List[int] = []
        for txn_id, txn_list in pending.items():
            for _ in txn_list:
                out.append(txn_id)
        return out

    # ---- setup ----

    async def setup_clocks_and_reset(self):
        cocotb.start_soon(Clock(self.dut.aclk, self.CLK, units="ns").start())
        self._drive_idle_cfg()
        self.dut.aresetn.value = 0
        for _ in range(10):
            await RisingEdge(self.dut.aclk)
        self.dut.aresetn.value = 1
        for _ in range(5):
            await RisingEdge(self.dut.aclk)
        # Bring up framework AXI4 slave on the engine's m_axi_* port.
        # Default slave delay = backtoback (0). Future scenarios can call
        # set_slave_delay_profile(...) to dial in stalls.
        self.slave = _Axi4SlaveWriteWithBrespOverride(
            dut=self.dut, clock=self.dut.aclk,
            prefix="m_axi_",
            data_width=self.AXI_DATA_WIDTH,
            id_width=self.AXI_ID_WIDTH,
            addr_width=32,
            user_width=1,
            multi_sig=True,
            memory_model=self.memory,
            log=self.log,
        )
        self.set_slave_delay_profile("backtoback")

        # Wire aw_log / w_log captures off the BFM's channel callbacks.
        def _aw_cb(pkt) -> None:
            self.aw_log.append(CapturedAw(
                addr  = int(getattr(pkt, "addr", 0)),
                axid  = int(getattr(pkt, "id", 0)),
                awlen = int(getattr(pkt, "len", 0)),
            ))

        def _w_cb(pkt) -> None:
            self.w_log.append(CapturedW(
                data = int(getattr(pkt, "data", 0)),
                last = int(getattr(pkt, "last", 0)),
            ))

        self.slave.aw_channel.add_callback(_aw_cb)
        self.slave.w_channel.add_callback(_w_cb)

    def _drive_idle_cfg(self) -> None:
        # The cfg surface is the only thing the TB drives now — the
        # AXI4SlaveWrite BFM owns m_axi_awready/wready/b*.
        self.dut.cfg_start_addr.value       = 0
        self.dut.cfg_addr_stride_0.value    = 0
        self.dut.cfg_addr_stride_1.value    = 0
        self.dut.cfg_addr_wrap_mask_0.value = 0
        self.dut.cfg_addr_wrap_mask_1.value = 0
        self.dut.cfg_burst_len.value        = 1
        self.dut.cfg_txn_count.value        = 0
        self.dut.cfg_axi_id.value           = 0
        self.dut.cfg_id_mode.value          = 0
        self.dut.cfg_axi_size.value         = 3
        self.dut.cfg_axi_burst.value        = 1  # INCR
        self.dut.cfg_lfsr_seed.value        = 0
        self.dut.cfg_data_mode.value        = 0
        self.dut.cfg_hash_seed0.value       = 0
        self.dut.cfg_hash_seed1.value       = 0
        self.dut.cfg_hash_seed2.value       = 0
        self.dut.cfg_wr_gap.value           = 0
        self.dut.cfg_start.value            = 0

    def set_slave_delay_profile(self, profile: str) -> None:
        """Apply the ``profile`` (from ``AXI_RANDOMIZER_CONFIGS``) to
        every slave channel's ready/valid randomizer. Use ``backtoback``
        (the default) for 0-delay always-ready; bump to ``slow_producer``
        / ``burst_pause`` etc. to stress flow control."""
        if profile not in AXI_RANDOMIZER_CONFIGS:
            raise ValueError(
                f"unknown profile {profile!r}; valid: "
                f"{sorted(AXI_RANDOMIZER_CONFIGS.keys())}"
            )
        cfg = AXI_RANDOMIZER_CONFIGS[profile]
        slave_constraints = cfg["slave"]   # {'ready_delay': ...}
        master_constraints = cfg["master"] # {'valid_delay': ...} for B
        self.slave.aw_channel.set_randomizer(FlexRandomizer(slave_constraints))
        self.slave.w_channel.set_randomizer(FlexRandomizer(slave_constraints))
        self.slave.b_channel.set_randomizer(FlexRandomizer(master_constraints))

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
                      hash_seed2: int = 0,
                      id_mode: int = 0) -> None:
        self.dut.cfg_start_addr.value       = start_addr
        self.dut.cfg_addr_stride_0.value    = stride_0
        self.dut.cfg_addr_stride_1.value    = stride_1
        self.dut.cfg_addr_wrap_mask_0.value = wrap_mask_0
        self.dut.cfg_addr_wrap_mask_1.value = wrap_mask_1
        self.dut.cfg_burst_len.value        = burst_len
        self.dut.cfg_txn_count.value        = txn_count
        self.dut.cfg_axi_id.value           = axi_id
        self.dut.cfg_id_mode.value          = id_mode & 0x3
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

    async def wait_done(self, timeout_cycles: int = 200_000) -> None:
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
        """Regenerate the Fibonacci LFSR sequence the DUT emits.
        Beat 0 = seed; beats 1..count-1 = subsequent advances. Delegates
        to the canonical shared mirror so this TB and the
        shifter_lfsr_fibonacci unit-test TB cannot drift."""
        seed = seed if seed not in (None, 0) else self.LFSR_DEFAULT_SEED
        return _shared_lfsr(
            seed=seed,
            taps=self.LFSR_TAPS,
            cycles=count - 1,
            width=self.LFSR_WIDTH,
            include_seed=True,
        )

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

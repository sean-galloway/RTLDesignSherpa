# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ioapic_merge_tb
# Purpose: Testbench for ioapic_deliv_merge_tb_top -- TWO apb4_ioapic channels
#          merged onto one receiver (RLB-008).
#
# Created: 2026-09-14

"""Testbench for the multi-IOAPIC delivery merge.

WHY THIS IS NOT A SUBCLASS OF IOAPICTB
--------------------------------------
IOAPICTB binds one APB master at the fixed prefix "s_apb" and reaches the
handshake through flat names (self.dut.s_apb_PSEL and friends). With two
IOAPICs both of those are wrong, and there is no override that makes them
right -- so this is a separate class.

It is smaller than that sounds. Only TWO methods in IOAPICTB hardcode signal
names, write_apb_register and read_apb_register, touching four signals
(PSEL, PENABLE, PREADY, PRDATA). Everything above them --
write_ioapic_register, read_ioapic_register, write_redirection_entry -- is
already master-agnostic. So the fix is one small indirection: a per-IOAPIC
PORT VIEW, with the register stack written once against it.

WHO DRIVES WHAT
---------------
src_ready/src_retry are merge OUTPUTS wired back to each IOAPIC's
irq_out_ready/irq_out_retry in the harness, so both producer handshakes close
in RTL. This testbench drives ONLY m_ready and m_retry -- it is the receiver on
the merged side, and nothing else. There is exactly one driver per net.
"""

import os
from typing import Dict, List, Optional, Tuple

from cocotb.triggers import RisingEdge
from cocotb.handle import SimHandleBase

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.apb.apb_components import APBMaster
from CocoTBFramework.components.apb.apb_packet import APBPacket
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.amba.amba_random_configs import APB_MASTER_RANDOMIZER_CONFIGS

import sys
from pathlib import Path
repo_root = Path(__file__).resolve().parents[6]
sys.path.insert(0, str(repo_root))

from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_tb import (
    IOAPICRegisterMap,
)


class _IOAPICPort:
    """One IOAPIC's APB access path: the BFM plus the four handshake signals.

    This is the whole reason a second TB class is cheap. cocotb_bus composes
    `<prefix>_<SIGNAL>` (cocotb_bus/bus.py:58) rather than substring-matching,
    so "s0_apb" and "s1_apb" bind exactly and cannot capture each other.
    """

    def __init__(self, tb, index: int, prefix: str):
        self.tb = tb
        self.index = index
        self.prefix = prefix
        self.log = tb.log
        d = tb.dut
        self.psel = getattr(d, f"{prefix}_PSEL")
        self.penable = getattr(d, f"{prefix}_PENABLE")
        self.pready = getattr(d, f"{prefix}_PREADY")
        self.prdata = getattr(d, f"{prefix}_PRDATA")
        self.master: Optional[APBMaster] = None

    async def create_master(self):
        self.master = APBMaster(
            entity=self.tb.dut,
            title=f"IOAPIC{self.index} APB Master",
            prefix=self.prefix,
            clock=self.tb.dut.pclk,
            bus_width=self.tb.apb_data_width,
            addr_width=self.tb.apb_addr_width,
            randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
            log=self.log,
        )
        await self.master.reset_bus()
        self.log.info(f"APB Master {self.index} bound at prefix '{self.prefix}'")

    def _packet(self, pwrite: int, addr: int, data: int) -> APBPacket:
        p = APBPacket(pwrite=pwrite, paddr=addr, pwdata=data, pstrb=0xF, pprot=0,
                      data_width=self.tb.apb_data_width,
                      addr_width=self.tb.apb_addr_width, strb_width=4)
        p.direction = 'WRITE' if pwrite else 'READ'
        return p

    async def _await_handshake(self, capture_read: bool) -> int:
        """Wait for PSEL & PENABLE & PREADY on THIS port. Returns PRDATA if asked."""
        data = 0
        for _ in range(100):
            await RisingEdge(self.tb.dut.pclk)
            if self.psel.value and self.penable.value and self.pready.value:
                if capture_read:
                    data = int(self.prdata.value)
                break
        else:
            self.log.error(f"APB{self.index} transaction timeout")
        await RisingEdge(self.tb.dut.pclk)
        return data

    async def write_apb(self, addr: int, data: int):
        await self.master.send(self._packet(1, addr, data))
        await self._await_handshake(capture_read=False)

    async def read_apb(self, addr: int) -> int:
        await self.master.send(self._packet(0, addr, 0))
        return await self._await_handshake(capture_read=True)

    async def write_reg(self, offset: int, data: int):
        """IOREGSEL then IOWIN -- the indirect sequence, per IOAPIC."""
        await self.write_apb(IOAPICRegisterMap.IOREGSEL, offset)
        await self.write_apb(IOAPICRegisterMap.IOWIN, data)

    async def read_reg(self, offset: int) -> int:
        await self.write_apb(IOAPICRegisterMap.IOREGSEL, offset)
        return await self.read_apb(IOAPICRegisterMap.IOWIN)

    async def write_rte(self, irq: int, vector: int, dest: int = 0,
                        delivery_mode: int = 0, dest_mode: int = 0,
                        polarity: int = 0, trigger_mode: int = 0, mask: int = 0):
        """Same composition as IOAPICTB.write_redirection_entry."""
        lo = ((vector & 0xFF) | ((delivery_mode & 0x7) << 8) |
              ((dest_mode & 0x1) << 11) | ((polarity & 0x1) << 13) |
              ((trigger_mode & 0x1) << 15) | ((mask & 0x1) << 16))
        hi = (dest & 0xFF) << 24
        await self.write_reg(IOAPICRegisterMap.get_redirection_offset(irq, False), lo)
        await self.write_reg(IOAPICRegisterMap.get_redirection_offset(irq, True), hi)
        self.log.info(f"IOAPIC{self.index} IRQ{irq}: vec=0x{vector:02X} "
                      f"deliv={delivery_mode} dest_mode={dest_mode}")


class IOAPICMergeTB(TBBase):
    """Two IOAPICs behind one merged delivery channel."""

    def __init__(self, dut: SimHandleBase, num_src: int = 2):
        super().__init__(dut)
        self.dut = dut
        self.num_src = num_src
        self.apb_data_width = 32
        self.apb_addr_width = 12
        self.ports: List[_IOAPICPort] = [
            _IOAPICPort(self, i, f"s{i}_apb") for i in range(num_src)
        ]
        self.log.info(f"IOAPIC merge testbench initialised, NUM_SRC={num_src}")

    # --- the three mandatory TBBase methods -------------------------------
    async def setup_clocks_and_reset(self):
        apb_ns = int(os.environ.get('TEST_APB_CLOCK_PERIOD', '10'))
        ioapic_ns = int(os.environ.get('TEST_IOAPIC_CLOCK_PERIOD', str(apb_ns)))
        await self.start_clock('pclk', freq=apb_ns, units='ns')
        await self.start_clock('ioapic_clk', freq=ioapic_ns, units='ns')
        await self.assert_reset()
        await self.wait_clocks('pclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('pclk', 5)
        self.log.info("Clock and reset setup complete")

    async def assert_reset(self):
        self.dut.presetn.value = 0
        self.dut.ioapic_resetn.value = 0

    async def deassert_reset(self):
        self.dut.presetn.value = 1
        self.dut.ioapic_resetn.value = 1

    # --- components -------------------------------------------------------
    async def setup_components(self):
        for p in self.ports:
            await p.create_master()
        self.dut.irq0_in.value = 0
        self.dut.irq1_in.value = 0
        self.dut.eoi0_in.value = 0
        self.dut.eoi0_vector.value = 0
        self.dut.eoi1_in.value = 0
        self.dut.eoi1_vector.value = 0
        # Receiver side only -- src_ready/src_retry are RTL-driven.
        self.dut.m_ready.value = 0
        self.dut.m_retry.value = 0
        await self.wait_clocks('pclk', 2)

    async def reset_all(self):
        await self.assert_reset()
        await self.wait_clocks('pclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('pclk', 5)
        self.dut.irq0_in.value = 0
        self.dut.irq1_in.value = 0
        self.dut.m_ready.value = 0
        self.dut.m_retry.value = 0
        await self.wait_clocks('pclk', 2)

    # --- stimulus / observation ------------------------------------------
    def pulse_irqs(self, mask0: int, mask1: int):
        """Raise pins on BOTH IOAPICs in the SAME cycle.

        Simultaneity matters: the arbiter rotates on ACK, so presenting the
        sources one at a time measures the testbench's ordering rather than
        the arbiter's fairness -- the same trap ioapic_tests_medium documents
        for the IOAPIC's own pin scan.
        """
        self.dut.irq0_in.value = mask0
        self.dut.irq1_in.value = mask1

    def clear_irqs(self):
        self.dut.irq0_in.value = 0
        self.dut.irq1_in.value = 0

    async def observe_merged(self, window_cycles: int, ready: int = 1,
                             retry: int = 0,
                             vector_filter: Optional[int] = None) -> List[Dict]:
        """Act as the receiver for a window and record every merged handshake.

        Drives m_ready/m_retry only. Each entry records which SOURCE the merge
        said the message came from, which is the routing claim under test.
        """
        self.dut.m_ready.value = ready
        self.dut.m_retry.value = retry
        seen: List[Dict] = []
        for _ in range(window_cycles):
            await RisingEdge(self.dut.pclk)
            if int(self.dut.m_valid.value) == 1 and int(self.dut.m_ready.value) == 1:
                vec = int(self.dut.m_vector.value)
                if vector_filter is not None and vec != vector_filter:
                    continue
                seen.append({
                    'vector':    vec,
                    'src_id':    int(self.dut.m_src_id.value),
                    'dest':      int(self.dut.m_dest.value),
                    'src_ready': int(self.dut.src_ready.value),
                    'src_retry': int(self.dut.src_retry.value),
                })
        self.dut.m_ready.value = 0
        self.dut.m_retry.value = 0
        return seen

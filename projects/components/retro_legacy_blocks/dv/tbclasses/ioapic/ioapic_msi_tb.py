# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ioapic_msi_tb
# Purpose: Testbench for ioapic_msi_emit_tb_top -- the MSI companion wired onto
#          a real apb4_ioapic delivery channel and a real apb4_master_stub
#          (RLB-008).
#
# Documentation: projects/components/retro_legacy_blocks/docs/ioapic_mas/
# Subsystem: retro_legacy_blocks/ioapic
#
# Created: 2026-09-14

"""Testbench for the MSI emitter sitting on a real IOAPIC channel.

WHY THIS IS A SUBCLASS AND WHAT IT HAD TO TAKE AWAY
---------------------------------------------------
Exactly the same reason as ioapic_arb_tb: IOAPICTB drives `irq_out_ready` and
`irq_out_retry` from Python because on the bare block the testbench IS the
receiver. Here the receiver is `ioapic_msi_emit`, so those pins are RTL-driven
outputs and a Python write to them is a multi-driver conflict.

The same five IOAPICTB methods write those pins, and all five are neutralised:
    setup_components          ready + retry   -> reimplemented without them
    reset_dut                 ready           -> reimplemented without it
    wait_for_interrupt        ready           -> disabled (raises)
    drain_pending_interrupts  ready           -> disabled (raises)
    count_irq_out_handshakes  ready           -> disabled (raises)

The last three RAISE rather than no-op, for the reason the arbiter TB gives: a
test reaching for the bare-block idiom here is asking the wrong question, and a
loud failure naming the replacement beats a quiet one that half-works. The
replacement is `observe_msi_writes()`, which only WATCHES -- the APB monitor
records what the master actually drove.

SIZING THE SLAVE, AND WHY 100 IS NOT 128
-----------------------------------------
APBSlave computes
    addr_bits_needed = (num_lines * strb_bits - 1).bit_length()
    memory_addr_mask = (1 << addr_bits_needed) - 1
    word_index       = (address & memory_addr_mask) >> 2
With a POWER-OF-TWO num_lines the mask is exactly wide enough that word_index
can never reach num_lines, so `word_index >= num_lines` is unreachable and the
out-of-range path -- the only source of PSLVERR here -- can never fire. A
slave sized 128 lines would make the retry test silently untestable: it would
pass by never being exercised.

100 lines gives mask 0x1FF and word indices up to 127, so words 100..127 are
out of range and DO return PSLVERR. That is what MSI_ADDR_BAD targets.
"""

import os
from typing import Dict, List

from cocotb.triggers import RisingEdge
from cocotb.handle import SimHandleBase

from CocoTBFramework.components.apb.apb_components import APBMaster
from CocoTBFramework.components.apb.apb_factories import (
    create_apb4_monitor, create_apb4_slave,
)
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.amba.amba_random_configs import APB_MASTER_RANDOMIZER_CONFIGS

import sys
from pathlib import Path
repo_root = Path(__file__).resolve().parents[6]
sys.path.insert(0, str(repo_root))

from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_tb import (
    IOAPICTB, IOAPICRegisterMap,
)


# Slave geometry -- see the docstring. NOT a power of two, deliberately.
MSI_SLAVE_LINES = 100

# An address whose masked word index is inside the slave (0x40 >> 2 = 16).
MSI_ADDR_GOOD = 0x0000_0040
# An address whose masked word index is 104, past the 100 lines the slave has,
# so the slave answers PSLVERR. Bits [19:12] are overwritten by the message
# destination, but the mask only looks at [8:0], so any destination still
# lands out of range.
MSI_ADDR_BAD = 0x0000_01A0


class IOAPICMsiTB(IOAPICTB):
    """IOAPICTB with the delivery handshake handed to the RTL MSI emitter."""

    def __init__(self, dut: SimHandleBase):
        super().__init__(dut)
        self.observed_writes: List[Dict] = []
        self.apb4_slave = None
        self.apb4_monitor = None
        self.log.info("IOAPIC+MSI testbench initialised")

    # ------------------------------------------------------------------
    # Observation
    # ------------------------------------------------------------------
    def _on_apb_txn(self, packet):
        """APB monitor callback: record completed WRITE transactions."""
        try:
            fields = getattr(packet, 'fields', {})
            if not fields.get('pwrite', 0):
                return
            self.observed_writes.append({
                'paddr': fields.get('paddr', 0),
                'pwdata': fields.get('pwdata', 0),
                'pstrb': fields.get('pstrb', 0),
                'pprot': fields.get('pprot', 0),
                'pslverr': fields.get('pslverr', 0),
            })
        except Exception as e:                      # pragma: no cover
            self.log.error(f"APB monitor callback error: {e}")

    def clear_observed(self):
        self.observed_writes = []

    async def observe_msi_writes(self, window_cycles: int) -> List[Dict]:
        """Watch for the given number of cycles and return what was written.

        Also SAMPLES the delivery pins every cycle. The counts matter because
        of how the two handshakes relate: deliv_ready is the master's
        cmd_ready, so the delivery handshake closes when the write is QUEUED,
        while deliv_retry only asserts when the bus response comes back --
        strictly later. ioapic_core qualifies retry AT the handshake
        (w_deliv_accept = w_deliv_done && !irq_out_retry), so a retry that
        arrives afterwards is gated away. `retry_at_handshake` is therefore
        the number that decides whether a refusal can ever be acted on.
        """
        self.deliv_handshakes = 0
        self.retry_asserts = 0
        self.retry_at_handshake = 0
        for _ in range(window_cycles):
            await RisingEdge(self.dut.pclk)
            try:
                v = int(self.dut.irq_out_valid.value)
                r = int(self.dut.irq_out_ready.value)
                q = int(self.dut.irq_out_retry.value)
            except ValueError:      # unresolvable during reset
                continue
            if v and r:
                self.deliv_handshakes += 1
                if q:
                    self.retry_at_handshake += 1
            if q:
                self.retry_asserts += 1
        self.log.info(
            f"  delivery pins over {window_cycles} cycles: "
            f"handshakes={self.deliv_handshakes} "
            f"retry_asserts={self.retry_asserts} "
            f"retry_at_handshake={self.retry_at_handshake}")
        return list(self.observed_writes)

    # ------------------------------------------------------------------
    # Programming
    # ------------------------------------------------------------------
    async def program_msi(self, addr: int, data: int):
        """Write IOAPICMSIADDR and IOAPICMSIDATA through IOREGSEL/IOWIN.

        This is the path under test: software writes, and the value has to
        survive the register block and come out on cfg_msi_*.
        """
        await self.write_ioapic_register(IOAPICRegisterMap.OFFSET_MSIADDR, addr)
        await self.write_ioapic_register(IOAPICRegisterMap.OFFSET_MSIDATA, data)
        self.log.info(f"MSI programmed: addr=0x{addr:08X} data=0x{data:08X}")

    # ------------------------------------------------------------------
    # Overrides: everything that used to drive irq_out_ready / irq_out_retry
    # ------------------------------------------------------------------
    async def setup_components(self):
        """IOAPICTB.setup_components minus the two emitter-owned pins.

        Reimplemented rather than extended, for the reason ioapic_arb_tb gives:
        calling super() first and 'undoing' it would still have placed a Python
        driver on an RTL-driven net.
        """
        self.log.info("Setting up IOAPIC+MSI components")
        try:
            self.apb4_master = APBMaster(
                entity=self.dut,
                title="IOAPIC APB Master",
                prefix="s_apb",
                clock=self.dut.pclk,
                bus_width=self.apb_data_width,
                addr_width=self.apb_addr_width,
                randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
                log=self.log,
            )
            await self.apb4_master.reset_bus()
            self.log.info("APB Master created and initialised")
        except Exception as e:
            self.log.error(f"Failed to create APB Master: {e}")
            raise

        # The far side: a real slave to terminate the master's writes, and a
        # monitor to record them. error_overflow=True is explicit -- the
        # factory defaults it to False, which would EXPAND the memory model
        # instead of refusing, and the retry test needs a refusal.
        try:
            self.apb4_slave = create_apb4_slave(
                self.dut, 'MSI APB Slave', 'm_apb', self.dut.pclk,
                registers=[0] * (MSI_SLAVE_LINES * 4),
                addr_width=32, data_width=32,
                error_overflow=True,
                log=self.log,
            )
            self.apb4_monitor = create_apb4_monitor(
                self.dut, 'MSI APB Monitor', 'm_apb', self.dut.pclk,
                addr_width=32, data_width=32, log=self.log,
            )
            self.apb4_monitor.add_callback(self._on_apb_txn)
            self.log.info("MSI APB slave + monitor created")
        except Exception as e:
            self.log.error(f"Failed to create MSI APB components: {e}")
            raise

        self.dut.irq_in.value = 0x000000
        self.dut.eoi_in.value = 0
        self.dut.eoi_vector.value = 0
        # NOT irq_out_ready / irq_out_retry -- u_msi drives those.
        self.clear_observed()
        await self.wait_clocks('pclk', 2)

    async def reset_dut(self):
        """IOAPICTB.reset_dut minus its irq_out_ready drive."""
        await self.assert_reset()
        await self.wait_clocks('pclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('pclk', 5)

        self.dut.irq_in.value = 0x000000
        self.dut.eoi_in.value = 0
        self.dut.eoi_vector.value = 0
        await self.wait_clocks('pclk', 2)

        self._last_int_vector = None
        self._last_int_dest = None
        self.clear_observed()
        self.log.info("IOAPIC+MSI reset to a clean state")

    async def wait_for_interrupt(self, timeout_cycles: int = 100) -> bool:
        raise RuntimeError(
            "wait_for_interrupt drives irq_out_ready, which u_msi owns here. "
            "Use observe_msi_writes() -- the APB monitor records what the "
            "emitter actually put on the bus."
        )

    async def drain_pending_interrupts(self, *args, **kwargs):
        raise RuntimeError(
            "drain_pending_interrupts drives irq_out_ready, which u_msi owns "
            "here. The emitter drains the channel by issuing writes."
        )

    async def count_irq_out_handshakes(self, *args, **kwargs):
        raise RuntimeError(
            "count_irq_out_handshakes drives irq_out_ready, which u_msi owns "
            "here. Count observed APB writes instead."
        )

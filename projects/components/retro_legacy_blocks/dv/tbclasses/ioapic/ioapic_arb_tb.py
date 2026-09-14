# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ioapic_arb_tb
# Purpose: Testbench for ioapic_lowest_pri_arb_tb_top -- the arbiter companion
#          wired onto a real apb4_ioapic delivery channel (RLB-008).
#
# Documentation: projects/components/retro_legacy_blocks/docs/ioapic_mas/
# Subsystem: retro_legacy_blocks/ioapic
#
# Created: 2026-09-14

"""Testbench for the LowestPriority arbiter sitting on a real IOAPIC channel.

WHY THIS IS A SUBCLASS AND WHAT IT HAD TO TAKE AWAY
---------------------------------------------------
IOAPICTB owns the delivery handshake: it drives `irq_out_ready` (and
`irq_out_retry`) from Python because, on the bare block, the testbench IS the
receiver. Under this harness the receiver is `ioapic_lowest_pri_arb`, so those
two pins are RTL-driven OUTPUTS. A Python write to them is a multi-driver
conflict, and it presents as a confusing X or a stuck handshake rather than as
an obvious error.

FIVE IOAPICTB methods write those pins, and every one is neutralised here:
    setup_components          ready + retry   -> reimplemented without them
    reset_dut                 ready           -> reimplemented without it
    wait_for_interrupt        ready           -> disabled (raises)
    drain_pending_interrupts  ready           -> disabled (raises)
    count_irq_out_handshakes  ready           -> disabled (raises)

The last three RAISE rather than silently no-op. A test that reaches for the
bare-block idiom here is asking the wrong question, and a loud failure naming
the replacement is worth more than a quiet one that half-works. Their
replacement is `observe_deliveries()`, which only WATCHES.

The register-programming helpers (write_redirection_entry, pulse_irq,
write_ioapic_register, read_remote_irr, set_arbitration_round_robin) touch none
of those pins and are inherited unchanged.
"""

import os
from typing import Dict, List, Optional

from cocotb.triggers import RisingEdge
from cocotb.handle import SimHandleBase

from CocoTBFramework.components.apb.apb_components import APBMaster
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.amba.amba_random_configs import APB_MASTER_RANDOMIZER_CONFIGS

import sys
from pathlib import Path
repo_root = Path(__file__).resolve().parents[6]
sys.path.insert(0, str(repo_root))

from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_tb import (
    IOAPICTB, IOAPICRegisterMap,
)


class IOAPICArbTB(IOAPICTB):
    """IOAPICTB with the delivery handshake handed to the RTL arbiter."""

    def __init__(self, dut: SimHandleBase, num_cpus: int = 4):
        super().__init__(dut)
        self.num_cpus = num_cpus
        self.log.info(f"IOAPIC+arbiter testbench initialised, NUM_CPUS={num_cpus}")

    # ------------------------------------------------------------------
    # Overrides: everything that used to drive irq_out_ready / irq_out_retry
    # ------------------------------------------------------------------
    async def setup_components(self):
        """IOAPICTB.setup_components minus the two arbiter-owned pins.

        Reimplemented rather than extended: the parent drives irq_out_ready and
        irq_out_retry, so calling super() first and 'undoing' it would still
        have placed a Python driver on an RTL-driven net.
        """
        self.log.info("Setting up IOAPIC+arbiter components")
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

        self.dut.irq_in.value = 0x000000
        self.dut.eoi_in.value = 0
        self.dut.eoi_vector.value = 0
        # NOT irq_out_ready / irq_out_retry -- u_arb drives those.
        self.set_cpu_state(can_accept=0)
        await self.wait_clocks('pclk', 2)

    async def reset_dut(self):
        """IOAPICTB.reset_dut minus its irq_out_ready drive (line 695 there)."""
        await self.assert_reset()
        await self.wait_clocks('pclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('pclk', 5)

        self.dut.irq_in.value = 0x000000
        self.dut.eoi_in.value = 0
        self.dut.eoi_vector.value = 0
        self.set_cpu_state(can_accept=0)
        await self.wait_clocks('pclk', 2)

        self._last_int_vector = None
        self._last_int_dest = None
        self.log.info("IOAPIC+arbiter reset to a clean state")

    async def wait_for_interrupt(self, timeout_cycles: int = 100) -> bool:
        raise RuntimeError(
            "wait_for_interrupt() drives irq_out_ready, which u_arb drives here. "
            "Use observe_deliveries() -- the arbiter closes the handshake itself."
        )

    async def drain_pending_interrupts(self, *args, **kwargs):
        raise RuntimeError(
            "drain_pending_interrupts() drives irq_out_ready, which u_arb drives "
            "here. Use reset_dut() to reach a clean state."
        )

    async def count_irq_out_handshakes(self, *args, **kwargs):
        raise RuntimeError(
            "count_irq_out_handshakes() drives irq_out_ready, which u_arb drives "
            "here. Use observe_deliveries(), which only watches."
        )

    # ------------------------------------------------------------------
    # The consumer state the arbiter arbitrates on
    # ------------------------------------------------------------------
    def set_cpu_state(self, apic_id=None, logical_dest=None, priority=None,
                      can_accept=None):
        """Drive the per-CPU inputs. Unpacked array ports are indexed handles
        (`dut.cpu_apic_id[i]`); cpu_can_accept is a packed vector."""
        if apic_id is not None:
            for i, v in enumerate(apic_id):
                self.dut.cpu_apic_id[i].value = v
        if logical_dest is not None:
            for i, v in enumerate(logical_dest):
                self.dut.cpu_logical_dest[i].value = v
        if priority is not None:
            for i, v in enumerate(priority):
                self.dut.cpu_priority[i].value = v
        if can_accept is not None:
            self.dut.cpu_can_accept.value = can_accept

    async def observe_deliveries(self, window_cycles: int,
                                 vector_filter: Optional[int] = None) -> List[Dict]:
        """Watch the channel for `window_cycles` and record every completed
        delivery. Drives NOTHING: the arbiter's deliv_ready closes the
        handshake, so a handshake here is the real thing rather than one the
        testbench manufactured.

        Returns one dict per handshake: vector, the one-hot cpu_irq_valid, the
        retry flag, and the delivery mode the receiver saw.
        """
        seen: List[Dict] = []
        for _ in range(window_cycles):
            await RisingEdge(self.dut.pclk)
            if int(self.dut.irq_out_valid.value) == 1 and int(self.dut.irq_out_ready.value) == 1:
                vec = int(self.dut.irq_out_vector.value)
                if vector_filter is not None and vec != vector_filter:
                    continue
                seen.append({
                    'vector':     vec,
                    'cpu_mask':   int(self.dut.cpu_irq_valid.value),
                    'retry':      int(self.dut.irq_out_retry.value),
                    'deliv_mode': int(self.dut.cpu_irq_deliv_mode.value),
                })
        return seen

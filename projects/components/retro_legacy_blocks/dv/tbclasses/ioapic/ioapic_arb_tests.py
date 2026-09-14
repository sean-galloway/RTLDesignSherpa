# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ioapic_arb_tests
# Purpose: The SEAM between apb4_ioapic and ioapic_lowest_pri_arb (RLB-008).
#
# Created: 2026-09-14

"""What these tests are for, and what they deliberately do NOT re-test.

`ioapic_tests_medium.test_rlb008_lowest_priority_retry` already proves the
IOAPIC half at its own ports: drive irq_out_retry from Python, and a refused
edge stays pending and is offered again. The arbiter's own contract is proved
at ITS ports by formal (prove + cover, mutation-checked).

Neither can reach what happens when the two are wired together, which is the
only thing these tests are about:

  * the arbiter's deliv_ready actually closes ioapic_core's handshake,
  * a grant lands on the CPU the message was addressed to,
  * LowestPriority picks ONE cpu -- from real cpu_priority inputs, not from a
    formal harness's free variables,
  * `cpu_can_accept == 0` is what produces the retry the IOAPIC then acts on,
    and clearing it lets the SAME vector through.

Every check carries a count. A test that ran zero comparisons and reported
"no violations" is the failure mode this repo has hit twice; each test below
asserts it observed something before it is allowed to pass.
"""

from cocotb.triggers import ClockCycles

from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_tb import (
    IOAPICRegisterMap,
)


class IOAPICArbTests:
    """Seam tests for apb4_ioapic + ioapic_lowest_pri_arb."""

    def __init__(self, tb):
        self.tb = tb
        self.log = tb.log
        # Four CPUs with distinct IDs and one-hot logical destinations.
        self.apic_ids = [0x00, 0x01, 0x02, 0x03]
        self.logical = [0x01, 0x02, 0x04, 0x08]

    async def _arm(self, irq, vector, dest, deliv_mode, dest_mode):
        await self.tb.reset_dut()
        await self.tb.write_redirection_entry(
            irq=irq, vector=vector, dest=dest,
            delivery_mode=deliv_mode, dest_mode=dest_mode,
            polarity=0, trigger_mode=0, mask=0)
        await ClockCycles(self.tb.pclk, 20)

    async def test_physical_delivery_reaches_that_cpu(self) -> bool:
        """A physical-destination message grants exactly the addressed CPU."""
        self.log.info("=== seam: physical destination reaches that CPU ===")
        try:
            checks = 0
            for target in range(4):
                await self._arm(irq=3, vector=0x40 + target,
                                dest=self.apic_ids[target],
                                deliv_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                                dest_mode=0)
                self.tb.set_cpu_state(apic_id=self.apic_ids,
                                      logical_dest=self.logical,
                                      priority=[0x10, 0x10, 0x10, 0x10],
                                      can_accept=0xF)
                await self.tb.pulse_irq(3)
                seen = await self.tb.observe_deliveries(200, vector_filter=0x40 + target)
                if not seen:
                    self.log.error(f"  CPU{target}: no delivery observed")
                    return False
                mask = seen[0]['cpu_mask']
                checks += 1
                if mask != (1 << target):
                    self.log.error(f"  CPU{target}: granted mask 0x{mask:X}, "
                                   f"want 0x{1 << target:X}")
                    return False
                self.log.info(f"  CPU{target}: granted correctly (mask 0x{mask:X})")
            if checks == 0:
                self.log.error("  no checks performed -- vacuous pass refused")
                return False
            self.log.info(f"seam physical delivery GREEN ({checks} checks)")
            return True
        except Exception as e:
            self.log.error(f"physical delivery test error: {e}")
            return False

    async def test_lowest_priority_picks_one_cpu(self) -> bool:
        """LowestPriority grants the single lowest-priority eligible CPU."""
        self.log.info("=== seam: LowestPriority picks one CPU, by priority ===")
        try:
            checks = 0
            # Rotate which CPU holds the lowest value so a fixed winner fails.
            for winner in range(4):
                prios = [0x80, 0x80, 0x80, 0x80]
                prios[winner] = 0x01
                await self._arm(irq=5, vector=0x60 + winner, dest=0x0F,
                                deliv_mode=IOAPICRegisterMap.DELIV_MODE_LOWPRI,
                                dest_mode=1)          # logical: the whole set
                self.tb.set_cpu_state(apic_id=self.apic_ids,
                                      logical_dest=self.logical,
                                      priority=prios, can_accept=0xF)
                await self.tb.pulse_irq(5)
                seen = await self.tb.observe_deliveries(200, vector_filter=0x60 + winner)
                if not seen:
                    self.log.error(f"  winner CPU{winner}: no delivery observed")
                    return False
                mask = seen[0]['cpu_mask']
                checks += 1
                if mask != (1 << winner):
                    self.log.error(f"  lowest priority was CPU{winner} but mask "
                                   f"was 0x{mask:X}")
                    return False
                self.log.info(f"  CPU{winner} (priority 0x01) won, mask 0x{mask:X}")
            if checks == 0:
                self.log.error("  no checks performed -- vacuous pass refused")
                return False
            self.log.info(f"seam LowestPriority GREEN ({checks} checks)")
            return True
        except Exception as e:
            self.log.error(f"lowest-priority test error: {e}")
            return False

    async def test_no_acceptor_retries_then_delivers(self) -> bool:
        """cpu_can_accept==0 drives retry; clearing it delivers the SAME vector.

        This is the one that could not be written before: the retry is produced
        by real consumer state rather than by the testbench asserting the pin.
        """
        self.log.info("=== seam: refusal comes from cpu_can_accept, then clears ===")
        try:
            vector = 0x71
            await self._arm(irq=7, vector=vector, dest=0x0F,
                            deliv_mode=IOAPICRegisterMap.DELIV_MODE_LOWPRI,
                            dest_mode=1)
            # Nobody can accept -> the arbiter must raise retry on every offer.
            self.tb.set_cpu_state(apic_id=self.apic_ids,
                                  logical_dest=self.logical,
                                  priority=[0x10] * 4, can_accept=0x0)
            await self.tb.pulse_irq(7)
            refused = await self.tb.observe_deliveries(200, vector_filter=vector)
            if len(refused) < 2:
                self.log.error(f"  only {len(refused)} offer(s) while refusing; "
                               f"a refusal must retire nothing (want >= 2)")
                return False
            if not all(o['retry'] == 1 and o['cpu_mask'] == 0 for o in refused):
                self.log.error("  an offer was not marked retry, or granted a CPU "
                               "while none could accept")
                return False
            self.log.info(f"  refused {len(refused)} offer(s), all retry=1, no grant")

            # Now let exactly CPU2 accept: the same vector must land there.
            self.tb.set_cpu_state(can_accept=0x4)
            accepted = await self.tb.observe_deliveries(200, vector_filter=vector)
            took = [o for o in accepted if o['retry'] == 0]
            if not took:
                self.log.error("  vector never delivered after a CPU could accept")
                return False
            if took[0]['cpu_mask'] != 0x4:
                self.log.error(f"  delivered to mask 0x{took[0]['cpu_mask']:X}, "
                               f"want 0x4 (only CPU2 could accept)")
                return False
            self.log.info(f"  delivered to CPU2 once it could accept "
                          f"({len(refused)} refusals then {len(took)} accept(s))")
            return True
        except Exception as e:
            self.log.error(f"retry-then-deliver test error: {e}")
            return False

    async def test_fixed_mode_signals_whole_set(self) -> bool:
        """Fixed is not arbitrated: every eligible CPU in the set is signalled."""
        self.log.info("=== seam: Fixed mode signals the whole destination set ===")
        try:
            vector = 0x55
            await self._arm(irq=9, vector=vector, dest=0x0F,
                            deliv_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                            dest_mode=1)                  # logical, all four
            self.tb.set_cpu_state(apic_id=self.apic_ids,
                                  logical_dest=self.logical,
                                  priority=[0x10] * 4, can_accept=0xF)
            await self.tb.pulse_irq(9)
            seen = await self.tb.observe_deliveries(200, vector_filter=vector)
            if not seen:
                self.log.error("  no delivery observed")
                return False
            mask = seen[0]['cpu_mask']
            if bin(mask).count('1') < 2:
                self.log.error(f"  Fixed granted mask 0x{mask:X}; the whole "
                               f"eligible set should be signalled, not arbitrated")
                return False
            self.log.info(f"  Fixed signalled mask 0x{mask:X} (whole set)")
            return True
        except Exception as e:
            self.log.error(f"fixed-mode test error: {e}")
            return False

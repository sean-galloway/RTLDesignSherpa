# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ioapic_boot_intx_tests
# Purpose: The SEAM between apb4_ioapic and ioapic_boot_intx (RLB-008).
#
# Created: 2026-09-14

"""What these tests are for, and what they deliberately do NOT re-test.

Formal proves the companion's contract at its own ports, with irq_in, cfg_mask
and boot_intx_en as FREE variables: the per-pin reroute decision, that a
disabled block reroutes nothing, that an unmasked pin never reroutes, and the
map onto the legacy inputs. Mutation-checked. None of that is repeated here.

What formal structurally cannot reach is where those three inputs come from:

  * cfg_mask is a free vector there. It proves the companion obeys whatever
    mask it is handed -- not that apb4_ioapic's exported cfg_mask_vec really
    tracks the IOREDTBL mask bits software writes through IOWIN.
  * boot_intx_en is likewise free. The register path IOWIN -> regblock ->
    cfg_boot_intx_en is outside the proof entirely.
  * the packed PIC_MAP parameter is a constant there; here it is the identity
    map the wrapper sets, so a pin carrying the no-reroute code can be shown
    to reach nothing.

Every check carries a count. A test that ran zero comparisons and reported no
violations is the failure mode this repo has hit twice.
"""

from cocotb.triggers import ClockCycles

from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_tb import (
    IOAPICRegisterMap,
)


class IOAPICBootIntxTests:
    """Seam tests for apb4_ioapic -> ioapic_boot_intx."""

    def __init__(self, tb):
        self.tb = tb
        self.log = tb.log

    async def _arm(self, irq, masked, enabled):
        """Reset, program one RTE with the given mask, set the enable bit."""
        await self.tb.reset_dut()
        await self.tb.write_redirection_entry(
            irq=irq, vector=0x40 + irq, dest=0x01,
            delivery_mode=IOAPICRegisterMap.DELIV_MODE_FIXED, dest_mode=0,
            polarity=0, trigger_mode=0, mask=1 if masked else 0)
        await self.tb.write_ioapic_register(
            IOAPICRegisterMap.OFFSET_BOOTINTX, 1 if enabled else 0)
        await ClockCycles(self.tb.pclk, 20)

    async def _drive(self, irq):
        self.tb.dut.irq_in.value = (1 << irq)
        await ClockCycles(self.tb.pclk, 5)

    def _read(self):
        return (int(self.tb.dut.reroute.value),
                int(self.tb.dut.pic_irq.value))

    # ------------------------------------------------------------------
    # gate
    # ------------------------------------------------------------------
    async def test_masked_pin_reroutes_to_its_legacy_input(self) -> bool:
        """The whole feature, end to end through both register paths."""
        self.log.info("=== seam: masked pin reroutes when enabled ===")
        try:
            irq = 3
            await self._arm(irq, masked=True, enabled=True)

            # The exported state first. If either register path is broken the
            # reroute check below would be misleading about which half failed.
            mask_vec = int(self.tb.dut.cfg_mask_vec.value)
            en = int(self.tb.dut.cfg_boot_intx_en.value)
            if not (mask_vec >> irq) & 1:
                self.log.error(
                    f"  cfg_mask_vec=0x{mask_vec:06X} does not show pin {irq} "
                    "masked -- the IOREDTBL mask export is broken, not the "
                    "companion")
                return False
            if en != 1:
                self.log.error(
                    "  cfg_boot_intx_en reads 0 after writing IOAPICBOOTINTX "
                    "-- the enable register path is broken")
                return False
            checks = 2

            await self._drive(irq)
            reroute, pic = self._read()
            if not (reroute >> irq) & 1:
                self.log.error(f"  reroute=0x{reroute:06X}, pin {irq} not set")
                return False
            checks += 1
            if pic != (1 << irq):
                self.log.error(
                    f"  pic_irq=0x{pic:02X}, want 0x{1 << irq:02X} (identity "
                    "map for the low 8 pins)")
                return False
            checks += 1

            self.log.info(f"seam boot-intx reroute GREEN ({checks} checks)")
            return True
        except Exception as e:
            self.log.error(f"reroute test error: {e}")
            return False

    # ------------------------------------------------------------------
    # func
    # ------------------------------------------------------------------
    async def test_unmasked_pin_does_not_reroute(self) -> bool:
        """An UNMASKED pin must not reach the PIC -- it would be taken twice.

        This is the half that stops the crutch from double-delivering an
        interrupt the IOAPIC is actively handling.
        """
        self.log.info("=== seam: unmasked pin does not reroute ===")
        try:
            irq = 4
            await self._arm(irq, masked=False, enabled=True)
            await self._drive(irq)
            reroute, pic = self._read()
            if reroute != 0 or pic != 0:
                self.log.error(
                    f"  an UNMASKED pin rerouted: reroute=0x{reroute:06X} "
                    f"pic_irq=0x{pic:02X} -- it would be delivered twice")
                return False
            self.log.info("seam unmasked-no-reroute GREEN (1 check)")
            return True
        except Exception as e:
            self.log.error(f"unmasked test error: {e}")
            return False

    async def test_disable_stops_rerouting(self) -> bool:
        """With the enable clear, a masked asserted pin reaches nothing.

        The reason the enable exists: an OS that has programmed the IOAPIC
        wants the crutch off, and the only other way to stop a deliberately
        masked pin leaking would be to unmask it.
        """
        self.log.info("=== seam: disable stops rerouting ===")
        try:
            irq = 5
            checks = 0

            await self._arm(irq, masked=True, enabled=False)
            await self._drive(irq)
            reroute, pic = self._read()
            if reroute != 0 or pic != 0:
                self.log.error(
                    f"  disabled but rerouted: reroute=0x{reroute:06X} "
                    f"pic_irq=0x{pic:02X}")
                return False
            checks += 1

            # Now enable it with the pin still asserted: the SAME stimulus
            # must start rerouting, which shows the first result was the
            # enable and not a dead harness.
            await self.tb.write_ioapic_register(
                IOAPICRegisterMap.OFFSET_BOOTINTX, 1)
            await ClockCycles(self.tb.pclk, 10)
            reroute, pic = self._read()
            if pic != (1 << irq):
                self.log.error(
                    f"  after enabling, pic_irq=0x{pic:02X}, want "
                    f"0x{1 << irq:02X} -- the first check may have passed "
                    "because nothing was driven at all")
                return False
            checks += 1

            self.log.info(f"seam enable-gate GREEN ({checks} checks)")
            return True
        except Exception as e:
            self.log.error(f"disable test error: {e}")
            return False

    # ------------------------------------------------------------------
    # full
    # ------------------------------------------------------------------
    async def test_unmapped_pin_reaches_no_legacy_input(self) -> bool:
        """A pin carrying the no-reroute code reroutes but maps nowhere.

        The wrapper maps pins 0-7 identity and gives pins 8+ the no-reroute
        code. Pin 8 masked, asserted and enabled must set its reroute bit --
        the decision is per-pin and independent of the map -- while pic_irq
        stays clear. That is what shows the map is consulted rather than
        ignored.
        """
        self.log.info("=== seam: unmapped pin reaches no legacy input ===")
        try:
            irq = 8
            await self._arm(irq, masked=True, enabled=True)
            await self._drive(irq)
            reroute, pic = self._read()
            checks = 0
            if not (reroute >> irq) & 1:
                self.log.error(
                    f"  reroute=0x{reroute:06X}: pin {irq} should still show "
                    "as rerouting; the decision does not depend on the map")
                return False
            checks += 1
            if pic != 0:
                self.log.error(
                    f"  pic_irq=0x{pic:02X}, want 0 -- pin {irq} carries the "
                    "no-reroute code and must reach no legacy input")
                return False
            checks += 1
            self.log.info(f"seam no-reroute-code GREEN ({checks} checks)")
            return True
        except Exception as e:
            self.log.error(f"unmapped test error: {e}")
            return False

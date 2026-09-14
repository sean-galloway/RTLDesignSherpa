# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ioapic_msi_tests
# Purpose: The SEAM between apb4_ioapic, ioapic_msi_emit and a real APB master
#          (RLB-008).
#
# Created: 2026-09-14

"""What these tests are for, and what they deliberately do NOT re-test.

Formal proves the emitter's mapping at its own ports (P1-P9, prove + cover,
mutation-checked): addr[19:12] is the destination, data[7:0] the vector,
data[10:8] the delivery mode, data[11] the destination mode, the command
packing matches what apb4_master_stub unpacks, and deliv_retry is exactly
`rsp_valid && pslverr`. None of that is re-proved here.

What formal structurally CANNOT reach:

  * msi_addr_base and msi_data_template are FREE VARIABLES there. It proves
    the emitter copies whatever it is given -- not that what software wrote
    through IOREGSEL/IOWIN is what it is given. The registers were added
    precisely so software could set them, so the register path is the claim.
  * rsp_data is `anyseq`. It proves retry follows pslverr; it cannot show that
    a real apb4_master_stub returns pslverr when a real slave refuses, or that
    the refused message is then re-offered.
  * No master is instantiated, so nothing shows the packed command actually
    becomes PSEL/PENABLE/PADDR/PWDATA on a bus.

Every check carries a count. A test that ran zero comparisons and reported no
violations is the failure mode this repo has hit twice, so each test asserts it
observed something before it is allowed to pass.
"""

from cocotb.triggers import ClockCycles

from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_tb import (
    IOAPICRegisterMap,
)
from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_msi_tb import (
    MSI_ADDR_BAD, MSI_ADDR_GOOD,
)


def expected_addr(base: int, dest: int) -> int:
    """Bits [19:12] are replaced by the destination; the rest pass through."""
    return (base & ~(0xFF << 12)) | ((dest & 0xFF) << 12)


def expected_data(template: int, vector: int, deliv_mode: int,
                  dest_mode: int) -> int:
    """[7:0] vector, [10:8] delivery mode, [11] destination mode."""
    return ((template & ~0xFFF)
            | (vector & 0xFF)
            | ((deliv_mode & 0x7) << 8)
            | ((dest_mode & 0x1) << 11))


class IOAPICMsiTests:
    """Seam tests for apb4_ioapic -> ioapic_msi_emit -> apb4_master_stub."""

    def __init__(self, tb):
        self.tb = tb
        self.log = tb.log

    async def _arm(self, irq, vector, dest, deliv_mode, dest_mode,
                   msi_addr=MSI_ADDR_GOOD, msi_data=0x0000_0000):
        """Reset, program the MSI registers, then arm one redirection entry."""
        await self.tb.reset_dut()
        await self.tb.program_msi(msi_addr, msi_data)
        await self.tb.write_redirection_entry(
            irq=irq, vector=vector, dest=dest,
            delivery_mode=deliv_mode, dest_mode=dest_mode,
            polarity=0, trigger_mode=0, mask=0)
        await ClockCycles(self.tb.pclk, 20)
        self.tb.clear_observed()

    # ------------------------------------------------------------------
    # gate
    # ------------------------------------------------------------------
    async def test_programmed_values_reach_the_bus(self) -> bool:
        """A value written over APB is the value that appears on the MSI write.

        This is the register path end to end, and the reason the addresses are
        registers at all.
        """
        self.log.info("=== seam: programmed MSI address and data reach the bus ===")
        try:
            base, template = MSI_ADDR_GOOD, 0x0000_0000
            vector, dest = 0x51, 0x02
            await self._arm(irq=4, vector=vector, dest=dest,
                            deliv_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                            dest_mode=0, msi_addr=base, msi_data=template)

            # The config outputs must carry what software wrote, before any
            # question about the bus. If this fails the register path is
            # broken and the bus check would only confuse the diagnosis.
            got_addr = int(self.tb.dut.cfg_msi_addr.value)
            got_data = int(self.tb.dut.cfg_msi_data.value)
            if got_addr != base or got_data != template:
                self.log.error(
                    f"  cfg_msi_* wrong: addr 0x{got_addr:08X} (want "
                    f"0x{base:08X}), data 0x{got_data:08X} (want "
                    f"0x{template:08X})")
                return False

            await self.tb.pulse_irq(4)
            writes = await self.tb.observe_msi_writes(200)
            if not writes:
                self.log.error("  no MSI write observed on the APB master")
                return False

            want_a = expected_addr(base, dest)
            want_d = expected_data(template, vector,
                                   IOAPICRegisterMap.DELIV_MODE_FIXED, 0)
            w = writes[0]
            checks = 0
            if w['paddr'] != want_a:
                self.log.error(f"  PADDR 0x{w['paddr']:08X}, want 0x{want_a:08X}")
                return False
            checks += 1
            if w['pwdata'] != want_d:
                self.log.error(f"  PWDATA 0x{w['pwdata']:08X}, want 0x{want_d:08X}")
                return False
            checks += 1

            if checks == 0:
                self.log.error("  no checks performed -- vacuous pass refused")
                return False
            self.log.info(f"seam programmed values GREEN ({checks} checks, "
                          f"addr 0x{w['paddr']:08X} data 0x{w['pwdata']:08X})")
            return True
        except Exception as e:
            self.log.error(f"programmed-values test error: {e}")
            return False

    # ------------------------------------------------------------------
    # func
    # ------------------------------------------------------------------
    async def test_message_fields_overwrite_the_template(self) -> bool:
        """Vector, delivery mode and destination mode land in the data word."""
        self.log.info("=== seam: message fields overwrite the template ===")
        try:
            template = 0xABCD_F000      # high bits must survive untouched
            cases = [
                (0x20, 0x01, IOAPICRegisterMap.DELIV_MODE_FIXED, 0),
                (0x7F, 0x03, IOAPICRegisterMap.DELIV_MODE_LOWPRI, 0),
                (0xC3, 0x08, IOAPICRegisterMap.DELIV_MODE_FIXED, 1),
            ]
            checks = 0
            for vector, dest, deliv_mode, dest_mode in cases:
                await self._arm(irq=5, vector=vector, dest=dest,
                                deliv_mode=deliv_mode, dest_mode=dest_mode,
                                msi_addr=MSI_ADDR_GOOD, msi_data=template)
                await self.tb.pulse_irq(5)
                writes = await self.tb.observe_msi_writes(200)
                if not writes:
                    self.log.error(f"  vector 0x{vector:02X}: no write observed")
                    return False
                w = writes[0]
                want_a = expected_addr(MSI_ADDR_GOOD, dest)
                want_d = expected_data(template, vector, deliv_mode, dest_mode)
                if w['paddr'] != want_a or w['pwdata'] != want_d:
                    self.log.error(
                        f"  vector 0x{vector:02X}: got addr 0x{w['paddr']:08X} "
                        f"data 0x{w['pwdata']:08X}, want addr 0x{want_a:08X} "
                        f"data 0x{want_d:08X}")
                    return False
                # The template's high bits are the point of a template.
                if (w['pwdata'] & 0xFFFF_F000) != (template & 0xFFFF_F000):
                    self.log.error("  template high bits were not preserved")
                    return False
                checks += 1
                self.log.info(f"  vector 0x{vector:02X} dest 0x{dest:02X} "
                              f"mode {deliv_mode}: correct")
            if checks == 0:
                self.log.error("  no checks performed -- vacuous pass refused")
                return False
            self.log.info(f"seam field mapping GREEN ({checks} checks)")
            return True
        except Exception as e:
            self.log.error(f"field-mapping test error: {e}")
            return False

    async def test_reprogramming_retargets_the_write(self) -> bool:
        """Rewriting IOAPICMSIADDR moves where the next MSI goes.

        Nothing else in the suite covers this, and it is exactly what a
        parameter could not do. If the address were still elaboration-time
        this test could not be written.
        """
        self.log.info("=== seam: reprogramming retargets the write ===")
        try:
            vector, dest = 0x33, 0x01
            first, second = 0x0000_0040, 0x0000_0080
            checks = 0
            for base in (first, second):
                await self._arm(irq=6, vector=vector, dest=dest,
                                deliv_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                                dest_mode=0, msi_addr=base, msi_data=0)
                await self.tb.pulse_irq(6)
                writes = await self.tb.observe_msi_writes(200)
                if not writes:
                    self.log.error(f"  base 0x{base:08X}: no write observed")
                    return False
                want_a = expected_addr(base, dest)
                if writes[0]['paddr'] != want_a:
                    self.log.error(
                        f"  base 0x{base:08X}: wrote to 0x{writes[0]['paddr']:08X}, "
                        f"want 0x{want_a:08X}")
                    return False
                checks += 1
                self.log.info(f"  base 0x{base:08X}: targeted correctly")
            if checks < 2:
                self.log.error("  fewer than two targets compared -- "
                               "retargeting was not actually shown")
                return False
            self.log.info(f"seam retargeting GREEN ({checks} checks)")
            return True
        except Exception as e:
            self.log.error(f"retargeting test error: {e}")
            return False

    # ------------------------------------------------------------------
    # full
    # ------------------------------------------------------------------
    async def test_pslverr_reaches_the_emitter_as_retry(self) -> bool:
        """A refused MSI write becomes deliv_retry -- which nothing can act on.

        MSI_ADDR_BAD is out of range for the 100-line slave, so it answers
        PSLVERR and the emitter raises deliv_retry. That much is proved here
        against a REAL slave and a REAL master; formal could not show it,
        because rsp_data is anyseq there.

        What this test does NOT assert is a re-offer, because under posted
        timing there cannot be one, and the reason is structural:

            ioapic_msi_emit.sv:144   deliv_ready = cmd_ready
            ioapic_msi_emit.sv:159   deliv_retry = rsp_valid && pslverr
            ioapic_core.sv:357-358   w_deliv_done   = r_out_valid && irq_out_ready
                                     w_deliv_accept = w_deliv_done && !irq_out_retry

        cmd_ready comes from apb4_master's cmd FIFO, so the delivery handshake
        closes when the write is QUEUED. The bus response -- and therefore
        deliv_retry -- arrives strictly later. ioapic_core samples retry AT the
        handshake, where it is always 0, so the edge is always retired as
        accepted and the later retry pulse is gated away by the w_deliv_done
        term. Measured: handshakes=1, retry_asserts=1, retry_at_handshake=0.

        deliv_retry is therefore inert in the posted configuration. That is a
        consequence of the posted timing decision (Sean, 2026-09-14), not a
        coding error, and which way to resolve it is an OPEN QUESTION recorded
        in RLB-008. Asserting the absence of a re-offer here would freeze the
        current behaviour into a contract, so this test asserts only what is
        genuinely true and logs the gap with its measurement.
        """
        self.log.info("=== seam: PSLVERR reaches the emitter as retry ===")
        try:
            vector, dest = 0x6A, 0x01
            await self._arm(irq=7, vector=vector, dest=dest,
                            deliv_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                            dest_mode=0, msi_addr=MSI_ADDR_BAD, msi_data=0)
            await self.tb.pulse_irq(7)
            writes = await self.tb.observe_msi_writes(400)
            if not writes:
                self.log.error("  no write reached the slave at all")
                return False

            checks = 0
            want_a = expected_addr(MSI_ADDR_BAD, dest)
            if writes[0]['paddr'] != want_a:
                self.log.error(
                    f"  wrote to 0x{writes[0]['paddr']:08X}, want the refused "
                    f"address 0x{want_a:08X}")
                return False
            checks += 1

            if not writes[0]['pslverr']:
                self.log.error(
                    "  the slave did not answer PSLVERR -- the address was not "
                    "actually refused, so the refusal path was never exercised")
                return False
            checks += 1

            if self.tb.retry_asserts < 1:
                self.log.error(
                    "  PSLVERR came back but deliv_retry never asserted -- the "
                    "emitter's refusal path is broken")
                return False
            checks += 1

            if checks == 0:
                self.log.error("  no checks performed -- vacuous pass refused")
                return False

            # The gap, measured rather than assumed. Not an assertion: see the
            # docstring. If this ever becomes non-zero the design changed and
            # RLB-008's open question has been answered.
            if self.tb.retry_at_handshake == 0:
                self.log.warning(
                    "  RLB-008 posted-timing gap: deliv_retry asserted "
                    f"{self.tb.retry_asserts} time(s) but NEVER at the delivery "
                    "handshake, so ioapic_core retired the edge as accepted "
                    "and the refused MSI is not re-offered. deliv_retry is "
                    "inert while the write is posted.")
            else:
                self.log.info(
                    f"  retry coincided with the handshake "
                    f"{self.tb.retry_at_handshake} time(s) -- the design now "
                    "supports re-offer; RLB-008 should be updated.")

            self.log.info(f"seam PSLVERR-to-retry GREEN ({checks} checks, "
                          f"retry_asserts={self.tb.retry_asserts}, "
                          f"retry_at_handshake={self.tb.retry_at_handshake})")
            return True
        except Exception as e:
            self.log.error(f"PSLVERR-to-retry test error: {e}")
            return False

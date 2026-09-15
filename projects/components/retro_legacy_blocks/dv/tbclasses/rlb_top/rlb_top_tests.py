# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rlb_top_tests
# Purpose: Light integration smoke tests for the RLB subsystem (rlb_top).
#
# Created: 2026-09-14

"""What these tests are for, and what they deliberately do NOT do.

Each of the nine blocks has its own suite -- 75 cells across the area -- and
none of it is repeated here. These tests cover only what no per-block test
can see: that the blocks are WIRED UP. Until now nothing elaborated rlb_top,
so a port could be added to a block and left unconnected here while the suite
stayed green. That is precisely how two PINMISSING breaks reached the tree.

READ SAFETY drove the choice of probe register, not convenience. Reading UART
offset 0x000 POPS THE RX FIFO, so the UART is probed at its scratch register
(0x020, "no hardware function") instead. The others are probed at their inert
config register.

WRITE SAFETY likewise. The isolation sweep writes only registers whose RDL
shows plain `sw = rw` storage with no singlepulse/woclr/onwrite property and
no `hw = w`/`hw = rw` -- hardware must not be able to overwrite what software
put there, or the read-back proves nothing. HPET and PIT are READ-ONLY here:
PIT has no inert writable register at all, and HPET's only one lives inside a
timer sub-block. Writing SMBus COMMAND or the PIC's ICW sequence would start
real transactions rather than test address decode.

AN UNMAPPED ADDRESS IS NOW TESTED, and the history is the point. This file
used to say the case was deliberately untestable: the hand-written crossbar
drove m_cmd_ready only when addr_in_range, so an out-of-range access was never
accepted, apb4_slave never left IDLE, PREADY never asserted, and with no
timeout in that path and an unbounded BFM completion loop, probing it would
hang until the cocotb timeout killed the run. That was true of the crossbar
that shipped then (RLB-016).

It is no longer true of the DUT. rlb_top now instantiates the GENERATED
apbx_xbar_1to10, which carries the apbx-xbar family's decode-miss agent: an
unmapped access is accepted and answered locally with PSLVERR. So the case
became reachable through the BFM, and test_unmapped_address_errors encodes it
rather than leaving it as a written-down finding.
"""

from cocotb.triggers import ClockCycles


class RLBTopTests:
    """Integration smoke tests for rlb_top."""

    def __init__(self, tb):
        self.tb = tb
        self.log = tb.log

    # ------------------------------------------------------------------
    # gate
    # ------------------------------------------------------------------
    async def test_every_window_answers(self) -> bool:
        """Every peripheral window decodes to a live slave that answers.

        The point is presence and routing, not behaviour: a window whose
        slave is unwired, mis-decoded or absent either errors or never
        completes, and both are failures here.
        """
        self.log.info("=== smoke: every window answers ===")
        try:
            checks = 0
            for name, (slave, offset) in self.tb.PROBE.items():
                addr = self.tb.window_addr(slave, offset)
                _, value, slverr = await self.tb.apb_read(addr)
                if slverr:
                    self.log.error(
                        f"  {name} (window {slave}, 0x{addr:08X}): PSLVERR -- "
                        "the window decoded but its slave refused the access")
                    return False
                checks += 1
                self.log.info(f"  {name:9s} window {slave} @ 0x{addr:08X} "
                              f"-> 0x{value:08X}")
            if checks != len(self.tb.PROBE):
                self.log.error(
                    f"  only {checks} of {len(self.tb.PROBE)} windows probed")
                return False
            self.log.info(f"smoke every-window GREEN ({checks} checks)")
            return True
        except Exception as e:
            self.log.error(f"every-window test error: {e}")
            return False

    # ------------------------------------------------------------------
    # func
    # ------------------------------------------------------------------
    async def test_reserved_window_errors(self) -> bool:
        """Window 9 is reserved: it answers, and it answers with an error.

        rlb_top ties that port to PRDATA=0xDEADBEEF, PSLVERR=1, PREADY=1. It
        matters that it READY-s at all: a reserved window that simply never
        responded would hang the bus rather than report a bad access.
        """
        self.log.info("=== smoke: reserved window errors ===")
        try:
            addr = self.tb.window_addr(self.tb.SLAVE_RESERVED, 0x000)
            _, value, slverr = await self.tb.apb_read(addr)
            checks = 0
            if not slverr:
                self.log.error(
                    f"  reserved window returned PSLVERR=0 (data 0x{value:08X}) "
                    "-- a reserved access must be reported, not silently served")
                return False
            checks += 1
            if value != 0xDEADBEEF:
                self.log.error(
                    f"  reserved window data 0x{value:08X}, want 0xDEADBEEF")
                return False
            checks += 1
            self.log.info(f"smoke reserved-window GREEN ({checks} checks, "
                          f"0x{value:08X} with PSLVERR)")
            return True
        except Exception as e:
            self.log.error(f"reserved-window test error: {e}")
            return False

    async def test_unmapped_address_errors(self) -> bool:
        """An address outside the 40KB map completes, with PSLVERR.

        This is the behaviour RLB-016 recorded as missing, and it is the whole
        reason rlb_top moved onto the generated crossbar. The decode-miss agent
        accepts the miss and answers it locally rather than leaving the master
        stalled in ACCESS with PREADY low and no error signature.

        The SECOND half matters as much as the first. The miss is tracked by a
        SINGLE pending bit (r_m0_decerr_pending), so if it ever failed to clear
        it would poison every later access on the bus. A normal read afterwards
        is what proves it cleared -- without it this test would pass against a
        crossbar that errors permanently after the first unmapped access.
        """
        self.log.info("=== smoke: unmapped address errors ===")
        try:
            checks = 0
            # addr_in_range is (paddr >= BASE) && (paddr < BASE + 40KB), so it
            # has TWO failing edges and both are probed here. Testing only the
            # upper one would leave the `>= BASE` half unexercised, which is
            # exactly where an off-by-one or a signedness slip would hide. The
            # family's own APB-2TO4-21 scenario probes both edges for the same
            # reason. Slave 9 is the last mapped window and ends at BASE+0x9FFF,
            # so window_addr(10, 0) is the first unmapped address above it.
            probes = (
                (self.tb.BASE_ADDR - 4,          "just below the map"),
                (self.tb.window_addr(10, 0x000), "first address past the map"),
                (self.tb.window_addr(15, 0x000), "well past the map"),
            )
            for addr, label in probes:
                _, value, slverr = await self.tb.apb_read(addr)
                if not slverr:
                    self.log.error(
                        f"  unmapped 0x{addr:08X} ({label}) returned PSLVERR=0 "
                        f"(data 0x{value:08X}) -- an unmapped access must be "
                        "reported, not silently served")
                    return False
                checks += 1
                self.log.info(f"  unmapped 0x{addr:08X} -> PSLVERR ({label})")

            probe = self.tb.window_addr(self.tb.SLAVE_HPET, 0x000)
            _, value, slverr = await self.tb.apb_read(probe)
            if slverr:
                self.log.error(
                    f"  HPET read after a decode miss returned PSLVERR=1 "
                    f"(data 0x{value:08X}) -- the decode-error flag did not "
                    "clear, so one unmapped access poisoned the bus")
                return False
            checks += 1
            self.log.info(f"  bus still healthy after the miss "
                          f"(HPET 0x{value:08X}, PSLVERR=0)")

            self.log.info(f"smoke unmapped-address GREEN ({checks} checks)")
            return True
        except Exception as e:
            self.log.error(f"unmapped-address test error: {e}")
            return False

    async def test_decode_isolation(self) -> bool:
        """A write to one window lands in that window and nowhere else.

        Every writable block gets a DISTINCT value at the same moment, and
        then all of them are read back. A decode that aliased two windows
        would show one block holding another's value -- which a
        write-then-read-immediately test would miss entirely, because it
        never has two live values in flight at once.
        """
        self.log.info("=== smoke: decode isolation ===")
        try:
            written = {}
            for i, (name, (slave, offset)) in enumerate(self.tb.WRITABLE.items()):
                val = self.tb.isolation_value(name, i)
                addr = self.tb.window_addr(slave, offset)
                await self.tb.apb_write(addr, val)
                written[name] = (addr, val)
                self.log.info(f"  wrote 0x{val:08X} -> {name} @ 0x{addr:08X}")

            checks = 0
            for name, (addr, val) in written.items():
                _, got, slverr = await self.tb.apb_read(addr)
                if slverr:
                    self.log.error(f"  {name}: PSLVERR on read-back")
                    return False
                # Compare only the bits the register actually implements --
                # reserved bits read 0 and that is not a decode failure.
                mask = self.tb.WRITE_MASK[name]
                if (got & mask) != (val & mask):
                    self.log.error(
                        f"  {name} @ 0x{addr:08X}: read 0x{got:08X}, wrote "
                        f"0x{val:08X} (mask 0x{mask:08X}) -- windows alias, or "
                        "the write did not reach this block")
                    return False
                checks += 1
                self.log.info(f"  {name:9s} held its own value 0x{got & mask:08X}")

            # CROSS-WINDOW NEGATIVE CHECK. The read-backs above prove each
            # window reaches storage that holds its own value -- but NOT that
            # the windows are distinct, because the three probe registers sit
            # at three DIFFERENT offsets (0x000, 0x010, 0x020). An alias of
            # window 8 onto 7 would send the UART write to gpio+0x020 and the
            # GPIO write to gpio+0x010, so both still read back correctly and
            # the check above passes. Found by trying to build a mutation
            # that the test could not catch.
            #
            # So: read each written OFFSET through a DIFFERENT window and
            # require it NOT to hold that value. Under an alias it would.
            names = list(written)
            for a in names:
                addr_a, val_a = written[a]
                off_a = addr_a & (self.tb.WINDOW - 1)
                for b in names:
                    if b == a:
                        continue
                    slave_b = self.tb.WRITABLE[b][0]
                    probe = self.tb.window_addr(slave_b, off_a)
                    _, got, slverr = await self.tb.apb_read(probe)
                    if slverr:
                        continue          # that offset is not implemented there
                    if (got & self.tb.WRITE_MASK[a]) == (val_a & self.tb.WRITE_MASK[a]):
                        self.log.error(
                            f"  {a}'s value 0x{val_a:02X} is visible at "
                            f"0x{probe:08X}, inside {b}'s window -- the two "
                            "windows alias")
                        return False
                    checks += 1

            if checks < 2:
                self.log.error(
                    "  fewer than two windows compared -- isolation was not "
                    "actually demonstrated")
                return False
            self.log.info(f"smoke decode-isolation GREEN ({checks} checks)")
            return True
        except Exception as e:
            self.log.error(f"decode-isolation test error: {e}")
            return False

    # ------------------------------------------------------------------
    # full
    # ------------------------------------------------------------------
    async def test_boot_interrupt_reaches_the_pic(self) -> bool:
        """A masked IOAPIC pin reaches the 8259 through ioapic_boot_intx.

        This is the only cross-block path in the subsystem, and no per-block
        suite can see it: the IOAPIC exports the mask, the companion
        reroutes, and the 8259 sees it on the same input a board would have
        driven directly.

        EACH PHASE RESETS FIRST. In edge mode the 8259 LATCHES int_out high
        until it is cleared, so without a reset between phases the second and
        third observations would be reading the first pulse's assertion --
        the "disabled" check would then pass or fail for entirely the wrong
        reason. Reset is used rather than an acknowledge because the
        acknowledge/EOI paths are what pic_8259's own C3/C4 tests document as
        expected-RED; an integration smoke test must not depend on them.

        A BASELINE comes first, driving pic_irq_in directly. If the PIC will
        not assert INT even for a direct IRQ, that step says so plainly
        instead of the reroute step failing for an unrelated reason.
        """
        self.log.info("=== smoke: boot interrupt reaches the 8259 ===")
        try:
            irq = 3
            checks = 0

            # --- baseline: the PIC responds to a direct IRQ at all
            if not await self.tb.reset_and_init_pic():
                self.log.error("  PIC initialisation failed; cannot proceed")
                return False
            if self.tb.pic_int_out():
                self.log.error("  pic_int_out already high after reset+init")
                return False
            if not await self.tb.pulse_pic_irq(irq):
                self.log.error(
                    f"  BASELINE FAILED: pic_irq_in[{irq}] driven directly did "
                    "not raise pic_int_out even with the PIC initialised")
                return False
            checks += 1
            self.log.info("  baseline: a direct IRQ raises pic_int_out")

            # --- the rerouted path, with pic_irq_in left idle throughout
            if not await self.tb.reset_and_init_pic():
                self.log.error("  PIC re-init failed before the reroute phase")
                return False
            if self.tb.pic_int_out():
                self.log.error("  pic_int_out did not clear across the reset")
                return False
            await self.tb.arm_ioapic_pin(irq, masked=True, boot_intx_en=True)
            if not await self.tb.pulse_ioapic_irq(irq):
                self.log.error(
                    f"  a MASKED IOAPIC pin {irq} with boot-interrupt enabled "
                    "did not reach pic_int_out -- the reroute path is broken")
                return False
            checks += 1
            self.log.info("  masked IOAPIC pin reaches pic_int_out")

            # --- and it is the ENABLE doing it, not the wiring alone
            if not await self.tb.reset_and_init_pic():
                self.log.error("  PIC re-init failed before the disabled phase")
                return False
            await self.tb.arm_ioapic_pin(irq, masked=True, boot_intx_en=False)
            if await self.tb.pulse_ioapic_irq(irq):
                self.log.error(
                    "  with boot-interrupt DISABLED the pin still reached the "
                    "PIC -- the enable gates nothing")
                return False
            checks += 1
            self.log.info("  disabled: the same pin reaches nothing")

            if checks != 3:
                self.log.error(f"  only {checks} of 3 phases ran")
                return False
            self.log.info(f"smoke boot-interrupt GREEN ({checks} checks)")
            return True
        except Exception as e:
            self.log.error(f"boot-interrupt test error: {e}")
            return False

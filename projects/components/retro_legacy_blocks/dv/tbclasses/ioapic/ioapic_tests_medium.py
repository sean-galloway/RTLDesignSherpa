# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: IOAPICMediumTests
# Purpose: GitHub #48 defect-regression suite for IOAPIC
#
# Created: 2026-09-09

"""
IOAPIC GitHub #48 Defect-Regression Test Suite

These tests encode the Intel 82093AA-style IOAPIC contract that GitHub
issue #48 (body + qc round_1/round_2/round_3 comments) found the original
RTL did not meet: exactly one delivery per edge, per-pin Remote IRR blocking
instead of a global in-service wait, EOI matched against the delivered
vector, a single IOREGSEL copy, and only IOREGSEL/IOWIN decoded on the APB.
History: they were written RED against the pre-fix RTL (2026-09-09) and are
kept as the regression for that fix.

Each test starts from IOAPICTB.reset_dut() rather than
drain_pending_interrupts(). The basic-suite helper drain_pending_interrupts()
and wait_for_interrupt() (which captures only the FIRST valid/ready handshake
and never checks for a second one) were the mechanisms that let the basic
suite pass against the original double-delivery defect; the per-test
docstrings here name which existing tests/helpers masked which defect. The
scenarios that once wedged the retired global delivery FSM now prove that
other pins keep delivering while one pin is in service.

Defect index (GitHub #48):
  1. C1 - edge-triggered IRQ delivered twice (delayed pending-clear allows a
     spurious re-arbitration window); a subsequent single ready pulse then
     leaves irq_out_valid parked for a pending bit that has already cleared.
  2. Per-pin level blocking - ONE global delivery_state FSM means a level IRQ
     sitting in WAIT_EOI (no EOI sent yet) blocks ALL other IRQs, not just
     its own pin.
  3. A lost/wrong-vector EOI stalls delivery for every IRQ, not just the one
     that was never EOI'd (same single-engine root cause as #2).
  4. An EOI landing while a level IRQ is still in DELIVER (before ready is
     granted) clears Remote IRR early via an unqualified vector compare, then
     wedges WAIT_EOI forever because software's one EOI has already been
     consumed.
  5. The Remote IRR clear compares eoi_vector against the LIVE cfg_vector,
     not the vector actually delivered - rewriting an RTE's vector between
     delivery and EOI permanently blocks that pin.
  6. Two divergent IOREGSEL copies (translation shadow vs. PeakRDL regblock
     field) - an invalid-selector IOWIN access corrupts only the readback
     copy, so IOREGSEL readback can diverge from the selector actually in
     effect for indirect-access translation.
  7/8. regblk_addr[8:0] into an 8-bit s_cpuif_addr with only address 0x004
     specially decoded means every APB address >= 0x100 aliases onto the
     register file modulo 0x100 (and the alias reads are defined 0, not X,
     in this 2-state Verilator build).

Item 9 (no CDC synchronizer on eoi_in/eoi_vector) is exercised by
test_cdc_eoi_single_pclk_cycle_honored() below but is NOT expected to go RED
with the runner's mandated CDC clock ratio (pclk=10ns, ioapic_clk=7ns,
ioapic_clk FASTER than pclk, matching gpio_tb.py's TEST_GPIO_CLOCK_PERIOD
precedent): a 10ns-wide single-pclk-cycle EOI pulse always straddles at least
one 7ns ioapic_clk edge, so a zero-delay, 2-state Verilator simulation cannot
show the pulse being lost or metastable - that is a real-silicon CDC risk,
not a value the digital model can produce. See that test's docstring.
"""

from .ioapic_tb import IOAPICRegisterMap


class IOAPICMediumTests:
    """GitHub #48 defect-regression suite for IOAPIC (medium/full levels)."""

    def __init__(self, tb):
        """
        Args:
            tb: IOAPICTB instance
        """
        self.tb = tb
        self.log = tb.log

    # =========================================================================
    # Defect 1 (C1): edge-triggered IRQ delivered twice
    # =========================================================================

    async def test_c1_edge_double_delivery_count(self) -> bool:
        """
        GitHub #48 C1: with irq_out_ready held asserted continuously, a
        single edge-triggered IRQ pulse must produce exactly ONE
        irq_out_valid&irq_out_ready handshake for its vector.

        wait_for_interrupt() cannot expose this: it returns True on the
        FIRST handshake and never looks for a second one, which is exactly
        how every existing basic-suite edge-interrupt test (test 4, test 9,
        test 11, ...) passes today despite C1.
        """
        self.log.info("TEST MED-1: C1 edge double-delivery count")

        try:
            await self.tb.reset_dut()

            test_vector = 0x30
            await self.tb.write_redirection_entry(
                irq=2, vector=test_vector, dest=0x01,
                delivery_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                dest_mode=0, polarity=0, trigger_mode=0, mask=0
            )
            await self.tb.wait_clocks('pclk', 5)

            await self.tb.pulse_irq(2, pulse_cycles=3)

            # Hold ready high for a generous window and count EVERY
            # valid&ready handshake for this vector, not just the first.
            handshakes = await self.tb.count_irq_out_handshakes(
                window_cycles=20, ready=1, vector_filter=test_vector)

            self.tb.dut.irq_out_ready.value = 0

            if len(handshakes) != 1:
                self.log.error(
                    f"C1 double-delivery: expected exactly 1 delivery of "
                    f"vector 0x{test_vector:02X}, observed "
                    f"{len(handshakes)} within a 20-cycle window with "
                    f"irq_out_ready held high"
                )
                return False

            self.log.info("PASS: edge IRQ delivered exactly once")
            return True

        except Exception as e:
            self.log.error(f"FAIL: C1 double-delivery test raised {e}")
            return False

    async def test_c1_no_park_after_single_ready_pulse(self) -> bool:
        """
        GitHub #48 C1 (second half): if irq_out_ready is pulsed for exactly
        one cycle (real ack behaviour) and then held low, irq_out_valid must
        not remain parked asserted once the pending bit has actually
        cleared - it must not wait on a spurious second delivery that will
        never be acknowledged.
        """
        self.log.info("TEST MED-2: C1 no park after single ready pulse")

        try:
            await self.tb.reset_dut()

            test_vector = 0x31
            await self.tb.write_redirection_entry(
                irq=3, vector=test_vector, dest=0x01,
                delivery_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                dest_mode=0, polarity=0, trigger_mode=0, mask=0
            )
            await self.tb.wait_clocks('pclk', 5)

            await self.tb.pulse_irq(3, pulse_cycles=3)

            delivered = await self.tb.wait_for_interrupt(timeout_cycles=20)
            if not delivered:
                self.log.error("No interrupt delivered for IRQ3 at all")
                return False

            _, vector, _ = await self.tb.get_interrupt_delivery()
            if vector != test_vector:
                self.log.error(
                    f"Wrong vector delivered: expected 0x{test_vector:02X}, "
                    f"got 0x{vector:02X}")
                return False

            # irq_out_ready is already low again (wait_for_interrupt pulses
            # it for one cycle). Give the DUT plenty of time to settle with
            # no further stimulus.
            await self.tb.wait_clocks('pclk', 20)

            if self.tb.dut.irq_out_valid.value == 1:
                self.log.error(
                    "irq_out_valid is still asserted 20 cycles after the "
                    "only ready pulse acknowledged the only pending edge - "
                    "the pending bit is clear but irq_out_valid is parked"
                )
                return False

            self.log.info("PASS: irq_out_valid deasserted, no park")
            return True

        except Exception as e:
            self.log.error(f"FAIL: no-park test raised {e}")
            return False

    # =========================================================================
    # Defects 2/3/4/5: single global engine blocking / wedging
    # =========================================================================

    async def test_per_pin_block_edge_b_and_eoi_redelivery(self) -> bool:
        """
        GitHub #48 qc round_2 item 3 / round_3 item 1: a level IRQ A left
        un-EOI'd (Remote IRR set) must block only ITS OWN pin, not an
        unrelated edge IRQ B. Then EOI(A) while A's input is still asserted
        must redeliver A exactly once.
        """
        self.log.info("TEST MED-3: per-pin block (edge B) + EOI redelivery")

        try:
            await self.tb.reset_dut()

            vec_a, vec_b = 0x32, 0x33
            await self.tb.write_redirection_entry(
                irq=4, vector=vec_a, dest=0x01,
                delivery_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                dest_mode=0, polarity=0, trigger_mode=1, mask=0)  # level
            await self.tb.write_redirection_entry(
                irq=5, vector=vec_b, dest=0x01,
                delivery_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                dest_mode=0, polarity=0, trigger_mode=0, mask=0)  # edge
            await self.tb.wait_clocks('pclk', 5)

            # Deliver level IRQ A and deliberately withhold EOI.
            await self.tb.assert_irq(4)
            delivered_a = await self.tb.wait_for_interrupt(timeout_cycles=30)
            if not delivered_a:
                self.log.error("Level IRQ A(4) was never delivered")
                return False
            _, vec, _ = await self.tb.get_interrupt_delivery()
            if vec != vec_a:
                self.log.error(f"Wrong vector for A: expected 0x{vec_a:02X}, got 0x{vec:02X}")
                return False

            # A is now in-service (Remote IRR set), no EOI has been sent.
            await self.tb.pulse_irq(5, pulse_cycles=3)
            delivered_b = await self.tb.wait_for_interrupt(timeout_cycles=40)

            if not delivered_b:
                self.log.error(
                    "Edge IRQ B(5) was NOT delivered while level IRQ A(4) "
                    "sat un-EOI'd in WAIT_EOI - the single global delivery "
                    "engine is blocking an unrelated pin instead of "
                    "blocking only A's own pin"
                )
                return False

            _, vec, _ = await self.tb.get_interrupt_delivery()
            if vec != vec_b:
                self.log.error(f"Wrong vector for B: expected 0x{vec_b:02X}, got 0x{vec:02X}")
                return False

            # EOI(A) while A's input is still asserted - must redeliver
            # exactly once.
            await self.tb.send_eoi(vec_a)
            handshakes = await self.tb.count_irq_out_handshakes(
                window_cycles=30, ready=1, vector_filter=vec_a)
            self.tb.dut.irq_out_ready.value = 0

            if len(handshakes) != 1:
                self.log.error(
                    f"EOI(A) with A still asserted: expected exactly 1 "
                    f"redelivery of vector 0x{vec_a:02X}, observed "
                    f"{len(handshakes)}"
                )
                return False

            await self.tb.deassert_irq(4)
            await self.tb.send_eoi(vec_a)
            await self.tb.wait_clocks('pclk', 5)

            self.log.info("PASS: IRQ B delivered while A awaited EOI; A redelivered once")
            return True

        except Exception as e:
            self.log.error(f"FAIL: per-pin-block(edge B) test raised {e}")
            return False

    async def test_per_pin_block_level_b_and_eoi_clears(self) -> bool:
        """
        GitHub #48 qc round_2 item 3: same per-pin-blocking scenario as
        above, with B as a LEVEL IRQ instead of edge. Then EOI(A) with A's
        input deasserted first must clear Remote IRR and deliver nothing
        further for A.
        """
        self.log.info("TEST MED-4: per-pin block (level B) + EOI clears")

        try:
            await self.tb.reset_dut()

            vec_a, vec_b = 0x34, 0x35
            await self.tb.write_redirection_entry(
                irq=6, vector=vec_a, dest=0x01,
                delivery_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                dest_mode=0, polarity=0, trigger_mode=1, mask=0)  # level
            await self.tb.write_redirection_entry(
                irq=7, vector=vec_b, dest=0x01,
                delivery_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                dest_mode=0, polarity=0, trigger_mode=1, mask=0)  # level
            await self.tb.wait_clocks('pclk', 5)

            await self.tb.assert_irq(6)
            delivered_a = await self.tb.wait_for_interrupt(timeout_cycles=30)
            if not delivered_a:
                self.log.error("Level IRQ A(6) was never delivered")
                return False

            await self.tb.assert_irq(7)
            delivered_b = await self.tb.wait_for_interrupt(timeout_cycles=40)

            if not delivered_b:
                self.log.error(
                    "Level IRQ B(7) was NOT delivered while level IRQ A(6) "
                    "sat un-EOI'd in WAIT_EOI - single global engine "
                    "blocking an unrelated pin (level-B variant)"
                )
                return False

            _, vec, _ = await self.tb.get_interrupt_delivery()
            if vec != vec_b:
                self.log.error(f"Wrong vector for B: expected 0x{vec_b:02X}, got 0x{vec:02X}")
                return False

            # Deassert A's input BEFORE EOI'ing it: Remote IRR must clear and
            # nothing further must be delivered for A.
            await self.tb.deassert_irq(6)
            await self.tb.wait_clocks('pclk', 5)
            await self.tb.send_eoi(vec_a)
            await self.tb.wait_clocks('pclk', 10)

            remote_irr_a = await self.tb.read_remote_irr(6)
            if remote_irr_a != 0:
                self.log.error(f"Remote IRR for A(6) still set after EOI with input deasserted")
                return False

            if self.tb.dut.irq_out_valid.value == 1:
                vec_now = self.tb.dut.irq_out_vector.value.integer
                if vec_now == vec_a:
                    self.log.error(f"IRQ A(6) redelivered after EOI despite input being deasserted")
                    return False

            # Clean up B.
            await self.tb.send_eoi(vec_b)
            await self.tb.deassert_irq(7)

            self.log.info("PASS: level IRQ B delivered while A awaited EOI; A cleanly cleared")
            return True

        except Exception as e:
            self.log.error(f"FAIL: per-pin-block(level B) test raised {e}")
            return False

    async def test_wrong_vector_eoi_does_not_stall_b(self) -> bool:
        """
        GitHub #48 qc round_3 item 1: an EOI for a vector that matches NO
        configured RTE (a lost or simply wrong EOI) must not stall delivery
        for every other IRQ - only A's own pin should be affected.
        """
        self.log.info("TEST MED-5: wrong-vector EOI does not stall B")

        try:
            await self.tb.reset_dut()

            vec_a, vec_b = 0x36, 0x37
            nonexistent_vector = 0xEE

            await self.tb.write_redirection_entry(
                irq=8, vector=vec_a, dest=0x01,
                delivery_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                dest_mode=0, polarity=0, trigger_mode=1, mask=0)  # level
            await self.tb.write_redirection_entry(
                irq=9, vector=vec_b, dest=0x01,
                delivery_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                dest_mode=0, polarity=0, trigger_mode=0, mask=0)  # edge
            await self.tb.wait_clocks('pclk', 5)

            await self.tb.assert_irq(8)
            delivered_a = await self.tb.wait_for_interrupt(timeout_cycles=30)
            if not delivered_a:
                self.log.error("Level IRQ A(8) was never delivered")
                return False

            # EOI with a vector that matches nothing configured.
            await self.tb.send_eoi(nonexistent_vector)
            await self.tb.wait_clocks('pclk', 5)

            await self.tb.pulse_irq(9, pulse_cycles=3)
            delivered_b = await self.tb.wait_for_interrupt(timeout_cycles=40)

            if not delivered_b:
                self.log.error(
                    f"Edge IRQ B(9) was NOT delivered after a wrong-vector "
                    f"EOI(0x{nonexistent_vector:02X}) - the single global "
                    f"engine is wedged in WAIT_EOI for A and blocks B too"
                )
                return False

            _, vec, _ = await self.tb.get_interrupt_delivery()
            if vec != vec_b:
                self.log.error(f"Wrong vector for B: expected 0x{vec_b:02X}, got 0x{vec:02X}")
                return False

            await self.tb.deassert_irq(8)
            await self.tb.send_eoi(vec_a)

            self.log.info("PASS: IRQ B delivered despite a wrong-vector EOI for A")
            return True

        except Exception as e:
            self.log.error(f"FAIL: wrong-vector-EOI test raised {e}")
            return False

    async def test_eoi_during_deliver_does_not_wedge(self) -> bool:
        """
        GitHub #48 qc round_2 item 3: an EOI for a level IRQ landing WHILE
        it is still in DELIVER (before irq_out_ready is granted) clears
        Remote IRR early via the unqualified `eoi_in &&
        eoi_vector==cfg_vector[i]` compare. The FSM still transitions
        DELIVER->WAIT_EOI once ready is later granted, but software's one
        EOI has already been consumed, so no new eoi_in pulse ever arrives
        and the single global engine wedges in WAIT_EOI forever - blocking
        an unrelated edge IRQ B too.

        Swept over a small deterministic set of race offsets (cycles into
        DELIVER before the EOI lands) so the race point itself is
        reproducible without relying on a random seed.
        """
        self.log.info("TEST MED-6: EOI-during-DELIVER race does not wedge")

        try:
            deliver_offsets = [0, 1, 2, 3]

            for offset in deliver_offsets:
                await self.tb.reset_dut()

                vec_a, vec_b = 0x38, 0x39
                await self.tb.write_redirection_entry(
                    irq=10, vector=vec_a, dest=0x01,
                    delivery_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                    dest_mode=0, polarity=0, trigger_mode=1, mask=0)  # level
                await self.tb.write_redirection_entry(
                    irq=11, vector=vec_b, dest=0x01,
                    delivery_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                    dest_mode=0, polarity=0, trigger_mode=0, mask=0)  # edge
                await self.tb.wait_clocks('pclk', 5)

                await self.tb.assert_irq(10)

                # Poll for DELIVER (irq_out_valid asserted) without granting
                # ready, so we control exactly how long DELIVER persists.
                entered_deliver = False
                for _ in range(30):
                    await self.tb.wait_clocks('pclk', 1)
                    if self.tb.dut.irq_out_valid.value == 1:
                        entered_deliver = True
                        break
                if not entered_deliver:
                    self.log.error(f"[offset={offset}] IRQ A(10) never entered DELIVER")
                    return False

                # Race the EOI to land `offset` cycles into DELIVER.
                await self.tb.wait_clocks('pclk', offset)
                await self.tb.send_eoi(vec_a)

                # Now the CPU actually accepts the delivery.
                self.tb.dut.irq_out_ready.value = 1
                await self.tb.wait_clocks('pclk', 1)
                self.tb.dut.irq_out_ready.value = 0

                # An unrelated edge IRQ B must still be able to get through.
                await self.tb.pulse_irq(11, pulse_cycles=3)
                delivered_b = await self.tb.wait_for_interrupt(timeout_cycles=40)

                if not delivered_b:
                    self.log.error(
                        f"[offset={offset}] EOI raced into DELIVER wedged "
                        f"the engine in WAIT_EOI - unrelated edge IRQ B(11) "
                        f"was never delivered"
                    )
                    return False

                _, vec, _ = await self.tb.get_interrupt_delivery()
                if vec != vec_b:
                    self.log.error(
                        f"[offset={offset}] wrong vector for B: expected "
                        f"0x{vec_b:02X}, got 0x{vec:02X}")
                    return False

                await self.tb.deassert_irq(10)

            self.log.info(
                f"PASS: EOI-during-DELIVER race did not wedge the engine "
                f"at any offset in {deliver_offsets}")
            return True

        except Exception as e:
            self.log.error(f"FAIL: EOI-during-DELIVER test raised {e}")
            return False

    async def test_rte_vector_rewrite_mid_delivery(self) -> bool:
        """
        GitHub #48 qc round_1: the Remote IRR clear compares the LIVE
        cfg_vector against eoi_vector, not the vector actually delivered
        (current_vector, latched at delivery time). Rewriting an RTE's
        vector between delivery and EOI - a legal software sequence, e.g.
        IRQ rebalancing - then EOI'ing with the vector that was actually
        delivered (the old one) must still clear Remote IRR, and the NEW
        vector must be used for the next delivery.
        """
        self.log.info("TEST MED-7: RTE vector rewrite mid-delivery")

        try:
            await self.tb.reset_dut()

            irq = 12
            old_vector, new_vector = 0x3A, 0x3B

            await self.tb.write_redirection_entry(
                irq=irq, vector=old_vector, dest=0x01,
                delivery_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                dest_mode=0, polarity=0, trigger_mode=1, mask=0)  # level
            await self.tb.wait_clocks('pclk', 5)

            await self.tb.assert_irq(irq)
            delivered = await self.tb.wait_for_interrupt(timeout_cycles=30)
            if not delivered:
                self.log.error(f"Level IRQ{irq} was never delivered")
                return False
            _, vec, _ = await self.tb.get_interrupt_delivery()
            if vec != old_vector:
                self.log.error(f"Wrong vector delivered: expected 0x{old_vector:02X}, got 0x{vec:02X}")
                return False

            # In WAIT_EOI now. Rewrite the RTE's vector BEFORE EOI'ing -
            # legal software sequence.
            await self.tb.write_redirection_entry(
                irq=irq, vector=new_vector, dest=0x01,
                delivery_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                dest_mode=0, polarity=0, trigger_mode=1, mask=0)
            await self.tb.wait_clocks('pclk', 3)

            # EOI with the vector that was ACTUALLY delivered (the old one).
            await self.tb.send_eoi(old_vector)
            await self.tb.wait_clocks('pclk', 10)

            remote_irr = await self.tb.read_remote_irr(irq)
            if remote_irr != 0:
                self.log.error(
                    f"Remote IRR for IRQ{irq} still set after "
                    f"EOI(0x{old_vector:02X}) - the RTL compares eoi_vector "
                    f"against the LIVE cfg_vector (now 0x{new_vector:02X}), "
                    f"not the vector actually delivered, so the pin is "
                    f"permanently blocked"
                )
                return False

            # The IRQ input was never deasserted; level tracking should
            # already have re-armed pending now that Remote IRR is clear,
            # and it must use the NEW vector.
            delivered2 = await self.tb.wait_for_interrupt(timeout_cycles=30)
            if not delivered2:
                self.log.error(f"IRQ{irq} did not redeliver after Remote IRR cleared")
                return False
            _, vec2, _ = await self.tb.get_interrupt_delivery()
            if vec2 != new_vector:
                self.log.error(
                    f"Redelivery used the wrong vector: expected "
                    f"0x{new_vector:02X}, got 0x{vec2:02X}")
                return False

            await self.tb.send_eoi(new_vector)
            await self.tb.deassert_irq(irq)

            self.log.info("PASS: EOI with the delivered vector clears Remote IRR; new vector used next")
            return True

        except Exception as e:
            self.log.error(f"FAIL: RTE vector rewrite test raised {e}")
            return False

    # =========================================================================
    # Defect 6: two divergent IOREGSEL copies
    # =========================================================================

    async def test_ioregsel_invalid_selector_readback(self) -> bool:
        """
        GitHub #48 qc round_2 item 2: the functional address-translation
        shadow (ioregsel_value, in ioapic_config_regs.sv) and the PeakRDL
        register block's own IOREGSEL.regsel field are two separate copies.
        ioregsel_value is updated only by a DIRECT write to IOREGSEL (APB
        0x000); the regblock's copy is ALSO written whenever an invalid
        (unmapped) selector routes an IOWIN access to regblk_addr=0x000 -
        the same address the regblock uses to store IOREGSEL itself. A write
        to IOWIN while an invalid selector is active silently corrupts the
        READBACK copy without touching the selector actually used for
        indirect-access translation.
        """
        self.log.info("TEST MED-8: IOREGSEL invalid-selector readback")

        try:
            await self.tb.reset_dut()

            # Sanity: select a known-valid register, confirm readback.
            await self.tb.write_apb_register(
                IOAPICRegisterMap.IOREGSEL, IOAPICRegisterMap.OFFSET_IOAPICVER)
            _, regsel = await self.tb.read_apb_register(IOAPICRegisterMap.IOREGSEL)
            if (regsel & 0xFF) != IOAPICRegisterMap.OFFSET_IOAPICVER:
                self.log.error(f"Sanity check failed: IOREGSEL readback 0x{regsel:02X}")
                return False

            # Select an INVALID offset: not IOAPICID/VER/ARB (0x00-0x02) and
            # not in the redirection table range (0x10-0x3F).
            invalid_selector = 0x03
            await self.tb.write_apb_register(IOAPICRegisterMap.IOREGSEL, invalid_selector)

            # Write IOWIN with garbage while the invalid selector is active.
            await self.tb.write_apb_register(IOAPICRegisterMap.IOWIN, 0xDEADBEEF)

            # IOREGSEL readback must still equal the selector actually
            # written (0x03) - not something derived from the IOWIN garbage.
            _, regsel_after = await self.tb.read_apb_register(IOAPICRegisterMap.IOREGSEL)
            if (regsel_after & 0xFF) != invalid_selector:
                self.log.error(
                    f"IOREGSEL readback corrupted by an invalid-selector "
                    f"IOWIN write: expected 0x{invalid_selector:02X} (the "
                    f"selector that was written), got "
                    f"0x{regsel_after & 0xFF:02X}"
                )
                return False

            self.log.info("PASS: IOREGSEL readback unaffected by invalid-selector IOWIN write")
            return True

        except Exception as e:
            self.log.error(f"FAIL: IOREGSEL invalid-selector test raised {e}")
            return False

    # =========================================================================
    # Defects 7/8: address decode aliasing above 0x0FF
    # =========================================================================

    async def test_address_decode_no_aliasing_above_0x100(self) -> bool:
        """
        ioapic_config_regs decodes only the low 4KB window's 0x000-0x0FF
        range as this block's register space (`w_addr_in_window =
        adapter_addr[11:8] == 4'h0`); any APB address >= 0x100 is dropped
        before it reaches the register block (`w_drop`) and answers with
        PSLVERR asserted (`w_drop_err = !w_addr_in_window`) and read data a
        defined 0, never X - this also covers item 8 (IOWIN readback at the
        0x104 alias). A write to 0x108 or 0x114 must not corrupt IOAPICID
        or IOREDTBL[0].

        History: before the GitHub #48 fix, ioapic_config_regs fed
        regblk_addr straight into the register block's 8-bit s_cpuif_addr
        with no upper-bit qualification and no PSLVERR, so any address
        >= 0x100 aliased onto the register file modulo 0x100 (0x108 aliased
        IOAPICID at 0x008, 0x114 aliased IOREDTBL[0].LO at 0x014).
        """
        self.log.info("TEST MED-9: address decode aliasing above 0x100")

        try:
            await self.tb.reset_dut()

            golden_id = await self.tb.read_ioapic_register(IOAPICRegisterMap.OFFSET_IOAPICID)
            golden_redir_lo, golden_redir_hi = await self.tb.read_redirection_entry(0)

            # 0x108 would alias IOAPICID (0x008) if decode ignores upper bits.
            wr_108 = await self.tb.write_apb_register(0x108, 0xFEEDFACE)
            # 0x114 would alias IOREDTBL[0].LO (0x014).
            wr_114 = await self.tb.write_apb_register(0x114, 0xFEEDFACE)

            for addr, pkt in [(0x108, wr_108), (0x114, wr_114)]:
                if not pkt.pslverr:
                    self.log.error(
                        f"APB write to 0x{addr:03X} (>= 0x100, outside the "
                        f"4KB window's mapped 0x000-0x0FF range) did not "
                        f"assert PSLVERR"
                    )
                    return False

            id_after = await self.tb.read_ioapic_register(IOAPICRegisterMap.OFFSET_IOAPICID)
            redir_lo_after, redir_hi_after = await self.tb.read_redirection_entry(0)

            if id_after != golden_id:
                self.log.error(
                    f"IOAPICID corrupted by a write to APB 0x108: was "
                    f"0x{golden_id:08X}, now 0x{id_after:08X} - address "
                    f"decode is aliasing 0x108 onto 0x008 (IOAPICID)"
                )
                return False

            if (redir_lo_after, redir_hi_after) != (golden_redir_lo, golden_redir_hi):
                self.log.error(
                    f"IOREDTBL[0] corrupted by a write to APB 0x114: was "
                    f"(0x{golden_redir_lo:08X}, 0x{golden_redir_hi:08X}), "
                    f"now (0x{redir_lo_after:08X}, 0x{redir_hi_after:08X}) - "
                    f"address decode is aliasing 0x114 onto 0x014 "
                    f"(IOREDTBL[0].LO)"
                )
                return False

            # Item 8: alias reads (0x104/0x108, direct APB addresses) must
            # not be X, and must be reported with PSLVERR asserted.
            rd_104, data_104 = await self.tb.read_apb_register(0x104)
            rd_108, data_108 = await self.tb.read_apb_register(0x108)

            for addr, data, pkt in [(0x104, data_104, rd_104), (0x108, data_108, rd_108)]:
                if data is None:
                    self.log.error(f"APB read at 0x{addr:03X} returned no data")
                    return False
                if data != 0:
                    self.log.error(
                        f"APB read at 0x{addr:03X} (>= 0x100) returned "
                        f"0x{data:08X}, expected a defined 0 for a dropped "
                        f"out-of-window access"
                    )
                    return False
                if not pkt.pslverr:
                    self.log.error(
                        f"APB read at 0x{addr:03X} (>= 0x100, outside the "
                        f"4KB window's mapped 0x000-0x0FF range) did not "
                        f"assert PSLVERR"
                    )
                    return False

            self.log.info(
                f"Out-of-window reads (defined 0, PSLVERR asserted): "
                f"0x104=0x{data_104:08X}, 0x108=0x{data_108:08X}"
            )

            self.log.info("PASS: no register-file corruption from >= 0x100 APB accesses, "
                          "all dropped with PSLVERR")
            return True

        except Exception as e:
            self.log.error(f"FAIL: address decode aliasing test raised {e}")
            return False

    # =========================================================================
    # Review finding M1: in-window backdoor (0x008-0x0FF, direct APB access)
    # =========================================================================

    async def test_apb_backdoor_dropped_with_slverr(self) -> bool:
        """
        Only APB 0x000 (IOREGSEL) and 0x004 (IOWIN) are software-visible in
        this block's 4KB window - every other address, including ones that
        happen to equal a register block offset (e.g. 0x008 is
        ADDR_IOAPICID, 0x014 is ADDR_REDIR), must be dropped before it
        reaches the register block and answer with PSLVERR asserted (write
        ignored, read a defined 0), exactly like a >= 0x100 access. The
        indirect IOREGSEL/IOWIN mechanism is the only software path to the
        register block.

        This exercises the part of the 0x000-0x0FF window that
        test_address_decode_no_aliasing_above_0x100 (MED-9) does not: MED-9
        covers addresses outside the window (>= 0x100); this covers the
        addresses INSIDE the window that are neither IOREGSEL nor IOWIN.

        History: `w_drop` in ioapic_config_regs only ever gated
        `!w_addr_in_window` (>= 0x100) or an unmapped-selector IOWIN access.
        An in-window address that is not 0x004 fell through the default
        `regblk_addr = adapter_addr[7:0]` case and reached the register
        block directly, at its raw offset, bypassing the indirect access
        mechanism entirely and with no PSLVERR - GitHub #48 review round,
        finding M1.
        """
        self.log.info("TEST: APB in-window backdoor (0x008-0x0FF) dropped with PSLVERR")

        try:
            await self.tb.reset_dut()

            await self.tb.write_redirection_entry(
                irq=0, vector=0x5A, dest=0x02,
                delivery_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                dest_mode=0, polarity=0, trigger_mode=0, mask=0)

            golden_id = await self.tb.read_ioapic_register(IOAPICRegisterMap.OFFSET_IOAPICID)
            golden_redir_lo, golden_redir_hi = await self.tb.read_redirection_entry(0)

            # 0x014 is ADDR_REDIR - IOREDTBL[0].LO's raw register-block
            # offset. A direct APB write there must be dropped, not routed
            # to the register block at that raw address.
            wr_014 = await self.tb.write_apb_register(0x014, 0xFEEDFACE)
            # 0x008 is ADDR_IOAPICID - IOAPICID's raw register-block offset.
            wr_008 = await self.tb.write_apb_register(0x008, 0xFEEDFACE)

            for addr, pkt in [(0x014, wr_014), (0x008, wr_008)]:
                if not pkt.pslverr:
                    self.log.error(
                        f"APB write to 0x{addr:03X} (in-window backdoor, "
                        f"neither IOREGSEL nor IOWIN) did not assert PSLVERR"
                    )
                    return False

            id_after = await self.tb.read_ioapic_register(IOAPICRegisterMap.OFFSET_IOAPICID)
            redir_lo_after, redir_hi_after = await self.tb.read_redirection_entry(0)

            if id_after != golden_id:
                self.log.error(
                    f"IOAPICID corrupted by a direct APB write to 0x008: was "
                    f"0x{golden_id:08X}, now 0x{id_after:08X} - the in-window "
                    f"backdoor reached the register block at its raw offset"
                )
                return False

            if (redir_lo_after, redir_hi_after) != (golden_redir_lo, golden_redir_hi):
                self.log.error(
                    f"IOREDTBL[0] corrupted by a direct APB write to 0x014: "
                    f"was (0x{golden_redir_lo:08X}, 0x{golden_redir_hi:08X}), "
                    f"now (0x{redir_lo_after:08X}, 0x{redir_hi_after:08X}) - "
                    f"the in-window backdoor reached the register block at "
                    f"its raw offset"
                )
                return False

            # A direct read at the same backdoor address must also be
            # dropped: defined 0, PSLVERR asserted.
            rd_014, data_014 = await self.tb.read_apb_register(0x014)
            if data_014 != 0:
                self.log.error(
                    f"APB read at 0x014 (in-window backdoor) returned "
                    f"0x{data_014:08X}, expected a defined 0 for a dropped "
                    f"access"
                )
                return False
            if not rd_014.pslverr:
                self.log.error(
                    "APB read at 0x014 (in-window backdoor, neither "
                    "IOREGSEL nor IOWIN) did not assert PSLVERR"
                )
                return False

            self.log.info(
                "PASS: in-window backdoor accesses (0x008, 0x014) dropped "
                "with PSLVERR, register file unchanged"
            )
            return True

        except Exception as e:
            self.log.error(f"FAIL: in-window backdoor test raised {e}")
            return False

    # =========================================================================
    # Defect 9 (informational): CDC EOI synchronization
    # =========================================================================

    async def test_cdc_eoi_single_pclk_cycle_honored(self) -> bool:
        """
        When CDC_ENABLE=1, apb4_ioapic edge-detects eoi_in in the pclk
        domain and crosses it into ioapic_clk through a dedicated
        `sync_pulse` (3 stages), identical in depth to the `cdc_synchronizer`
        used for the delivery-accept crossing so the two events keep their
        pclk-domain order (see the crossing's header comment in
        apb4_ioapic.sv). ioapic_core has no WAIT_EOI to exit or miss - EOI is
        honoured in any state - so a synchronized EOI pulse simply clears
        Remote IRR whenever it arrives.

        NOT EXPECTED TO GO RED: with the runner's mandated CDC ratio
        (pclk=10ns, ioapic_clk=7ns - ioapic_clk FASTER than pclk, matching
        gpio_tb.py's TEST_GPIO_CLOCK_PERIOD precedent), a 10ns-wide
        single-pclk-cycle EOI pulse always straddles at least one 7ns
        ioapic_clk edge, so a zero-delay 2-state Verilator simulation cannot
        produce a "lost pulse" outcome - there is no metastability model to
        exercise. This is kept as a same-clock-vs-CDC regression (must pass
        in both configurations today) rather than a defect-proving test.

        History: before the GitHub #48 fix, eoi_in/eoi_vector reached the
        core combinationally with no synchronizer at all, and delivery was a
        single global WAIT_EOI state a missed EOI could wedge.
        """
        self.log.info("TEST MED-10: CDC EOI single-pclk-cycle honored (informational)")

        try:
            await self.tb.reset_dut()

            irq = 13
            vector = 0x3C
            await self.tb.write_redirection_entry(
                irq=irq, vector=vector, dest=0x01,
                delivery_mode=IOAPICRegisterMap.DELIV_MODE_FIXED,
                dest_mode=0, polarity=0, trigger_mode=1, mask=0)  # level
            await self.tb.wait_clocks('pclk', 5)

            await self.tb.assert_irq(irq)
            delivered = await self.tb.wait_for_interrupt(timeout_cycles=30)
            if not delivered:
                self.log.error(f"Level IRQ{irq} was never delivered")
                return False

            # Deassert and give the 3-stage irq_in synchronizer (ioapic_core)
            # time to actually settle low BEFORE sending EOI - otherwise the
            # RTL's synchronized view of the level is legitimately still
            # "asserted" at EOI time and a redelivery is CORRECT behaviour
            # (same rule as item 4/5: EOI with the input still asserted
            # redelivers), not the CDC defect this test targets.
            await self.tb.deassert_irq(irq)
            await self.tb.wait_clocks('pclk', 5)
            await self.tb.send_eoi(vector)
            await self.tb.wait_clocks('pclk', 20)

            remote_irr = await self.tb.read_remote_irr(irq)
            if remote_irr != 0:
                self.log.error(
                    f"Remote IRR for IRQ{irq} still set 20 pclk cycles "
                    f"after a single-cycle EOI(0x{vector:02X}) - the EOI "
                    f"pulse was lost crossing into the ioapic_clk domain"
                )
                return False

            self.log.info("PASS (expected): single-cycle EOI honored across the clock boundary")
            return True

        except Exception as e:
            self.log.error(f"FAIL: CDC EOI test raised {e}")
            return False

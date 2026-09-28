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

Each of the nine block TYPES has its own suite -- 54 cells across the area,
measured with `pytest --collect-only -q test_*.py` rather than remembered --
and none of it is repeated here. (Nine types, ten instances: RLB/pic_8259
TASK-001 put a SECOND 8259 on window 9 as the cascade slave.) These tests cover only what no per-block test
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

# RLB TASK-015: the fabric tests acknowledge through the 8259, so they need
# the register map the TB already uses.
from projects.components.retro_legacy_blocks.dv.tbclasses.pic_8259.pic_8259_tb import (
    PIC8259RegisterMap,
)


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
    async def test_aggregated_irq_output(self) -> bool:
        """rlb_irq_out asserts while any block interrupt is (PRD.md:515).

        Uses the EXTERNAL pic_irq_in deliberately: it needs no block
        programming, so a failure here is the aggregate being unwired rather
        than a peripheral that would not assert.
        """
        self.log.info("=== smoke: aggregated interrupt output ===")
        try:
            if not await self.tb.reset_and_init_pic():
                self.log.error("  PIC init failed; cannot proceed")
                return False
            if self.tb.rlb_irq_out():
                self.log.error("  rlb_irq_out already high after reset+init")
                return False
            if not await self.tb.pulse_pic_irq(3):
                self.log.error("  IRQ3 did not raise pic_int_out")
                return False
            if not self.tb.rlb_irq_out():
                self.log.error("  pic_int_out is high but rlb_irq_out is LOW -- "
                               "the aggregate does not see the PIC")
                return False
            self.log.info("smoke aggregated-irq GREEN (low at rest, high with "
                          "pic_int_out)")
            return True
        except Exception as e:
            self.log.error(f"aggregated irq test failed: {e}")
            return False

    async def test_fabric_routes_gpio_to_the_pic(self) -> bool:
        """A GPIO interrupt reaches the 8259 with NOTHING driven externally.

        This is the fabric's actual claim. pic_irq_in is held at 0 for the whole
        test, so the only path from GPIO to pic_int_out is the internal routing:
        gpio_irq -> IRQ11 -> slave 8259 IR3 -> slave INT -> master IR2.
        """
        self.log.info("=== smoke: fabric routes GPIO to the 8259 ===")
        try:
            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await self.tb.wait_clocks('pclk', 10)
            self.tb._idle_inputs()          # pic_irq_in = 0 and stays 0
            await self.tb.wait_clocks('pclk', 5)

            if not await self.tb.init_pic_cascade():
                self.log.error("  cascade init failed; IRQ8-15 cannot arrive")
                return False
            if self.tb.pic_int_out():
                self.log.error("  pic_int_out already high before the stimulus")
                return False

            # GPIO: global enable + global int enable, pin 0 rising edge.
            await self.tb.gpio_write(0x000, 0x3)          # gpio_enable|int_enable
            await self.tb.gpio_write(0x010, 0x1)          # INT_ENABLE  pin 0
            await self.tb.gpio_write(0x014, 0x0)          # INT_TYPE    edge
            await self.tb.gpio_write(0x018, 0x1)          # INT_POLARITY rising
            await self.tb.gpio_write(0x01C, 0x0)          # INT_BOTH    off

            self.tb.dut.gpio_in.value = 0
            await self.tb.wait_clocks('pclk', 5)
            self.tb.dut.gpio_in.value = 1                 # rising edge on pin 0
            await self.tb.wait_clocks('pclk', 40)

            if int(self.tb.dut.pic_irq_in.value) != 0:
                self.log.error("  pic_irq_in is non-zero -- the test would not "
                               "be proving internal routing")
                return False
            if not self.tb.pic_int_out():
                self.log.error("  GPIO asserted but pic_int_out stayed LOW -- "
                               "the internal fabric did not deliver IRQ11")
                return False
            if not self.tb.rlb_irq_out():
                self.log.error("  rlb_irq_out LOW while a block interrupt is "
                               "asserted")
                return False

            # The BFM's negative assertion, which polling could not express:
            # exactly these lines moved and no others. The line that must NOT
            # have moved is where the bugs are -- a fabric that ORed a source
            # onto the wrong bit passes every positive check above.
            ok, missing, unexpected = self.tb.irqs.expect_only(
                ['gpio_irq', 'pic_int_out', 'rlb_irq_out'])
            if not ok:
                self.log.error(f"  IRQ lines wrong: missing={missing} "
                               f"unexpected={unexpected}")
                for pkt in self.tb.irqs.all_events():
                    self.log.error(f"    {pkt}")
                return False

            self.log.info("smoke fabric-GPIO GREEN (gpio_irq reached the 8259 "
                          "with pic_irq_in held at 0; exactly gpio_irq, "
                          "pic_int_out and rlb_irq_out moved)")
            return True
        except Exception as e:
            self.log.error(f"fabric GPIO routing test failed: {e}")
            return False

    async def test_fabric_routes_pm_acpi_to_the_pic(self) -> bool:
        """A PM/ACPI GPE interrupt reaches the 8259 on IRQ9, internally.

        Chosen as the second block because, like GPIO, it is driven by a DUT
        INPUT (pm_gpe_events) rather than needing a clocked count-down (PIT),
        a simulated second (RTC) or bus modelling (SMBus). pic_irq_in is held
        at 0 throughout, so only the internal fabric can explain the result.

        PM/ACPI is IRQ9 -> slave 8259 IR1.
        """
        self.log.info("=== smoke: fabric routes PM/ACPI to the 8259 ===")
        try:
            await self.tb.assert_reset()
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.deassert_reset()
            await self.tb.wait_clocks('pclk', 10)
            self.tb._idle_inputs()
            await self.tb.wait_clocks('pclk', 5)

            if not await self.tb.init_pic_cascade():
                self.log.error("  cascade init failed; IRQ8-15 cannot arrive")
                return False
            self.tb.irqs.clear()
            if self.tb.pic_int_out():
                self.log.error("  pic_int_out already high before the stimulus")
                return False

            # ACPI_CONTROL: enable ACPI + GPE. Bit values from the pm_acpi TB,
            # not guessed: CONTROL_ACPI_ENABLE (1<<0), CONTROL_GPE_ENABLE (1<<2).
            await self.tb.apb_write(
                self.tb.window_addr(self.tb.SLAVE_PM, 0x000), 0x1 | 0x4)
            # ACPI_INT_ENABLE: INT_ENABLE_GPE (1<<5)
            await self.tb.apb_write(
                self.tb.window_addr(self.tb.SLAVE_PM, 0x008), 1 << 5)
            # GPE0_ENABLE_LO: unmask GPE bit 0
            await self.tb.apb_write(
                self.tb.window_addr(self.tb.SLAVE_PM, 0x038), 0x1)
            await self.tb.wait_clocks('pclk', 5)

            self.tb.dut.pm_gpe_events.value = 0
            await self.tb.wait_clocks('pclk', 5)
            self.tb.dut.pm_gpe_events.value = 1      # rising GPE event
            await self.tb.wait_clocks('pclk', 40)

            if int(self.tb.dut.pic_irq_in.value) != 0:
                self.log.error("  pic_irq_in is non-zero -- this would not be "
                               "proving internal routing")
                return False

            pm = self.tb.irqs.monitors.get('pm_interrupt')
            if pm is None or pm.assert_count == 0:
                self.log.error("  pm_interrupt never asserted -- the PM block "
                               "did not raise, so the fabric is untested here")
                for pkt in self.tb.irqs.all_events():
                    self.log.error(f"    saw: {pkt}")
                self.tb.dut.pm_gpe_events.value = 0
                return False

            if not self.tb.pic_int_out():
                self.log.error("  pm_interrupt asserted but pic_int_out stayed "
                               "LOW -- the fabric did not deliver IRQ9")
                return False

            ok, missing, unexpected = self.tb.irqs.expect_only(
                ['pm_interrupt', 'pic_int_out', 'rlb_irq_out'])
            if not ok:
                self.log.error(f"  IRQ lines wrong: missing={missing} "
                               f"unexpected={unexpected}")
                for pkt in self.tb.irqs.all_events():
                    self.log.error(f"    {pkt}")
                self.tb.dut.pm_gpe_events.value = 0
                return False

            self.log.info("smoke fabric-PM GREEN (pm_interrupt reached the 8259 "
                          "on IRQ9 with pic_irq_in held at 0)")
            self.tb.dut.pm_gpe_events.value = 0
            return True
        except Exception as e:
            self.log.error(f"PM/ACPI fabric routing test failed: {e}")
            return False

    async def _fabric_preamble(self) -> bool:
        """Reset, idle every input, bring the cascaded pair up, clear the BFM.

        Shared by the per-block routing tests. Each one resets first because
        the 8259 LATCHES int_out in edge mode: without a reset between blocks
        the second test would be reading the first one's assertion and would
        pass for entirely the wrong reason.
        """
        await self.tb.assert_reset()
        await self.tb.wait_clocks('pclk', 10)
        await self.tb.deassert_reset()
        await self.tb.wait_clocks('pclk', 10)
        self.tb._idle_inputs()
        await self.tb.wait_clocks('pclk', 5)
        if not await self.tb.init_pic_cascade():
            self.log.error("  cascade init failed; IRQ8-15 cannot arrive")
            return False
        self.tb.irqs.clear()
        if self.tb.pic_int_out():
            self.log.error("  pic_int_out already high before the stimulus")
            return False
        return True

    def _routing_verdict(self, source: str, expected: list) -> bool:
        """Shared checks: source fired, reached the PIC, and NOTHING else moved."""
        if int(self.tb.dut.pic_irq_in.value) != 0:
            self.log.error("  pic_irq_in is non-zero -- this would not be "
                           "proving internal routing")
            return False
        mon = self.tb.irqs.monitors.get(source)
        if mon is None or mon.assert_count == 0:
            self.log.error(f"  {source} never asserted -- the BLOCK did not "
                           "raise, so the fabric is untested here")
            for pkt in self.tb.irqs.all_events():
                self.log.error(f"    saw: {pkt}")
            return False
        if not self.tb.pic_int_out():
            self.log.error(f"  {source} asserted but pic_int_out stayed LOW -- "
                           "the fabric did not deliver it")
            return False
        ok, missing, unexpected = self.tb.irqs.expect_only(expected)
        if not ok:
            self.log.error(f"  IRQ lines wrong: missing={missing} "
                           f"unexpected={unexpected}")
            for pkt in self.tb.irqs.all_events():
                self.log.error(f"    {pkt}")
            return False
        return True

    async def test_fabric_routes_uart_to_the_pic(self) -> bool:
        """A UART interrupt reaches the 8259 on IRQ4, internally.

        Uses the TX-HOLDING-EMPTY source, not RX. RX would need the DLAB dance
        to set a baud divisor and then real shift time for a byte to travel
        TX->RX in loopback -- several ways to fail for reasons that have
        nothing to do with the fabric. The transmitter is already empty at
        reset, so enabling that interrupt asserts it almost immediately.

        MCR_OUT2 is REQUIRED as well as IER: OUT2 gates the IRQ pin, and a UART
        configured with IER alone is fully set up and still never asserts.

        UART is IRQ4 -> MASTER 8259 IR4 (below 8, so it does not go via the
        slave, unlike GPIO and PM).
        """
        self.log.info("=== smoke: fabric routes UART to the 8259 ===")
        try:
            if not await self._fabric_preamble():
                return False

            W = self.tb.SLAVE_UART
            # MCR: OUT2 (1<<3) gates the IRQ pin
            await self.tb.apb_write(self.tb.window_addr(W, 0x014), 1 << 3)
            # IER: TX holding empty (1<<1)
            await self.tb.apb_write(self.tb.window_addr(W, 0x004), 1 << 1)
            await self.tb.wait_clocks('pclk', 40)

            if not self._routing_verdict(
                    'uart_irq', ['uart_irq', 'pic_int_out', 'rlb_irq_out']):
                return False
            self.log.info("smoke fabric-UART GREEN (uart_irq reached the 8259 "
                          "on IRQ4 with pic_irq_in held at 0)")
            return True
        except Exception as e:
            self.log.error(f"UART fabric routing test failed: {e}")
            return False

    async def test_fabric_routes_pit_to_the_pic(self) -> bool:
        """A PIT counter-0 interrupt reaches the 8259 on IRQ0, internally.

        Mode 0 is 'interrupt on terminal count': the output goes low on the
        count write and HIGH when the counter reaches zero, which is the
        interrupt. GATE must be high for counting to proceed.

        NOTE the constant convention: PIT's CONFIG_PIT_ENABLE is a bit
        POSITION (0), where RTC/SMBus/PM/UART use pre-shifted masks. Hence
        `1 << 0` here and bare constants elsewhere -- mixing them is a silent
        off-by-shift.

        PIT is IRQ0 -> MASTER 8259 IR0.
        """
        self.log.info("=== smoke: fabric routes PIT to the 8259 ===")
        try:
            if not await self._fabric_preamble():
                return False

            W = self.tb.SLAVE_PIT
            self.tb.dut.pit_gate_in.value = 0x1          # GATE high, counter 0
            await self.tb.apb_write(self.tb.window_addr(W, 0x000), 1 << 0)  # enable
            # Control word: BCD=0 (bit0), MODE=0 (bits 3:1), RW=3 LSB+MSB
            # (bits 5:4), COUNTER=0 (bits 7:6)  ->  0x30
            await self.tb.apb_write(self.tb.window_addr(W, 0x004), 0x30)
            # A small initial count so terminal count arrives quickly.
            await self.tb.apb_write(self.tb.window_addr(W, 0x010), 0x0005)
            await self.tb.wait_clocks('pclk', 400)       # pit_clk is slower

            if not self._routing_verdict(
                    'pit_timer_irq', ['pit_timer_irq', 'pic_int_out', 'rlb_irq_out']):
                self.tb.dut.pit_gate_in.value = 0
                return False
            self.log.info("smoke fabric-PIT GREEN (pit_timer_irq reached the "
                          "8259 on IRQ0 with pic_irq_in held at 0)")
            self.tb.dut.pit_gate_in.value = 0
            return True
        except Exception as e:
            self.log.error(f"PIT fabric routing test failed: {e}")
            return False

    async def test_fabric_routes_rtc_to_the_pic(self) -> bool:
        """An RTC second-tick reaches the 8259 on IRQ8, internally.

        The RTC divider is the obstacle: one tick is 32768 selected_clk edges
        in production mode. clock_select=1 puts selected_clk on pclk AND drops
        the divider target to 99 (rtc_core: DIV_TARGET_SYS), and the block's own
        TB ships force_divider_near_target() to poke r_clk_div_counter just
        below that -- the RTL comment names that helper as the reason the two
        targets are localparams. Same trick here, through the rlb_top hierarchy.

        NOT modelled on the RTC block's own periodic-tick test: that one waits
        500 cycles and then logs "Second tick flag not set (may need more time)"
        and passes ANYWAY. It cannot fail, so it proves nothing. This one fails
        if the tick does not arrive.

        RTC is IRQ8 -> slave 8259 IR0.
        """
        self.log.info("=== smoke: fabric routes RTC to the 8259 ===")
        try:
            if not await self._fabric_preamble():
                return False

            W = self.tb.SLAVE_RTC
            # RTC_CONFIG: CONFIG_RTC_ENABLE (1<<0) | CONFIG_CLOCK_SELECT (1<<3).
            # clock_select=1 is what makes the divider target 99 instead of 32767.
            await self.tb.apb_write(self.tb.window_addr(W, 0x000), 0x1 | 0x8)
            # RTC_STATUS is W1C -- clear any stale tick before arming.
            await self.tb.apb_write(self.tb.window_addr(W, 0x008), 0xFFFFFFFF)
            # RTC_CONTROL: CONTROL_SECOND_INT_ENABLE (1<<2)
            await self.tb.apb_write(self.tb.window_addr(W, 0x004), 1 << 2)
            await self.tb.wait_clocks('pclk', 10)

            # Whitebox: roll the divider over in a few cycles instead of 100.
            # An explicit failure if the path is wrong -- a silent fallback to
            # "just wait" would turn a broken hierarchy into a passing test.
            try:
                core = self.tb.dut.u_rtc.u_rtc_core
                core.r_clk_div_counter.value = 99 - 2      # DIV_TARGET_SYS - 2
            except AttributeError as e:
                self.log.error("  whitebox path dut.u_rtc.u_rtc_core."
                               f"r_clk_div_counter not reachable: {e}")
                return False
            await self.tb.wait_clocks('pclk', 60)

            if not self._routing_verdict(
                    'rtc_second_irq',
                    ['rtc_second_irq', 'pic_int_out', 'rlb_irq_out']):
                return False
            self.log.info("smoke fabric-RTC GREEN (rtc_second_irq reached the "
                          "8259 on IRQ8 with pic_irq_in held at 0)")
            return True
        except Exception as e:
            self.log.error(f"RTC fabric routing test failed: {e}")
            return False

    async def test_fabric_routes_smbus_to_the_pic(self) -> bool:
        """An SMBus error interrupt reaches the 8259 on IRQ10, internally.

        No bus model and no timeout needed. rlb_top_tb._idle_inputs() holds
        smb_sda_i high ("open-drain with pull-ups: released lines read high"),
        so nothing on the bus ever pulls the ACK slot low. smbus_core.sv:494
        reads that as a NAK:

            end else if (w_ack_state && r_ack_valid && r_ack_bit) begin
                r_nak_received <= 1'b1;
                r_master_state <= M_ERROR;

        and r_nak_received is one of the terms in w_error_next (line 238), so
        the sticky error status sets and, with INT_ERROR_EN armed, raises
        smb_interrupt. The absent slave IS the stimulus.

        A quick command is the shortest transaction that has an ACK slot:
        START, 8 address bits, ACK, STOP. clk_div 6 gives unit=(6+2)>>1=4 and
        an SCL period of 32 pclk, so the whole thing is ~400 cycles -- the
        phy warns about degenerate periods down at clk_div=2, which this
        stays well clear of.

        SMBus is IRQ10 -> slave 8259 IR2.
        """
        self.log.info("=== smoke: fabric routes SMBus to the 8259 ===")
        try:
            if not await self._fabric_preamble():
                return False

            W = self.tb.SLAVE_SMBUS
            # Slow enough to be legal, fast enough to be cheap.
            await self.tb.apb_write(self.tb.window_addr(W, 0x020), 6)
            # INT_STATUS is W1C -- clear before arming.
            await self.tb.apb_write(self.tb.window_addr(W, 0x030), 0xFF)
            # INT_ENABLE: INT_ERROR_EN (1<<1)
            await self.tb.apb_write(self.tb.window_addr(W, 0x02C), 1 << 1)
            # CONTROL: MASTER_EN (1<<0). Must precede the start -- w_start_req
            # is (cmd_start && cfg_master_en && !w_slv_addressed).
            await self.tb.apb_write(self.tb.window_addr(W, 0x000), 1 << 0)
            await self.tb.wait_clocks('pclk', 10)

            # SLAVE_ADDR, then COMMAND = QUICK_CMD | START | STOP.
            await self.tb.apb_write(self.tb.window_addr(W, 0x00C), 0x50)
            await self.tb.apb_write(self.tb.window_addr(W, 0x008),
                                    0x0 | (1 << 16) | (1 << 17))
            await self.tb.wait_clocks('pclk', 1500)

            if not self._routing_verdict(
                    'smb_interrupt',
                    ['smb_interrupt', 'pic_int_out', 'rlb_irq_out']):
                return False
            self.log.info("smoke fabric-SMBus GREEN (a NAKed quick command "
                          "reached the 8259 on IRQ10 with pic_irq_in held at 0)")
            return True
        except Exception as e:
            self.log.error(f"SMBus fabric routing test failed: {e}")
            return False

    async def test_fabric_gpio_returns_the_slave_vector(self) -> bool:
        """The GPIO interrupt is acknowledged as a SLAVE vector, not the master's.

        GPIO is IRQ11 -> slave IR3. With slave base 0x28 that is vector 0x2B,
        while the master's own IR2 vector would be 0x22. Different numbers on
        purpose: this distinguishes "the cascade delivered it" from "the master
        answered for itself".
        """
        self.log.info("=== smoke: GPIO acknowledges as a slave vector ===")
        try:
            if not self.tb.pic_int_out():
                self.log.error("  precondition: no interrupt pending "
                               "(run the routing test first)")
                return False
            addr = self.tb.window_addr(self.tb.SLAVE_PIC,
                                       PIC8259RegisterMap.PIC_INTA)
            _, raw, _ = await self.tb.apb_read(addr)
            valid, vector = (raw >> 8) & 1, raw & 0xFF
            self.log.info(f"  master INTA: valid={valid} vector=0x{vector:02X} "
                          f"(slave IR3 expects 0x2B, master IR2 would be 0x22)")
            if not valid:
                self.log.error("  INTA returned valid=0 with an interrupt pending")
                return False
            if vector == 0x22:
                self.log.error("  master returned its OWN IR2 vector -- the "
                               "cascade diversion did not happen")
                return False
            if vector != 0x2B:
                self.log.error(f"  vector 0x{vector:02X}, expected the slave's 0x2B")
                return False
            self.log.info("smoke slave-vector GREEN (0x2B via the cascade)")
            return True
        except Exception as e:
            self.log.error(f"slave vector test failed: {e}")
            return False

    async def test_slave_pic_window_responds(self) -> bool:
        """Window 9 is the SLAVE 8259 now, and it answers cleanly.

        REPLACES test_reserved_window_errors. That test asserted window 9
        returned 0xDEADBEEF with PSLVERR, which was true while the slot was a
        tie-off. RLB/pic_8259 TASK-001 put the slave 8259 there, so there is no
        reserved window left in the map and the old assertion is now exactly
        backwards -- it would fail against correct hardware.

        The window was ALREADY DECODED by the generated crossbar, which is why
        taking it needed no regeneration; this checks the decode actually
        reaches a real block rather than a dangling port.
        """
        self.log.info("=== smoke: slave PIC window responds ===")
        try:
            addr = self.tb.window_addr(self.tb.SLAVE_PIC_SLAVE, 0x000)
            _, value, slverr = await self.tb.apb_read(addr)
            checks = 0
            if slverr:
                self.log.error(
                    f"  slave PIC window returned PSLVERR=1 (data 0x{value:08X}) "
                    "-- window 9 is a real block now, not a reserved tie-off")
                return False
            checks += 1
            if value == 0xDEADBEEF:
                self.log.error(
                    "  slave PIC window still returns 0xDEADBEEF -- the reserved "
                    "tie-off is still driving it, so the slave PIC is not wired")
                return False
            checks += 1
            # Prove it is the PIC and not merely something that READYs: writing
            # pic_enable must read back, which a tie-off could never do.
            await self.tb.apb_write(addr, 0x1)
            await self.tb.wait_clocks('pclk', 5)
            _, readback, rb_err = await self.tb.apb_read(addr)
            if rb_err or (readback & 0x1) != 0x1:
                self.log.error(
                    f"  slave PIC PIC_CONFIG readback 0x{readback:08X} "
                    f"(pslverr={rb_err}) -- expected pic_enable to stick")
                return False
            checks += 1
            self.log.info(f"smoke slave-PIC-window GREEN ({checks} checks, "
                          f"PIC_CONFIG 0x{readback:08X})")
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

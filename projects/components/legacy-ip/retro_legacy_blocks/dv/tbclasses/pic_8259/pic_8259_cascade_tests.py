# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PIC8259CascadeTests
# Purpose: 8259 PC/AT cascade coverage (RLB/pic_8259 TASK-001)
#
# Created: 2026-09-28

"""8259 cascade (master/slave) test suite.

Runs against pic_8259_cascade_tb_top, which instantiates two apb4_pic_8259 in
the PC/AT arrangement: the slave's int_out drives master IR2, and cas_ack /
cas_vector cross-connect. Both PICs sit behind one APB port, the slave at
+0x800 (the wrapper decodes PADDR[11]).

WHAT MAKES THESE TESTS MEAN SOMETHING: the master's own IR2 vector would be
0x22 and the slave's IR0 vector is 0x28. They are DIFFERENT NUMBERS on purpose,
so "the master returned the slave's vector" is a positive assertion rather than
a coincidence. A cascade implementation that forgot to divert would return 0x22
and fail loudly.

The wrapper forces master IR2 from the slave's int_out rather than OR-ing it,
so a test cannot fake "the slave raised the master" by driving irq_in[2].
"""

from .pic_8259_tb import PIC8259RegisterMap


class PIC8259CascadeTests:
    """PC/AT cascade test suite for the 8259 pair."""

    SLAVE = 0x800           # wrapper chip select: PADDR[11] picks the slave
    CASCADE_IR = 2          # PC/AT hangs the slave off master IR2
    CASCADE_BITMAP = 0x04   # master ICW3: a slave sits on IR2

    MASTER_VEC_BASE = 0x20  # -> master IR2 would be 0x22
    SLAVE_VEC_BASE = 0x28   # -> slave  IR0 is     0x28

    def __init__(self, tb):
        self.tb = tb
        self.log = tb.log

    # ------------------------------------------------------------------
    # helpers
    # ------------------------------------------------------------------
    def _slave_reg(self, offset: int) -> int:
        return self.SLAVE | offset

    async def _set_slave_irq(self, value: int):
        """Drive the slave's IR lines (IRQ8-15 in PC/AT terms)."""
        self.tb.dut.slave_irq_in.value = value
        await self.tb.wait_clocks('pclk', 2)

    def _master_int(self) -> int:
        return int(self.tb.dut.int_out.value)

    def _slave_int(self) -> int:
        return int(self.tb.dut.slave_int.value)

    async def _init_pair(self, master_imr: int = 0x00, slave_imr: int = 0x00):
        """Bring both PICs up in cascade mode and quiesce the IR lines.

        Called at the START of every test rather than relying on the previous
        one leaving things tidy: a stale ISR bit in either controller changes
        priority resolution and would make a later failure look like a cascade
        bug when it is really leakage.
        """
        self.tb.dut.irq_in.value = 0
        await self._set_slave_irq(0)

        # MASTER: SNGL=0, ICW3 = bitmap of IR lines carrying a slave.
        await self.tb.initialize_pic(vector_base=self.MASTER_VEC_BASE,
                                     edge_triggered=True,
                                     cascade=self.CASCADE_BITMAP)
        # SLAVE: SNGL=0, ICW3 = the IR line it hangs off.
        await self.tb.initialize_pic(vector_base=self.SLAVE_VEC_BASE,
                                     edge_triggered=True,
                                     slave_id=self.CASCADE_IR,
                                     base_addr=self.SLAVE)

        await self.tb.write_register(PIC8259RegisterMap.PIC_OCW1, master_imr)
        await self.tb.write_register(self._slave_reg(PIC8259RegisterMap.PIC_OCW1),
                                     slave_imr)
        await self.tb.wait_clocks('pclk', 5)

    async def _read_both_isr(self):
        _, m = await self.tb.read_register(PIC8259RegisterMap.PIC_ISR)
        _, s = await self.tb.read_register(self._slave_reg(PIC8259RegisterMap.PIC_ISR))
        return m & 0xFF, s & 0xFF

    # ------------------------------------------------------------------
    # tests
    # ------------------------------------------------------------------
    async def test_cascade_initialization(self) -> bool:
        """Both PICs initialise in cascade mode, and ICW3 stays write-only."""
        self.log.info("=== cascade init: SNGL=0 on both, ICW3 written ===")
        self.tb.test_phase = "CASCADE_INIT"
        try:
            await self._init_pair()

            _, m_status = await self.tb.read_register(PIC8259RegisterMap.PIC_STATUS)
            _, s_status = await self.tb.read_register(
                self._slave_reg(PIC8259RegisterMap.PIC_STATUS))
            passed = True

            # init_complete is bit 0. With SNGL=0 the core WAITS for ICW3, so
            # reaching init_complete at all proves the ICW3 write was consumed
            # as ICW3 -- in single mode that same write would have been taken
            # as ICW4 and the sequence would not have completed here.
            if not (m_status & 1):
                self.log.error(f"master did not complete init (STATUS=0x{m_status:08X})")
                passed = False
            if not (s_status & 1):
                self.log.error(f"slave did not complete init (STATUS=0x{s_status:08X})")
                passed = False

            # ICW3 is sw = w on a real 8259A. It must NOT read back.
            _, m_icw3 = await self.tb.read_register(PIC8259RegisterMap.PIC_ICW3)
            if (m_icw3 & 0xFF) != 0:
                self.log.error(f"PIC_ICW3 read back 0x{m_icw3:02X}, expected 0 -- "
                               "ICW3 is write-only on a real part")
                passed = False

            self.log.info(f"master STATUS=0x{m_status:08X} slave STATUS=0x{s_status:08X} "
                          f"ICW3 readback=0x{m_icw3 & 0xFF:02X}")
            return passed
        except Exception as e:
            self.log.error(f"cascade init test failed: {e}")
            return False

    async def test_slave_int_raises_master(self) -> bool:
        """A slave IR raises the slave's INT, which raises the master."""
        self.log.info("=== slave INT -> master IR2 ===")
        self.tb.test_phase = "CASCADE_SLAVE_RAISES_MASTER"
        try:
            await self._init_pair()
            if self._master_int() or self._slave_int():
                self.log.error("INT already asserted before the stimulus")
                return False

            await self._set_slave_irq(0x01)          # slave IR0 == IRQ8
            await self.tb.wait_clocks('pclk', 10)

            passed = True
            if not self._slave_int():
                self.log.error("slave int_out did not assert for slave IR0")
                passed = False
            if not self._master_int():
                self.log.error("master int_out did not assert -- the slave's INT "
                               "is wired to master IR2, so the master must see it")
                passed = False

            _, m_irr = await self.tb.read_register(PIC8259RegisterMap.PIC_IRR)
            if not ((m_irr >> self.CASCADE_IR) & 1):
                self.log.error(f"master IRR=0x{m_irr & 0xFF:02X}: IR{self.CASCADE_IR} "
                               "not latched from the slave")
                passed = False

            self.log.info(f"slave_int={self._slave_int()} master int_out="
                          f"{self._master_int()} master IRR=0x{m_irr & 0xFF:02X}")
            await self._set_slave_irq(0)
            return passed
        except Exception as e:
            self.log.error(f"slave-raises-master test failed: {e}")
            return False

    async def test_master_inta_returns_slave_vector(self) -> bool:
        """The master's PIC_INTA read returns the SLAVE's vector, not its own."""
        self.log.info("=== master INTA on a cascade level -> SLAVE vector ===")
        self.tb.test_phase = "CASCADE_VECTOR"
        try:
            await self._init_pair()
            await self._set_slave_irq(0x01)          # slave IR0 -> vector 0x28
            await self.tb.wait_clocks('pclk', 10)

            inta = await self.tb.read_inta()
            passed = True
            self.log.info(f"master INTA: valid={inta['valid']} "
                          f"vector=0x{inta['vector']:02X} "
                          f"(slave expects 0x{self.SLAVE_VEC_BASE:02X}, "
                          f"master's own IR2 would be "
                          f"0x{self.MASTER_VEC_BASE | self.CASCADE_IR:02X})")

            if not inta['valid']:
                self.log.error("master INTA returned valid=0 with a cascade "
                               "request pending")
                passed = False
            if inta['vector'] == (self.MASTER_VEC_BASE | self.CASCADE_IR):
                self.log.error("master returned its OWN IR2 vector -- the cascade "
                               "diversion did not happen")
                passed = False
            elif inta['vector'] != self.SLAVE_VEC_BASE:
                self.log.error(f"master returned 0x{inta['vector']:02X}, expected the "
                               f"slave's 0x{self.SLAVE_VEC_BASE:02X}")
                passed = False

            # The acknowledge must retire the level in BOTH controllers.
            m_isr, s_isr = await self._read_both_isr()
            if not ((m_isr >> self.CASCADE_IR) & 1):
                self.log.error(f"master ISR=0x{m_isr:02X}: cascade level not in service")
                passed = False
            if not (s_isr & 0x01):
                self.log.error(f"slave ISR=0x{s_isr:02X}: the master's read must "
                               "acknowledge the slave too (cas_ack -> inta_ack)")
                passed = False

            self.log.info(f"master ISR=0x{m_isr:02X} slave ISR=0x{s_isr:02X}")
            await self._set_slave_irq(0)
            return passed
        except Exception as e:
            self.log.error(f"cascade vector test failed: {e}")
            return False

    async def test_masked_cascade_level_blocks_slave(self) -> bool:
        """Masking master IR2 stops the slave reaching the CPU."""
        self.log.info("=== masked cascade level blocks the slave ===")
        self.tb.test_phase = "CASCADE_MASKED"
        try:
            # Mask ONLY the cascade level on the master; the slave is wide open.
            await self._init_pair(master_imr=self.CASCADE_BITMAP)
            await self._set_slave_irq(0x02)          # slave IR1
            await self.tb.wait_clocks('pclk', 10)

            passed = True
            if not self._slave_int():
                self.log.error("slave int_out did not assert -- the slave is "
                               "unmasked, so the mask under test is the master's")
                passed = False
            if self._master_int():
                self.log.error("master int_out asserted with IR2 MASKED -- the "
                               "master's mask must gate the cascade like any level")
                passed = False

            self.log.info(f"slave_int={self._slave_int()} "
                          f"master int_out={self._master_int()} (expect 1 / 0)")
            await self._set_slave_irq(0)
            return passed
        except Exception as e:
            self.log.error(f"masked cascade test failed: {e}")
            return False

    async def test_eoi_retires_both(self) -> bool:
        """EOI to each controller clears its own ISR bit."""
        self.log.info("=== EOI retires the level in BOTH controllers ===")
        self.tb.test_phase = "CASCADE_EOI"
        try:
            await self._init_pair()
            await self._set_slave_irq(0x01)
            await self.tb.wait_clocks('pclk', 10)
            await self.tb.read_inta()

            m_isr, s_isr = await self._read_both_isr()
            if not ((m_isr >> self.CASCADE_IR) & 1) or not (s_isr & 0x01):
                self.log.error(f"precondition failed: master ISR=0x{m_isr:02X} "
                               f"slave ISR=0x{s_isr:02X}, expected both in service")
                await self._set_slave_irq(0)
                return False

            # The slave is acknowledged by the master's read, but EOI'd on its
            # OWN port -- send_eoi() writes the master's OCW2 offset only, so
            # the slave's EOI is an explicit write at +0x800.
            # OCW2 = R SL EOI 0 0 L2 L1 L0; specific EOI is cmd 011 -> 0x60 | n.
            await self.tb.write_register(self._slave_reg(PIC8259RegisterMap.PIC_OCW2),
                                         0x60 | 0)
            await self.tb.wait_clocks('pclk', 5)
            await self.tb.send_eoi(irq=self.CASCADE_IR, specific=True)

            m_isr, s_isr = await self._read_both_isr()
            passed = True
            if (m_isr >> self.CASCADE_IR) & 1:
                self.log.error(f"master ISR=0x{m_isr:02X}: cascade level still in service")
                passed = False
            if s_isr & 0x01:
                self.log.error(f"slave ISR=0x{s_isr:02X}: slave level still in service")
                passed = False

            self.log.info(f"after EOI: master ISR=0x{m_isr:02X} slave ISR=0x{s_isr:02X}")
            await self._set_slave_irq(0)
            return passed
        except Exception as e:
            self.log.error(f"cascade EOI test failed: {e}")
            return False

    async def test_non_cascade_level_unaffected(self) -> bool:
        """A NON-cascade master level still returns the master's own vector.

        The off-state of the diversion. Without this, RTL that returned
        cas_vector for every level would pass every other test here.
        """
        self.log.info("=== non-cascade level returns the MASTER vector ===")
        self.tb.test_phase = "CASCADE_OFF_STATE"
        try:
            await self._init_pair()
            self.tb.dut.irq_in.value = 0x20          # master IR5, not a cascade level
            await self.tb.wait_clocks('pclk', 10)

            inta = await self.tb.read_inta()
            expected = self.MASTER_VEC_BASE | 5
            passed = True
            self.log.info(f"master INTA on IR5: valid={inta['valid']} "
                          f"vector=0x{inta['vector']:02X} (expect 0x{expected:02X})")

            if not inta['valid']:
                self.log.error("master INTA returned valid=0 for an unmasked IR5")
                passed = False
            elif inta['vector'] != expected:
                self.log.error(f"master returned 0x{inta['vector']:02X} for IR5, "
                               f"expected its OWN 0x{expected:02X} -- the diversion "
                               "must apply ONLY to cascade levels")
                passed = False

            _, s_isr = await self.tb.read_register(
                self._slave_reg(PIC8259RegisterMap.PIC_ISR))
            if s_isr & 0xFF:
                self.log.error(f"slave ISR=0x{s_isr & 0xFF:02X}: a non-cascade "
                               "acknowledge must not reach the slave")
                passed = False

            self.tb.dut.irq_in.value = 0
            return passed
        except Exception as e:
            self.log.error(f"non-cascade level test failed: {e}")
            return False

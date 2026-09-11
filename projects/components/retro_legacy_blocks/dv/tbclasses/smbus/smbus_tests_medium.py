# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SMBusMediumTests
# Purpose: Coordinator-directed RED regression tests for GitHub issue #58
#          (apb4_smbus RTL bugs), written FIRST against the unfixed RTL.
#
# Created: 2026-09-09
#
# ============================================================================
# GH#58 defect map (RTL mechanism traced by reading smbus_core.sv,
# smbus_pec.sv, smbus_config_regs.sv and rdl/smbus/smbus_regs.rdl -- no
# rtl/** file was modified to produce this list or these tests):
#
#  1. C4  - SCL never toggles / not open-drain.
#           smbus_core.sv's physical-layer FSM only assigns r_scl_out in
#           PHY_START and PHY_STOP; PHY_BIT_TX/PHY_BIT_RX (every data/ACK
#           bit after the initial START) never touch it, so smb_scl_o
#           freezes low forever after the first START edge. Separately,
#           the tristate-control block leaves r_sda_tristate=0 (driving)
#           for the whole PHY_STOP state even on the sub-phase where
#           r_sda_out is set to 1 to "release" SDA - i.e. the DUT
#           actively drives a logic 1 on an open-drain line instead of
#           releasing it (sda_t should be 1 there).
#  2. C3  - Timeout detection dead; SMBUS_TIMEOUT=0 wedges M_ERROR.
#           r_timeout_en is declared but never assigned anywhere in
#           smbus_core.sv (grep-verified: one declaration, one read
#           site, zero writes) - it is permanently 0, so
#           `if (rst || !r_timeout_en || ...) r_timeout_counter <= 0`
#           holds the counter at 0 forever and w_timeout can only ever
#           fire when cfg_timeout==0. A genuinely stuck bus never times
#           out, and cfg_timeout==0 (meant to disable the timeout) makes
#           w_timeout permanently true, so the "Global timeout check"
#           forces M_ERROR the instant ANY transaction starts.
#  3. H5  - Read protocols omit the repeated START / re-addressed read.
#           M_RESTART (4'hF) is defined in master_state_t but never
#           entered by any FSM case arm - dead state. r_rw_bit is
#           latched once at cmd_start and used for the FIRST address
#           byte (M_START loads {slave_addr, r_rw_bit}), so a Read Byte
#           transaction sends S+Addr+R directly instead of
#           S+Addr+W, cmd, Sr+Addr+R.
#  4. H6  - TX FIFO pushes stale data.
#           The next-byte reload (`shift_reg <= w_tx_fifo_rdata`) and
#           byte-counter increment are both gated on the transition
#           condition `r_master_state==M_DATA_WR && r_master_state_next
#           ==M_DATA_WR` - but the master FSM's M_DATA_WR case ALWAYS
#           routes to M_DATA_WR_ACK, never back to itself directly, so
#           that condition is structurally unreachable. r_shift_reg is
#           therefore never reloaded from the FIFO after the first data
#           byte, even though w_tx_fifo_rd (a separate, reachable
#           condition) keeps popping the FIFO every loop iteration -
#           FIFO bytes are silently discarded while the same stale byte
#           is repeated on the wire.
#  5. H7  - PEC generation garbage; PEC checking absent.
#           w_pec_data is wired to r_shift_reg and sampled when
#           bit_counter==8; by the last bit of any transmitted byte,
#           r_shift_reg has been left-shifted 8 times (each TX bit
#           shifts in a 0), so it reads 0x00 at exactly the moment the
#           PEC engine samples it - every byte gets XORed into the CRC
#           as 0x00 regardless of its real value. Separately,
#           r_pec_error is assigned only in the reset branch of the
#           "Status Register Updates" block (grep-verified) - nothing
#           ever sets it on a real mismatch.
#  6. H8  - SMBUS_DATA / SMBUS_PEC clobbered one cycle after a SW write.
#           Both fields are `hw=rw` in the RDL with only `.next` driven
#           (no `we`), so PeakRDL's hardware path overwrites the field
#           EVERY cycle unconditionally: hwif_in.SMBUS_DATA.data.next =
#           data_byte_in (= smbus_core's r_shift_reg) and
#           hwif_in.SMBUS_PEC.pec.next = pec_value (the live PEC
#           calculator output, held at 0 whenever idle since
#           w_pec_clear is true in S_IDLE). Any SW write is stomped the
#           very next clock.
#  7. qc1 - INT_STATUS never sticky; W1C ineffective.
#           Same "hw=w with only .next, no we" pattern: complete_int/
#           error_int are pulses (edge-detected each cycle) rewritten
#           every clock instead of only strobing hw once and letting SW
#           W1C hold it; tx_thresh_int/rx_thresh_int are wired straight
#           to the LIVE tx_fifo_empty/!rx_fifo_empty levels every cycle,
#           so a SW W1C write is undone on the very next clock
#           regardless of whether the underlying condition cleared.
#  8. qc2 - smb_interrupt bypasses INT_STATUS.
#           apb4_smbus.sv's `r_interrupt` is built directly from the raw
#           w_status_*/w_int_*_en wires (smbus_core/config_regs live
#           outputs), never from the registered INT_STATUS value - so
#           the pin follows live status, not (INT_STATUS & INT_ENABLE),
#           and a SW W1C on INT_STATUS has zero effect on it.
#  9. qc5 - Byte engine never transmits past the first data byte / block
#           write hangs. Direct consequence of the #4 dead-transition
#           bug: since r_byte_counter is only ever incremented on that
#           same unreachable M_DATA_WR->M_DATA_WR edge, it is stuck at 0
#           forever, so M_DATA_WR_ACK's `byte_counter >= bytes_total`
#           exit test is only ever true when bytes_total==0 - ANY
#           transaction needing >=1 data byte oscillates
#           M_DATA_WR <-> M_DATA_WR_ACK forever and never completes.
# 10. qc6 - r_bytes_total loaded from block_count for all transaction
#           types. The "Latch transaction parameters on START" block
#           does `r_bytes_total <= cmd_block_count` unconditionally,
#           with no case on cmd_trans_type, so Write Byte/Word inherit
#           whatever SMBUS_BLOCK_COUNT happens to hold instead of the
#           1/2 bytes their transaction type actually needs.
# 11. Strict decode - every unmapped address in the 4KB window must read
#           0 and return PSLVERR; writes ignored (RTC GH56 pattern).
#
# OPEN QUESTION (not a confirmed 12th item): while debugging why GH58-4/9
#           couldn't reach M_DATA_WR with only smb_sda_i forced low, a
#           hypothesis (master_state_next's *_ACK case arms reading a
#           stale r_ack_bit on entry) was investigated but NOT confirmed
#           - a differently-set-up whitebox run contradicted it (see
#           the comment above the removed test in this file's history /
#           the coordinator report for this round). Items #4/#9 avoid
#           the question entirely by forcing r_ack_bit itself
#           (`_force_permanent_ack_task`), which is unambiguous.
# ============================================================================

"""
SMBus GH#58 Medium-Level RED Regression Tests

These tests are written against the RTL AS IT EXISTS TODAY (no rtl/**
files touched) and are EXPECTED TO FAIL (RED) - each failure is the
mechanism-traced signature of one of the 11 GH#58 defect items above.
They exist to be routed to rds-rtl-design as findings, and to flip GREEN
once the corresponding RTL fix lands (at which point mutation-check
requires re-breaking the fix and re-confirming RED before trusting the
GREEN).

Framework note (dv-author non-negotiable: never hand-roll a driver/
monitor/decoder): all bus interaction goes through the RDS-DV
CocoTBFramework SMBusSlave/SMBusMonitor/SMBusCRC BFMs. Several of these
defects (most notably #1's frozen SCL) structurally prevent the
SMBusSlave BFM from ever completing an address-byte handshake with this
DUT (it blocks on RisingEdge(smb_scl_o), which never fires again after
the initial START edge) - so tests for the deeper, downstream defects
(#3/#4/#5/#9/#10) that need the master FSM to get past the address/ACK
phase use a documented whitebox override (holding smb_sda_i low) to
simulate a permanently-ACKing environment, instead of a hand-rolled
protocol responder: it is a static pin force, not a byte decoder, and it
exists specifically because defect #1 (covered by its own, independent
test) would otherwise mask every defect behind it. Items that do not
need to get past the address phase (open-drain/edge-count, timeout,
DATA/PEC register clobber, INT_STATUS stickiness, interrupt bypass,
strict decode) use the real BFMs / plain APB register access exactly as
the coordinator asked.

BFM gap found and fixed in the framework (not hand-rolled here):
SMBusSlave's `clock_stretch_cycles` constructor parameter was accepted
and stored but never used anywhere - clock stretching was structurally
unimplemented. Fixed in RTLDesignSherpa-DV's
CocoTBFramework/components/smbus/smbus_components.py (added
`clock_period_ns` and a `_stretch_clock_if_configured()` step invoked
from `_send_ack()`) and copied into the venv's editable-installed copy.
End-to-end exercise of the fixed behavior against this DUT is blocked by
defect #1 (the master never re-enters a bit-clock phase for a slave to
stretch against), so it is reported here as a framework fix, not folded
into a DUT pass/fail assertion.
"""

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge, FallingEdge

from projects.components.retro_legacy_blocks.dv.tbclasses.smbus.smbus_tb import SMBusRegisterMap
from CocoTBFramework.components.smbus import SMBusCRC, SMBusTransactionType
from CocoTBFramework.components.apb.apb_packet import APBPacket


# Master FSM state encoding (smbus_core.sv master_state_t) - mirrored here
# for whitebox assertions; NOT re-decoding the bus, just naming states
# already exposed either via u_smbus_core.r_master_state (whitebox) or
# via SMBUS_STATUS.fsm_state (register-level, same encoding).
M_IDLE = 0x0
M_START = 0x1
M_ADDR = 0x2
M_ADDR_ACK = 0x3
M_CMD = 0x4
M_CMD_ACK = 0x5
M_DATA_WR = 0x6
M_DATA_WR_ACK = 0x7
M_STOP = 0xD
M_ERROR = 0xE


class SMBusMediumTests:
    """GH#58 RED regression suite for apb4_smbus."""

    def __init__(self, tb):
        self.tb = tb
        self.log = tb.log

    # ------------------------------------------------------------------
    # Shared helpers
    # ------------------------------------------------------------------

    def _core(self):
        return self.tb.dut.u_smbus_core

    async def _recover_and_reset(self):
        """Baseline between GH58 tests: a REAL DUT reset, not a soft STOP.

        Bug fix (2026-09-09): a soft recovery (write COMMAND=STOP, write
        CONTROL=0, reset_fifos()) is NOT enough. Disabling cfg_master_en
        only gates the quarter-tick clock generator - it does not reset
        r_master_state/r_ack_bit/r_byte_counter etc (only the real `rst`
        does). GH58-9 deliberately drives the FSM into a permanent
        M_DATA_WR<->M_DATA_WR_ACK oscillation (that IS the bug under
        test); a soft "recovery" leaves that oscillation FROZEN-but-
        intact, and it silently RESUMES the moment any later test
        re-enables master_en - which corrupted an unrelated, pre-
        existing, untouched basic test (`test_fifo_full_detection`,
        intermittently "TX FIFO level wrong: got 31, expected 32" -
        one byte silently popped by the resumed oscillation) in the
        first post-fix full run. A real reset pulse is the only
        reliable way to guarantee no GH58 test's deliberately-broken
        state can leak into a later test.
        """
        self.tb.dut.smb_sda_i.value = 1
        await self.tb.assert_reset()
        await ClockCycles(self.tb.pclk, 10)
        await self.tb.deassert_reset()
        await ClockCycles(self.tb.pclk, 5)
        await self.tb.apb4_master.reset_bus()
        await self.tb.reset_fifos()
        await ClockCycles(self.tb.pclk, 10)

    def _force_permanent_ack(self):
        """Whitebox stimulus: hold smb_sda_i low for the rest of a test.

        Defect #1's dead SCL generation structurally prevents the
        framework's SMBusSlave BFM from ever completing an address-byte
        reception (it blocks on RisingEdge(smb_scl_o), which never
        fires again after the initial START edge), so it can never
        drive a real ACK. This is a static pin override, retained for
        tests (#1/#2/#3) that only need the address phase's shift
        register/timing, not real progress past it. It is NOT sufficient
        on its own to get a transaction past M_ADDR_ACK - see
        `_force_permanent_ack_task()` and GH58-NEW1 below.
        """
        self.tb.dut.smb_sda_i.value = 0

    def _force_permanent_ack_task(self):
        """Whitebox stimulus: continuously force r_ack_bit=0 (ACK) inside
        smbus_core, for tests that need the master FSM to actually
        progress past M_ADDR_ACK/M_CMD_ACK/M_DATA_WR_ACK (items #4/#9).

        Diagnosis (2026-09-09, found while debugging why GH58-4/9 could
        not observe their target states even with `_force_permanent_ack`
        holding smb_sda_i low the entire time): this is a SEPARATE,
        newly-found RTL defect, not one of GH#58's original 11 items -
        see GH58-NEW1's test for the writeup. In short:
        master_state_next's M_ADDR_ACK/M_CMD_ACK/M_DATA_WR_ACK/
        M_PEC_WR_ACK case arms check r_ack_bit COMBINATIONALLY on the
        very first cycle the FSM enters that state - before the internal
        PHY_BIT_RX bit-sampling sequence (which takes several more
        cycles to actually run) has any chance to update it - so every
        ACK check reads the STALE r_ack_bit (1=NAK at reset, and it is
        never freshly resampled, because the FSM has already moved on to
        M_ERROR one cycle later, abandoning the sampling sequence before
        it starts). Whitebox-confirmed: smb_sda_i reads 0 throughout via
        `_force_permanent_ack`, yet r_ack_bit reads 1 throughout, and
        r_master_state only ever visits {M_ADDR, M_ADDR_ACK, M_ERROR}.
        Forcing the register directly is the only way to reach the
        downstream states items #4/#9 need to inspect.
        """
        core = self._core()

        async def _drive():
            while True:
                await RisingEdge(self.tb.pclk)
                core.r_ack_bit.value = 0

        return cocotb.start_soon(_drive())

    # ==================================================================
    # Item 1 (C4): SCL never toggles / not open-drain
    # ==================================================================

    # ------------------------------------------------------------------
    # RLB-011: slave (target) mode
    # ------------------------------------------------------------------

    @staticmethod
    def _crc8(data) -> int:
        """SMBus PEC: CRC-8, polynomial 0x07, seed 0."""
        crc = 0
        for byte in data:
            crc ^= byte & 0xFF
            for _ in range(8):
                crc = ((crc << 1) ^ 0x07) & 0xFF if (crc & 0x80) else ((crc << 1) & 0xFF)
        return crc

    async def _slave_setup(self, addr=0x42, **kwargs):
        """Reset, then arm the target engine. Every slave test starts here so
        none of them inherits another one's FIFO or sticky status."""
        await self._recover_and_reset()
        await self.tb.configure_clock(clk_div=249)
        await self.tb.enable_slave_mode(enable=True, own_addr=addr, **kwargs)
        await self.tb.write_register(SMBusRegisterMap.SMBUS_INT_STATUS, 0xFF)
        await ClockCycles(self.tb.pclk, 50)

    async def test_rlb011_slave_write_and_address_match(self) -> bool:
        """RLB-011: a foreign master writes to us, and only to us.

        The address byte is answered by the engine, not by software, so the
        thing under test is the match itself: our own address is ACKed and
        the byte stream lands in the RX FIFO; a neighbour's address is NAKed
        and nothing lands at all."""
        self.log.info("=== RLB-011: slave address match and write path ===")
        M = SMBusRegisterMap
        try:
            # --- addressed to us
            await self._slave_setup(addr=0x42)
            acks = await self.tb.ext_master.write_raw(0x42, [0xA5, 0x5A])
            await ClockCycles(self.tb.pclk, 50)
            fifo = await self.tb.read_fifo_status()
            got = await self.tb.read_rx_fifo(fifo['rx_level'])
            ints = await self.tb.read_interrupt_status()
            self.log.info(f"  to 0x42: acks={acks} rx={[hex(b) for b in got]} "
                          f"int_status=0x{ints:02X}")
            ours_ok = (acks == [True, True, True] and got == [0xA5, 0x5A] and
                       bool(ints & M.INT_SLAVE_ADDR_EN) and
                       bool(ints & M.INT_SLAVE_RX_EN) and
                       bool(ints & M.INT_SLAVE_DONE_EN))

            # --- addressed to somebody else
            await self._slave_setup(addr=0x42)
            acks2 = await self.tb.ext_master.write_raw(0x43, [0x11])
            await ClockCycles(self.tb.pclk, 50)
            fifo2 = await self.tb.read_fifo_status()
            ints2 = await self.tb.read_interrupt_status()
            self.log.info(f"  to 0x43: acks={acks2} rx_level={fifo2['rx_level']} "
                          f"int_status=0x{ints2:02X}")
            theirs_ok = (acks2[0] is False and fifo2['rx_level'] == 0 and
                         not (ints2 & M.INT_SLAVE_ADDR_EN))

            # --- software says it is busy
            await self._slave_setup(addr=0x42, nack_all=True)
            acks3 = await self.tb.ext_master.write_raw(0x42, [0x22])
            await ClockCycles(self.tb.pclk, 50)
            fifo3 = await self.tb.read_fifo_status()
            self.log.info(f"  to 0x42 with nack_all: acks={acks3} "
                          f"rx_level={fifo3['rx_level']}")
            busy_ok = (acks3[0] is False and fifo3['rx_level'] == 0)

            # --- general call
            await self._slave_setup(addr=0x42, gc=True)
            acks4 = await self.tb.ext_master.write_raw(0x00, [0x33])
            await ClockCycles(self.tb.pclk, 50)
            fifo4 = await self.tb.read_fifo_status()
            got4 = await self.tb.read_rx_fifo(fifo4['rx_level'])
            self.log.info(f"  general call: acks={acks4} rx={[hex(b) for b in got4]}")
            gc_ok = (acks4 == [True, True] and got4 == [0x33])

            ok = ours_ok and theirs_ok and busy_ok and gc_ok
            if ok:
                self.log.info("RLB-011 slave address match and write GREEN")
                return True
            self.log.error(
                f"RLB-011 slave write: own_address={ours_ok} "
                f"other_address_ignored={theirs_ok} nack_all={busy_ok} "
                f"general_call={gc_ok}")
            return False
        except Exception as e:
            self.log.error(f"RLB-011 slave write test error: {e}")
            return False
        finally:
            await self._recover_and_reset()

    async def test_rlb011_slave_read_and_stretch(self) -> bool:
        """RLB-011: a foreign master reads from us, with and without a queue.

        A target that is read has to produce bytes on somebody else's clock.
        With data already queued it just sends it. With the queue empty it has
        two honest answers, and which one it gives is
        SMBUS_SLAVE_CTRL.stretch_en: hold the clock until software catches up,
        or send 0xFF and let the bus carry on."""
        self.log.info("=== RLB-011: slave read path and clock stretching ===")
        M = SMBusRegisterMap
        try:
            # --- queued data
            await self._slave_setup(addr=0x42)
            await self.tb.write_tx_fifo([0x11, 0x22])
            acked, data = await self.tb.ext_master.read_raw(0x42, 2)
            await ClockCycles(self.tb.pclk, 50)
            self.log.info(f"  queued read: addr_acked={acked} "
                          f"data={[hex(b) for b in data]}")
            queued_ok = acked and data == [0x11, 0x22]

            # --- empty queue, stretching OFF: 0xFF rather than a held bus
            await self._slave_setup(addr=0x42, stretch=False)
            acked2, data2 = await self.tb.ext_master.read_raw(0x42, 1)
            self.log.info(f"  dry read, no stretch: addr_acked={acked2} "
                          f"data={[hex(b) for b in data2]}")
            dry_ok = acked2 and data2 == [0xFF]

            # --- empty queue, stretching ON: the bus waits for software
            await self._slave_setup(addr=0x42, stretch=True)
            reader = cocotb.start_soon(self.tb.ext_master.read_raw(0x42, 1))
            saw_stretch = False
            for _ in range(400):
                st = await self.tb.read_slave_status()
                if st['stretching']:
                    saw_stretch = True
                    break
                await ClockCycles(self.tb.pclk, 20)
            # HOLD, and hold long enough to matter. A stretch that software
            # releases within one bit time proves nothing: a master that
            # ignored the stretch entirely would still line up by accident.
            # Ten SCL periods is longer than the whole remaining byte, so a
            # master that clocked through would have finished sending
            # nothing into a bus that was never moving.
            await ClockCycles(self.tb.pclk, 5000)
            still_held = (await self.tb.read_slave_status())['stretching']
            # Only now does software produce the byte, which is the whole
            # point: the master could not have had it any earlier.
            await self.tb.write_tx_fifo([0x77])
            acked3, data3 = await reader
            self.log.info(f"  dry read, stretching: held={saw_stretch} "
                          f"still_held_after_10_periods={still_held} "
                          f"addr_acked={acked3} data={[hex(b) for b in data3]}")
            stretch_ok = (saw_stretch and still_held and acked3 and
                          data3 == [0x77])

            ok = queued_ok and dry_ok and stretch_ok
            if ok:
                self.log.info("RLB-011 slave read and stretch GREEN")
                return True
            self.log.error(
                f"RLB-011 slave read: queued={queued_ok} dry_sends_FF={dry_ok} "
                f"stretched_until_software_answered={stretch_ok} "
                f"(held={saw_stretch} still_held={still_held} "
                f"data={[hex(b) for b in data3]}, want [0x77])")
            return False
        except Exception as e:
            self.log.error(f"RLB-011 slave read test error: {e}")
            return False
        finally:
            await self._recover_and_reset()

    async def test_rlb011_slave_pec_and_ownership(self) -> bool:
        """RLB-011: the target's own PEC, and one engine on the wire.

        The slave PEC never counts bytes. On a write a correct trailing PEC
        drives the running CRC to zero, so 'good' is 'zero at the STOP'; on a
        read the running CRC IS the byte to send once the queue is dry. And
        while the target is answering, the master half must refuse to start,
        or this block would be on the bus twice."""
        self.log.info("=== RLB-011: slave PEC and engine ownership ===")
        M = SMBusRegisterMap
        try:
            # --- a write with a correct PEC
            payload = [0xDE, 0xAD]
            good_pec = self._crc8([(0x42 << 1) | 0] + payload)
            await self._slave_setup(addr=0x42, pec=True)
            await self.tb.ext_master.write_raw(0x42, payload + [good_pec])
            await ClockCycles(self.tb.pclk, 50)
            st_good = await self.tb.read_slave_status()
            self.log.info(f"  good PEC 0x{good_pec:02X}: pec_error="
                          f"{st_good['pec_error']} running=0x"
                          f"{st_good['pec_value']:02X}")

            # --- the same write with the PEC byte corrupted
            await self._slave_setup(addr=0x42, pec=True)
            await self.tb.ext_master.write_raw(
                0x42, payload + [(good_pec ^ 0xFF) & 0xFF])
            await ClockCycles(self.tb.pclk, 50)
            st_bad = await self.tb.read_slave_status()
            self.log.info(f"  bad PEC: pec_error={st_bad['pec_error']}")

            # --- a read: the byte after the queue runs dry is the PEC
            await self._slave_setup(addr=0x42, pec=True)
            await self.tb.write_tx_fifo([0x5A])
            acked, data = await self.tb.ext_master.read_raw(0x42, 2)
            expect_pec = self._crc8([(0x42 << 1) | 1, 0x5A])
            self.log.info(f"  read with PEC: data={[hex(b) for b in data]} "
                          f"expected trailing PEC=0x{expect_pec:02X}")
            read_pec_ok = acked and len(data) == 2 and data[0] == 0x5A and \
                data[1] == expect_pec

            # --- ownership: no master START while the target is answering
            await self._slave_setup(addr=0x42, stretch=True)
            reader = cocotb.start_soon(self.tb.ext_master.read_raw(0x42, 1))
            held = False
            for _ in range(400):
                st = await self.tb.read_slave_status()
                if st['stretching']:
                    held = True
                    break
                await ClockCycles(self.tb.pclk, 20)
            # The target is mid-transfer. Ask the master half to go.
            await self.tb.enable_master_mode(enable=True)
            await self.tb.start_transaction(trans_type=0x9, slave_addr=0x55)
            await ClockCycles(self.tb.pclk, 200)
            mstatus = await self.tb.read_status()
            master_refused = not mstatus['busy']
            self.log.info(f"  ownership: target holding={held} "
                          f"master_busy={mstatus['busy']} (want False)")
            # Let the target finish so the bus is not left held.
            await self.tb.write_tx_fifo([0x00])
            await reader

            ok = ((not st_good['pec_error']) and st_bad['pec_error'] and
                  read_pec_ok and held and master_refused)
            if ok:
                self.log.info("RLB-011 slave PEC and ownership GREEN")
                return True
            self.log.error(
                f"RLB-011 slave PEC: good_pec_clean={not st_good['pec_error']} "
                f"bad_pec_flagged={st_bad['pec_error']} "
                f"read_appends_pec={read_pec_ok} target_held={held} "
                f"master_refused_while_target_busy={master_refused}")
            return False
        except Exception as e:
            self.log.error(f"RLB-011 slave PEC test error: {e}")
            return False
        finally:
            await self._recover_and_reset()

    async def test_gh58_c4_scl_toggle_and_open_drain(self) -> bool:
        """SCL must clock every bit (>=9 edges/byte) and stay open-drain."""
        self.log.info("=== GH58-1 (C4): SCL toggle count + open-drain contract ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=4)
            await self.tb.configure_timeout(timeout=200000)

            await self.tb.write_data_byte(0xAB)
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x10)

            prev_scl = int(self.tb.dut.smb_scl_o.value)
            rise_events = 0
            odrain_violations = 0

            for i in range(500):
                await RisingEdge(self.tb.pclk)
                cur_scl = int(self.tb.dut.smb_scl_o.value)
                if cur_scl == 1 and prev_scl == 0:
                    rise_events += 1
                prev_scl = cur_scl

                if int(self.tb.dut.smb_scl_t.value) == 0 and cur_scl == 1:
                    odrain_violations += 1
                if (int(self.tb.dut.smb_sda_t.value) == 0
                        and int(self.tb.dut.smb_sda_o.value) == 1):
                    odrain_violations += 1

                # Force a STOP partway through so PHY_STOP (where the
                # open-drain violation lives) actually gets exercised
                # even though the address NAKs (no BFM ack) and parks
                # in M_ERROR long before a real STOP would occur.
                if i == 450:
                    await self.tb.write_register(
                        SMBusRegisterMap.SMBUS_COMMAND,
                        SMBusRegisterMap.COMMAND_STOP)

            self.log.info(f"  SCL rising edges observed: {rise_events} "
                           f"(need >=9 for one byte+ACK)")
            self.log.info(f"  open-drain violations (_t=0 while _o=1): "
                           f"{odrain_violations}")

            if rise_events < 9:
                self.log.error(
                    f"GH58 item 1 (C4): expected >=9 SCL rising edges for one "
                    f"address byte + ACK, observed {rise_events}. "
                    f"smbus_core.sv's PHY_BIT_TX/PHY_BIT_RX never assign "
                    f"r_scl_out (only PHY_START/PHY_STOP do), so smb_scl_o "
                    f"freezes low after the initial START edge.")
                return False

            if odrain_violations > 0:
                self.log.error(
                    f"GH58 item 1 (C4): {odrain_violations} cycles observed "
                    f"with an SMBus line actively driven high (_t=0, _o=1) "
                    f"instead of released (_t=1) - open-drain violation "
                    f"during PHY_STOP's SDA-release sub-phase.")
                return False

            self.log.warning("GH58-1 unexpectedly GREEN")
            return True

        except Exception as e:
            self.log.error(f"GH58-1 test error: {e}")
            return False

    # ==================================================================
    # Item 2 (C3): timeout detection dead / SMBUS_TIMEOUT=0 wedges M_ERROR
    # ==================================================================

    async def test_gh58_c3_timeout_detection_dead(self) -> bool:
        """A slave stretching past SMBUS_TIMEOUT must time out; TIMEOUT=0
        must mean disabled and let the stretched transaction complete.

        Rewrite (2026-09-09, coordinator round 2): the original sub-A used
        no slave at all and relied on a plain address NAK to reach
        M_ERROR/busy=0 - that is the NAK path (see GH58-11's own defect,
        now fixed), not the timeout path, and it passed for the wrong
        reason once the RTL rewrite landed. The TB's open-drain wiring
        also tied smb_scl_i to the slave BFM's last commanded value only
        (see smbus_tb.py's _bus_model_loop), so a slave actually holding
        SCL low (stretching) was never modeled either. Both are fixed
        now: this drives a REAL SMBusSlave with clock_stretch_cycles set
        past (sub-A) and under (sub-B) SMBUS_TIMEOUT, through the real
        wired-AND bus model.
        """
        self.log.info("=== GH58-2 (C3): timeout via real SCL stretch; TIMEOUT=0 disables it ===")
        try:
            await self._recover_and_reset()

            # --- Sub-test A: stretch (15us) exceeds SMBUS_TIMEOUT (5us) ---
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=500)  # 500 core clocks = 5us @ 10ns/clk
            await self.tb.enable_interrupts(error=True)
            await self.tb.write_data_byte(0x5A)

            self.tb.smbus_slave.clock_stretch_cycles = 1500  # 15us @ clock_period_ns=10
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()

            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x01)

            # timeout_error can latch well before busy drops: M_ERROR's own
            # STOP still has to release SCL, and the slave is still
            # stretching (a fixed-duration Timer, oblivious to the
            # master's timeout) until its own 15us elapses - a real
            # open-drain bus cannot complete a STOP while another device
            # holds SCL low. So keep polling for busy==0 too, not just a
            # short fixed margin after timeout_error first appears.
            #
            # Whitebox polling (core.status_* wires directly), NOT a
            # per-cycle APB read: an APB round trip is several pclk cycles
            # on its own, so polling read_status() every RisingEdge blew
            # the shared 500us cocotb test-level timeout budget across the
            # whole suite on the first attempt at this rewrite.
            core = self._core()
            timeout_seen = False
            for _ in range(6000):  # 60us of pclk edges, comfortably past the 15us stretch
                await RisingEdge(self.tb.pclk)
                if int(core.status_timeout_error.value):
                    timeout_seen = True
                if timeout_seen and not int(core.status_busy.value):
                    break
            status_after = await self.tb.read_status()
            int_status_after = await self.tb.read_interrupt_status()
            bus_released = (int(self.tb.dut.smb_scl_t.value) == 1 and
                             int(self.tb.dut.smb_sda_t.value) == 1)

            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()

            self.log.info(f"  sub-A: timeout_error seen={timeout_seen}, "
                           f"status_after={status_after}, "
                           f"INT_STATUS.error={bool(int_status_after & 0x02)}, "
                           f"bus_released={bus_released}")

            sub_a_pass = (timeout_seen and not status_after['busy'] and
                          (int_status_after & 0x02) and bus_released)
            if not sub_a_pass:
                self.log.error(
                    f"GH58 item 2 (C3) sub-A: slave stretched SCL for 15us "
                    f"against SMBUS_TIMEOUT=500 clocks (5us); expected "
                    f"status_timeout_error, INT_STATUS.error set, busy=0 and "
                    f"the bus released. Mechanism (matches coordinator H3): "
                    f"when w_phy_timeout fires, smbus_core issues a "
                    f"single-cycle r_phy_req for PHY_OP_STOP, but "
                    f"smbus_bit_phy only samples op_req while `!r_active` - "
                    f"the PHY is still active, mid the stretched primitive "
                    f"the timeout itself is about, so the STOP request is "
                    f"silently dropped. busy only clears once the ORIGINAL "
                    f"(non-STOP) primitive eventually completes on its own "
                    f"(when the slave's stretch elapses), leaving SCL/SDA "
                    f"wherever that primitive left them - never a real STOP. "
                    f"Got timeout_error observed="
                    f"{timeout_seen}, final status={status_after}, "
                    f"INT_STATUS=0x{int_status_after:02X}, "
                    f"bus_released={bus_released}.")

            await self._recover_and_reset()

            # --- Sub-test B: TIMEOUT=0 (disabled) must let the SAME stretch
            # complete normally once the slave releases. Quick Command (a
            # single address-only ACK) rather than Write Byte: the BFM's
            # stretch fires on EVERY ACK it sends, and with three ACKs
            # (address/cmd/data) all stretching, cumulative timing pushed
            # this into the same "did it really NAK" territory as GH58-12 -
            # a single, unambiguous stretch isolates the timeout-vs-stretch
            # contract this sub-test is actually about.
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=0)

            self.tb.smbus_slave.clock_stretch_cycles = 1500  # same 15us stretch
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()

            await self.tb.start_transaction(SMBusRegisterMap.TRANS_QUICK_CMD, 0x50)

            completed = False
            for _ in range(6000):  # 60us, whitebox polling (see sub-A note)
                await RisingEdge(self.tb.pclk)
                if int(core.status_complete.value):
                    completed = True
                    break
                if (int(core.status_bus_error.value) or
                        int(core.status_timeout_error.value) or
                        int(core.status_pec_error.value)):
                    break

            status_b = await self.tb.read_status()
            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()

            self.log.info(f"  sub-B: TIMEOUT=0, stretched 15us -> "
                           f"completed={completed}, status={status_b}")

            sub_b_pass = completed and not status_b['timeout_error']
            if not sub_b_pass:
                self.log.error(
                    f"GH58 item 2 (C3) sub-B: SMBUS_TIMEOUT=0 must mean "
                    f"disabled - a transaction against a slave stretching "
                    f"for 15us should complete once the slave releases, not "
                    f"time out or error. Got completed={completed}, "
                    f"status={status_b}.")

            await self._recover_and_reset()

            if not (sub_a_pass and sub_b_pass):
                return False
            self.log.info("GH58-2 GREEN: real SCL-stretch timeout detected "
                           "(sub-A) and TIMEOUT=0 correctly disables it (sub-B)")
            return True

        except Exception as e:
            self.log.error(f"GH58-2 test error: {e}")
            return False

    # ==================================================================
    # Item 12 (new, coordinator round 2): a slave stretch SHORTER than
    # SMBUS_TIMEOUT delays the byte but the transaction still completes
    # cleanly - proves the PHY genuinely waits for SCL high rather than
    # merely tolerating short stalls by coincidence.
    # ==================================================================

    async def test_gh58_12_short_stretch_completes_without_error(self) -> bool:
        """A stretch shorter than SMBUS_TIMEOUT must not cause any error."""
        self.log.info("=== GH58-12: short SCL stretch (< TIMEOUT) completes cleanly ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=3000)  # 30us, comfortably above the stretch

            self.tb.smbus_slave.clock_stretch_cycles = 800  # 8us < 30us timeout

            # Quick Command (single address-only ACK), not Write Byte: the
            # BFM's stretch fires on every ACK it sends, and three
            # compounding 8us stretches (address/cmd/data) is a different,
            # confusing question from the one this test asks. One ACK, one
            # stretch, one unambiguous measurement.
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()

            core = self._core()
            start_time_ns = cocotb.utils.get_sim_time('ns')
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_QUICK_CMD, 0x50)

            # Whitebox polling (see GH58-2's note): a per-cycle APB read
            # here blows the suite's shared 500us cocotb timeout budget.
            completed = False
            for _ in range(4000):  # 40us
                await RisingEdge(self.tb.pclk)
                if int(core.status_complete.value):
                    completed = True
                    break
                if (int(core.status_bus_error.value) or
                        int(core.status_timeout_error.value) or
                        int(core.status_pec_error.value)):
                    break

            end_time_ns = cocotb.utils.get_sim_time('ns')
            status_final = await self.tb.read_status()

            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            await self._recover_and_reset()

            elapsed_ns = end_time_ns - start_time_ns
            self.log.info(f"  completed={completed}, elapsed={elapsed_ns}ns "
                           f"(stretch alone was 8000ns), status={status_final}")

            no_errors = not (status_final['bus_error'] or
                              status_final['timeout_error'] or
                              status_final['pec_error'] or
                              status_final['nak_received'])
            # The elapsed time must be AT LEAST the stretch duration - if the
            # PHY did not really wait for SCL to read high, the transaction
            # would finish in a few hundred ns regardless of the stretch.
            stretch_honored = elapsed_ns >= 8000

            if completed and no_errors and stretch_honored:
                self.log.info("GH58-12 GREEN: short stretch delayed the byte "
                               "but the transaction completed with no error")
                return True

            self.log.error(
                f"GH58-12: a slave stretch (8us) shorter than SMBUS_TIMEOUT "
                f"(30us) must delay but not fail the transaction. Got "
                f"completed={completed}, no_errors={no_errors}, "
                f"elapsed={elapsed_ns}ns (expected >= 8000ns - "
                f"stretch_honored={stretch_honored}), status={status_final}.")
            return False

        except Exception as e:
            self.log.error(f"GH58-12 test error: {e}")
            return False

    # ==================================================================
    # Item 3 (H5): read protocols omit repeated START / re-addressed read
    # ==================================================================

    async def test_gh58_h5_read_missing_repeated_start(self) -> bool:
        """Read Byte must send S+Addr+W, cmd, Sr+Addr+R - not S+Addr+R."""
        self.log.info("=== GH58-3 (H5): read protocols missing repeated START ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=4)
            await self.tb.configure_timeout(timeout=200000)

            core = self._core()

            # Bug fix (2026-09-09, first run against real RTL): a 20-cycle
            # poll window STARTED AFTER start_transaction() returned missed
            # M_ADDR entirely (rw_bit_in_first_addr_byte stayed None, so the
            # `== 1` check was vacuously False -> false GREEN). The two APB
            # writes inside start_transaction() (SLAVE_ADDR, then COMMAND)
            # already consume enough cycles that M_ADDR can be entered and
            # even fully transited before this method gets control back.
            # Fix: launch the watcher BEFORE issuing the transaction so it
            # runs concurrently with the APB handshakes and catches M_ADDR
            # whenever it actually occurs, with a generous 300-cycle budget.
            captured = {'rw': None}

            async def _watch_first_addr_rw():
                for _ in range(300):
                    await RisingEdge(self.tb.pclk)
                    if int(core.r_master_state.value) == M_ADDR:
                        captured['rw'] = int(core.r_shift_reg.value) & 0x01
                        return

            watcher = cocotb.start_soon(_watch_first_addr_rw())
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_READ_BYTE,
                                             0x50, command=0x22)
            await watcher.join()

            rw_bit_in_first_addr_byte = captured['rw']

            self.log.info(f"  First address byte R/W bit for Read Byte: "
                           f"{rw_bit_in_first_addr_byte} (spec requires 0=W "
                           f"here; the read-addressed byte only comes after "
                           f"a repeated START)")

            # Bus-level corroboration (best-effort - defect #1 means this
            # will not complete cleanly either, since the BFM can never
            # ACK); recorded for evidence, not gating pass/fail below.
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()
            self.tb.smbus_slave.write_memory(0x22, [0x99])
            success, _ = await self.tb.read_byte_data(0x50, 0x22)
            self.log.info(f"  Bus-level Read Byte completion: {success} "
                           f"(monitor saw {len(self.tb.smbus_monitor.recv_queue)} "
                           f"packet(s), none of which can show a repeated "
                           f"START while this defect and #1 both stand)")
            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()

            await self._recover_and_reset()

            if rw_bit_in_first_addr_byte == 1:
                self.log.error(
                    "GH58 item 3 (H5): Read Byte's FIRST address byte was "
                    "sent with R/W=1 (read) instead of R/W=0 (write, to "
                    "address the command-byte phase). smbus_core.sv latches "
                    "r_rw_bit once at cmd_start from cmd_trans_type and uses "
                    "it for the very first address load in M_START; "
                    "M_RESTART (repeated START) is defined but never entered "
                    "by any FSM case arm, so no S+Addr+W, cmd, Sr+Addr+R "
                    "sequence is ever generated.")
                return False

            if rw_bit_in_first_addr_byte is None:
                self.log.error(
                    "GH58 item 3 (H5) test infrastructure: watcher never "
                    "observed r_master_state==M_ADDR within 300 pclk cycles "
                    "of issuing a Read Byte transaction - cannot judge the "
                    "R/W bit this run. Treating as RED pending investigation "
                    "(this is a test-timing gap, not confirmation the RTL "
                    "is correct).")
                return False

            self.log.warning("GH58-3 unexpectedly GREEN")
            return True

        except Exception as e:
            self.log.error(f"GH58-3 test error: {e}")
            return False

    # ==================================================================
    # Item 4 (H6): TX FIFO pushes stale data
    # ==================================================================

    async def test_gh58_h6_tx_fifo_stale_data(self) -> bool:
        """FIFO bytes must reach the wire in order; none may be discarded."""
        self.log.info("=== GH58-4 (H6): TX FIFO pushes stale data ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.reset_fifos()

            await self.tb.set_block_count(3)
            await self.tb.write_tx_fifo([0xAA, 0xBB, 0xCC])
            await self.tb.write_data_byte(0x11)  # sentinel "first sent byte"

            # Bug fix (2026-09-09): pin-level `_force_permanent_ack()`
            # alone never gets the FSM past M_ADDR_ACK at all (see
            # GH58-NEW1) - use the register-level force instead so this
            # test can reach the M_DATA_WR states it actually needs to
            # inspect.
            ack_task = self._force_permanent_ack_task()
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_BLOCK_WRITE,
                                             0x50, command=0x30)

            core = self._core()

            # Widened window (900 cycles) to guarantee several M_DATA_WR
            # loop passes once the FSM can actually reach that state; the
            # real bug signature is that r_shift_reg NEVER takes any of
            # the actual FIFO payload values (0xAA/0xBB/0xCC) even as the
            # FIFO level keeps dropping.
            observed_shift_reg_values = set()
            for _ in range(900):
                await RisingEdge(self.tb.pclk)
                observed_shift_reg_values.add(int(core.r_shift_reg.value))

            fifo_status = await self.tb.read_fifo_status()

            ack_task.kill()
            self.tb.dut.smb_sda_i.value = 1
            await self._recover_and_reset()

            payload_bytes_seen = observed_shift_reg_values & {0xAA, 0xBB, 0xCC}
            self.log.info(f"  After 900 cycles (multiple M_DATA_WR loop "
                           f"passes): r_shift_reg took values "
                           f"{sorted(hex(v) for v in observed_shift_reg_values)}, "
                           f"real FIFO payload bytes among them: "
                           f"{sorted(hex(v) for v in payload_bytes_seen)}, "
                           f"TX FIFO level={fifo_status['tx_level']} "
                           f"(started at 3)")

            fifo_silently_drained = fifo_status['tx_level'] < 3
            wire_never_advanced = len(payload_bytes_seen) == 0

            if fifo_silently_drained and wire_never_advanced:
                self.log.error(
                    "GH58 item 4 (H6): TX FIFO level dropped from 3 to "
                    f"{fifo_status['tx_level']} (bytes silently popped) over "
                    f"900 pclk cycles, yet r_shift_reg (the byte actually "
                    f"being transmitted) never once took any of the real "
                    f"FIFO payload values (0xAA/0xBB/0xCC) - only "
                    f"{sorted(hex(v) for v in observed_shift_reg_values)} "
                    f"were observed. smbus_core.sv's next-byte reload "
                    "(`shift_reg <= w_tx_fifo_rdata`) is gated on "
                    "`r_master_state==M_DATA_WR && r_master_state_next=="
                    "M_DATA_WR`, a transition the master FSM's M_DATA_WR case "
                    "never produces (it always goes to M_DATA_WR_ACK), while "
                    "w_tx_fifo_rd (a separately-reachable condition) keeps "
                    "popping the FIFO every loop pass regardless.")
                return False

            self.log.warning("GH58-4 unexpectedly GREEN "
                              f"(fifo_silently_drained={fifo_silently_drained}, "
                              f"payload_bytes_seen={sorted(hex(v) for v in payload_bytes_seen)})")
            return True

        except Exception as e:
            self.log.error(f"GH58-4 test error: {e}")
            return False

    # ==================================================================
    # Item 5 (H7): PEC generation garbage; PEC checking absent
    # ==================================================================

    async def test_gh58_h7_pec_generation_and_checking(self) -> bool:
        """PEC must be the real CRC-8 over the bytes sent; errors must be caught."""
        self.log.info("=== GH58-5 (H7): PEC generation garbage / checking absent ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True, use_pec=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)

            core = self._core()
            await self.tb.write_data_byte(0x11)
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x40)

            # Wait for the address byte's 8th bit (where the PEC engine
            # samples w_pec_data == r_shift_reg for the first time).
            pec_value_at_byte_end = None
            expected_addr_byte = (0x50 << 1) | 0  # write
            for _ in range(60):
                await RisingEdge(self.tb.pclk)
                if (int(core.r_master_state.value) == M_ADDR
                        and int(core.r_bit_counter.value) == 8):
                    pec_value_at_byte_end = int(core.pec_value.value)
                    break

            expected_pec_after_one_byte = SMBusCRC.calculate([expected_addr_byte])
            self.log.info(f"  PEC after address byte: got "
                           f"0x{(pec_value_at_byte_end or 0):02X}, "
                           f"SMBusCRC over [0x{expected_addr_byte:02X}] = "
                           f"0x{expected_pec_after_one_byte:02X}")

            pec_garbage = (pec_value_at_byte_end is not None
                            and pec_value_at_byte_end != expected_addr_byte
                            and expected_pec_after_one_byte != 0)
            # (expected_pec_after_one_byte is never 0 for a nonzero address
            # byte under a real CRC-8/0x07 calc, so any 0x00 readback here
            # is itself the smoking gun.)
            pec_reads_zero = pec_value_at_byte_end == 0x00

            await self._recover_and_reset()

            if pec_reads_zero:
                self.log.error(
                    f"GH58 item 5 (H7): PEC value after transmitting the "
                    f"address byte 0x{expected_addr_byte:02X} reads 0x00; "
                    f"SMBusCRC.calculate([0x{expected_addr_byte:02X}]) = "
                    f"0x{expected_pec_after_one_byte:02X}. smbus_core.sv "
                    f"wires w_pec_data to r_shift_reg and samples it when "
                    f"bit_counter==8 - but by then r_shift_reg has been "
                    f"left-shifted 8 times (shifting in 0 each time TX'd a "
                    f"bit) and reads 0x00, so every byte is XORed into the "
                    f"CRC as 0x00 regardless of its real value.")
                # Also confirm PEC-error checking is absent: r_pec_error is
                # only ever assigned in the module's reset branch.
                self.log.error(
                    "GH58 item 5 (H7): r_pec_error is assigned only in "
                    "smbus_core.sv's reset branch (grep-verified) - nothing "
                    "in the module ever sets it on a PEC mismatch, so "
                    "status_pec_error can never report a real PEC error.")
                return False

            self.log.warning("GH58-5 unexpectedly GREEN")
            return True

        except Exception as e:
            self.log.error(f"GH58-5 test error: {e}")
            return False

    # ==================================================================
    # Item 6 (H8 / qc4): SMBUS_DATA / SMBUS_PEC clobbered one cycle later
    # ==================================================================

    async def test_gh58_h8_data_pec_clobbered(self) -> bool:
        """A SW write to DATA/PEC must survive readback, not just the same cycle."""
        self.log.info("=== GH58-6 (H8/qc4): SMBUS_DATA / SMBUS_PEC clobbered ===")
        try:
            await self._recover_and_reset()

            await self.tb.write_register(SMBusRegisterMap.SMBUS_DATA, 0x77)
            await ClockCycles(self.tb.pclk, 3)
            _, data_readback = await self.tb.read_register(SMBusRegisterMap.SMBUS_DATA)
            data_readback &= 0xFF

            await self.tb.write_register(SMBusRegisterMap.SMBUS_PEC, 0x55)
            await ClockCycles(self.tb.pclk, 3)
            _, pec_readback = await self.tb.read_register(SMBusRegisterMap.SMBUS_PEC)
            pec_readback &= 0xFF

            self.log.info(f"  Wrote DATA=0x77, read back 0x{data_readback:02X} "
                           f"after 3 cycles")
            self.log.info(f"  Wrote PEC=0x55, read back 0x{pec_readback:02X} "
                           f"after 3 cycles")

            data_clobbered = data_readback != 0x77
            pec_clobbered = pec_readback != 0x55

            if data_clobbered or pec_clobbered:
                self.log.error(
                    f"GH58 item 6 (H8/qc4): SMBUS_DATA wrote 0x77, read back "
                    f"0x{data_readback:02X}; SMBUS_PEC wrote 0x55, read back "
                    f"0x{pec_readback:02X}. Both fields are `hw=rw` in the "
                    f"RDL with only `.next` driven (no `we` qualifier), so "
                    f"PeakRDL's hardware path (hwif_in.SMBUS_DATA.data.next="
                    f"data_byte_in, hwif_in.SMBUS_PEC.pec.next=pec_value) "
                    f"overwrites the software-written value unconditionally "
                    f"on the very next clock.")
                return False

            self.log.warning("GH58-6 unexpectedly GREEN")
            return True

        except Exception as e:
            self.log.error(f"GH58-6 test error: {e}")
            return False

    # ==================================================================
    # Item 7 (qc1): INT_STATUS never sticky / W1C ineffective
    # ==================================================================

    async def test_gh58_qc1_int_status_not_sticky(self) -> bool:
        """INT_STATUS bits must latch and clear only on SW W1C, not every cycle."""
        self.log.info("=== GH58-7 (qc1): INT_STATUS never sticky / W1C ineffective ===")
        try:
            await self._recover_and_reset()

            # --- Level-tied bit: tx_thresh_int should be sticky-clearable,
            # but is wired straight to the live tx_fifo_empty every cycle.
            await self.tb.enable_interrupts(tx_thresh=True)
            _, int_status = await self.tb.read_register(SMBusRegisterMap.SMBUS_INT_STATUS)
            tx_thresh_set = bool(int_status & (1 << 2))
            self.log.info(f"  TX FIFO empty (no data written) -> "
                           f"INT_STATUS.tx_thresh_int={tx_thresh_set}")

            # Attempt W1C
            await self.tb.write_register(SMBusRegisterMap.SMBUS_INT_STATUS, 1 << 2)
            await ClockCycles(self.tb.pclk, 2)
            _, int_status_after = await self.tb.read_register(SMBusRegisterMap.SMBUS_INT_STATUS)
            tx_thresh_after_w1c = bool(int_status_after & (1 << 2))
            self.log.info(f"  After W1C write: INT_STATUS.tx_thresh_int="
                           f"{tx_thresh_after_w1c} (should be 0 until FIFO "
                           f"state changes again)")

            level_bit_not_sticky = tx_thresh_set and tx_thresh_after_w1c

            await self._recover_and_reset()

            if level_bit_not_sticky:
                self.log.error(
                    "GH58 item 7 (qc1): SMBUS_INT_STATUS.tx_thresh_int "
                    "reasserted itself on the very next read after a W1C "
                    "write, with no new FIFO activity in between. "
                    "smbus_config_regs.sv wires "
                    "hwif_in.SMBUS_INT_STATUS.tx_thresh_int.next = "
                    "tx_fifo_empty (and rx_thresh_int.next = !rx_fifo_empty) "
                    "directly to the live FIFO flags every cycle, "
                    "unconditionally overriding the RDL's `onwrite=woclr` "
                    "W1C semantics.")
                return False

            self.log.warning("GH58-7 unexpectedly GREEN")
            return True

        except Exception as e:
            self.log.error(f"GH58-7 test error: {e}")
            return False

    # ==================================================================
    # Item 8 (qc2): smb_interrupt bypasses INT_STATUS
    # ==================================================================

    async def test_gh58_qc2_interrupt_bypasses_int_status(self) -> bool:
        """smb_interrupt must be (INT_STATUS & INT_ENABLE) != 0, registered,
        deasserting only on W1C.

        Rewrite (2026-09-09, coordinator round 2): the RTL now implements
        exactly this (apb4_smbus.sv's interrupt-aggregation block, feeding
        smbus_core's sticky int_status through INT_ENABLE and a registered/
        CDC-synchronized level, not the raw live status wires). The old
        version of this test asserted the OLD, since-fixed bypass behavior
        and had no GREEN path at all (both branches of its final decision
        returned False) - it could never pass even against correct RTL.
        Replaced with an assertion of the CONTRACT itself: error_en set ->
        an error latches INT_STATUS AND holds smb_interrupt=1 (not a pulse)
        until W1C; W1C drops both within synchronizer latency; error_en
        clear leaves the pin at 0 even though INT_STATUS.error is set;
        enabling later raises the pin with no new event needed.
        """
        self.log.info("=== GH58-8 (qc2): smb_interrupt == (INT_STATUS & INT_ENABLE) ===")
        # Generous poll bound covering the CDC path's synchronizer latency
        # (3-flop glitch_free_n_dff_arn + the final pclk registration).
        SYNC_MARGIN_CYCLES = 10

        async def _provoke_nak_error():
            """An address NAK (no slave started) - folded into
            w_int_cond_error alongside bus/timeout/PEC errors."""
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.write_data_byte(0x01)
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x01)
            # Whitebox polling (see GH58-2's note on the shared 500us
            # cocotb timeout budget): int_status[1] is the core's own
            # sticky error bit, same information read_interrupt_status()
            # would return via a much more expensive APB round trip.
            core = self._core()
            for _ in range(300):
                await RisingEdge(self.tb.pclk)
                if int(core.int_status.value) & 0x02:
                    return True
            return False

        try:
            await self._recover_and_reset()

            # --- Phase 1: error_en CLEAR - the pin must stay 0 even once
            # INT_STATUS.error latches.
            await self.tb.enable_interrupts(error=False)
            error_latched = await _provoke_nak_error()
            await ClockCycles(self.tb.pclk, SYNC_MARGIN_CYCLES)
            int_status_1 = await self.tb.read_interrupt_status()
            pin_with_en_clear = int(self.tb.dut.smb_interrupt.value)

            self.log.info(f"  Phase 1 (error_en=0): error_latched={error_latched}, "
                           f"INT_STATUS=0x{int_status_1:02X}, "
                           f"smb_interrupt={pin_with_en_clear}")

            phase1_ok = error_latched and (int_status_1 & 0x02) and pin_with_en_clear == 0

            # --- Phase 2: enable error_en with NO new event - the pin must
            # rise from the ALREADY-latched INT_STATUS.error alone.
            await self.tb.enable_interrupts(error=True)
            pin_after_enable = 0
            for _ in range(SYNC_MARGIN_CYCLES):
                await RisingEdge(self.tb.pclk)
                pin_after_enable = int(self.tb.dut.smb_interrupt.value)
                if pin_after_enable:
                    break

            self.log.info(f"  Phase 2 (error_en enabled, no new event): "
                           f"smb_interrupt={pin_after_enable} within "
                           f"{SYNC_MARGIN_CYCLES} cycles")

            # --- Phase 3: held, not a pulse - sample repeatedly.
            held_samples = []
            for _ in range(20):
                await RisingEdge(self.tb.pclk)
                held_samples.append(int(self.tb.dut.smb_interrupt.value))
            pin_held = all(s == 1 for s in held_samples)

            self.log.info(f"  Phase 3: smb_interrupt held over 20 cycles: "
                           f"{pin_held} (samples={held_samples})")

            # --- Phase 4: W1C -> INT_STATUS=0 and smb_interrupt=0 within
            # synchronizer latency.
            await self.tb.write_register(SMBusRegisterMap.SMBUS_INT_STATUS,
                                          0xFFFFFFFF)
            int_status_after_w1c = None
            pin_after_w1c = None
            for _ in range(SYNC_MARGIN_CYCLES):
                await RisingEdge(self.tb.pclk)
                int_status_after_w1c = await self.tb.read_interrupt_status()
                pin_after_w1c = int(self.tb.dut.smb_interrupt.value)
                if int_status_after_w1c == 0 and pin_after_w1c == 0:
                    break

            self.log.info(f"  Phase 4 (after W1C): INT_STATUS="
                           f"0x{int_status_after_w1c:02X}, "
                           f"smb_interrupt={pin_after_w1c}")

            await self._recover_and_reset()

            phase2_ok = pin_after_enable == 1
            phase3_ok = pin_held
            phase4_ok = (int_status_after_w1c == 0) and (pin_after_w1c == 0)

            if phase1_ok and phase2_ok and phase3_ok and phase4_ok:
                self.log.info("GH58-8 GREEN: smb_interrupt tracks "
                               "(INT_STATUS & INT_ENABLE), registered, "
                               "W1C-clearable")
                return True

            self.log.error(
                f"GH58 item 8 (qc2): contract violated - "
                f"phase1(error_en=0 keeps pin low)={phase1_ok}, "
                f"phase2(enable raises pin w/o new event)={phase2_ok}, "
                f"phase3(pin held, not pulsed)={phase3_ok}, "
                f"phase4(W1C clears both within {SYNC_MARGIN_CYCLES} cycles)="
                f"{phase4_ok}.")
            return False

        except Exception as e:
            self.log.error(f"GH58-8 test error: {e}")
            return False

    # ==================================================================
    # Item 9 (qc5 / round_3-1): byte engine never transmits past the
    # first data byte / block write hangs
    # ==================================================================

    async def test_gh58_qc5_byte_engine_bounded_completion(self) -> bool:
        """Write Byte/Word and Block Write must complete within bounded time."""
        self.log.info("=== GH58-9 (qc5/round_3-1): byte engine hang ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)  # ~20 pclk/bit
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.reset_fifos()

            await self.tb.set_block_count(1)  # correct count for Write Byte
            await self.tb.write_data_byte(0x33)

            # Bug fix (2026-09-09): pin-level `_force_permanent_ack()`
            # alone never gets the FSM past M_ADDR_ACK at all (see
            # GH58-NEW1) - use the register-level force so this test can
            # reach M_DATA_WR/M_DATA_WR_ACK, the states it is actually
            # about.
            ack_task = self._force_permanent_ack_task()
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x50)

            core = self._core()
            observed_states = set()

            async def _watch_states():
                while True:
                    await RisingEdge(self.tb.pclk)
                    observed_states.add(int(core.r_master_state.value))

            watcher = cocotb.start_soon(_watch_states())

            # wait_for_complete's own loop bound is in APB-read iterations,
            # not raw pclk cycles (each iteration is a full APB read), so
            # this comfortably covers address(9)+cmd(9)+data(9) bits worth
            # of real pclk time; sample byte_counter alongside completion
            # for direct mechanism evidence.
            bound_cycles = 800
            completed = await self.tb.wait_for_complete(timeout_cycles=bound_cycles)
            byte_counter_stuck = int(core.r_byte_counter.value)
            watcher.kill()

            ack_task.kill()
            self.tb.dut.smb_sda_i.value = 1
            await self._recover_and_reset()

            reached_data_wr = M_DATA_WR in observed_states or M_DATA_WR_ACK in observed_states
            self.log.info(f"  Write Byte completed within {bound_cycles} "
                           f"cycles: {completed}; r_byte_counter sampled at "
                           f"end = {byte_counter_stuck}; r_master_state "
                           f"visited {sorted(hex(v) for v in observed_states)} "
                           f"(reached M_DATA_WR/M_DATA_WR_ACK: {reached_data_wr})")

            if not reached_data_wr:
                self.log.error(
                    "GH58-9 test infrastructure: the register-level ACK "
                    "force did not get the FSM into M_DATA_WR/M_DATA_WR_ACK "
                    f"at all (states visited: "
                    f"{sorted(hex(v) for v in observed_states)}) - cannot "
                    "judge the byte-engine-hang mechanism this run. "
                    "Treating as RED pending investigation.")
                return False

            if not completed:
                self.log.error(
                    f"GH58 item 9 (qc5/round_3-1): Write Byte (1 data byte, "
                    f"BLOCK_COUNT correctly set to 1, r_ack_bit forced to 0 "
                    f"every cycle) reached M_DATA_WR/M_DATA_WR_ACK but did "
                    f"not reach status_complete within {bound_cycles} pclk "
                    f"cycles (r_byte_counter sampled at {byte_counter_stuck}, "
                    f"never advanced past 0). smbus_core.sv's byte-counter "
                    f"increment and next-byte reload are gated on the "
                    f"unreachable M_DATA_WR->M_DATA_WR self-transition (see "
                    f"item 4), so M_DATA_WR_ACK's `byte_counter >= "
                    f"bytes_total` exit test is only ever satisfied when "
                    f"bytes_total==0 - any transaction needing >=1 data byte "
                    f"oscillates M_DATA_WR <-> M_DATA_WR_ACK forever.")
                return False

            self.log.warning("GH58-9 unexpectedly GREEN")
            return True

        except Exception as e:
            self.log.error(f"GH58-9 test error: {e}")
            return False

    # ==================================================================
    # Item 10 (qc6): r_bytes_total loaded from block_count for all types
    # ==================================================================

    async def test_gh58_qc6_bytes_total_from_block_count_always(self) -> bool:
        """Write Byte must always target 1 data byte, regardless of BLOCK_COUNT."""
        self.log.info("=== GH58-10 (qc6): r_bytes_total always from block_count ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.reset_fifos()

            # Deliberately leave BLOCK_COUNT wrong for a Write Byte
            # transaction (a Block Write from an earlier step, say).
            await self.tb.set_block_count(5)
            await self.tb.write_tx_fifo([0xDE, 0xAD, 0xBE, 0xEF, 0x01])
            await self.tb.write_data_byte(0x77)

            self._force_permanent_ack()
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x60)

            core = self._core()
            await ClockCycles(self.tb.pclk, 5)  # r_bytes_total latches at cmd_start
            bytes_total = int(core.r_bytes_total.value)

            self.tb.dut.smb_sda_i.value = 1
            await self._recover_and_reset()

            self.log.info(f"  SMBUS_BLOCK_COUNT=5 left set, Write Byte issued -> "
                           f"r_bytes_total latched = {bytes_total} (must be 1)")

            if bytes_total != 1:
                self.log.error(
                    f"GH58 item 10 (qc6): Write Byte must always send "
                    f"exactly 1 data byte; r_bytes_total was latched as "
                    f"{bytes_total} because smbus_core.sv's "
                    f"'Latch transaction parameters on START' block does "
                    f"`r_bytes_total <= cmd_block_count` unconditionally, "
                    f"with no case on cmd_trans_type - it inherited the "
                    f"stale SMBUS_BLOCK_COUNT=5 left over from a prior "
                    f"block transfer instead of using 1.")
                return False

            self.log.warning("GH58-10 unexpectedly GREEN")
            return True

        except Exception as e:
            self.log.error(f"GH58-10 test error: {e}")
            return False

    # ==================================================================
    # NOTE: while debugging GH58-4/9's initial false-GREEN results, a
    # register-level ACK force (`_force_permanent_ack_task`, above) was
    # found necessary because the pin-level `_force_permanent_ack`
    # override alone left the FSM stuck at M_ADDR/M_ADDR_ACK/M_ERROR in
    # one specific setup (Block Write, longer register-write preamble).
    # A hypothesis that master_state_next's *_ACK case arms read a
    # stale r_ack_bit on entry (before the PHY_BIT_RX sample completes)
    # was investigated with a dedicated whitebox test, but a second,
    # more carefully-instrumented run (Write Byte, shorter preamble,
    # watcher started before any config calls) showed the SAME pin-only
    # force reaching M_DATA_WR/M_DATA_WR_ACK just fine - contradicting
    # the hypothesis. Rather than report an unconfirmed root cause, this
    # is left here as an open question for whoever next instruments
    # smbus_core.sv's master FSM: pin-level ACK forcing is unreliable
    # across at least these two setups for a reason not yet pinned
    # down (config/timing preamble length? clk_div phase alignment at
    # cmd_start? something else?) - items #4/#9 sidestep the question
    # entirely by forcing r_ack_bit itself, which works unambiguously.
    # ==================================================================


    # ==================================================================
    # Item 11: strict decode across the 4KB APB window
    # ==================================================================

    async def test_gh58_strict_decode(self) -> bool:
        """Every unmapped address must read 0 + PSLVERR; writes must be ignored."""
        self.log.info("=== GH58-11: strict decode of unmapped addresses ===")
        try:
            await self._recover_and_reset()

            # SMBUS_SLAVE_STATUS @ 0x040 is the last mapped register;
            # 0x044-0xFFC (4KB APB window, 12-bit paddr) must all be
            # unmapped per rdl/smbus/smbus_regs.rdl's own address-layout
            # comment. 0x03C and 0x040 were in this list until slave mode
            # gave them to SMBUS_SLAVE_CTRL and SMBUS_SLAVE_STATUS
            # (RLB-011); 0x044 and 0x080 take their place, and 0x080 is the
            # first alias of SMBUS_CONTROL now that the generated block
            # decodes seven address bits rather than six.
            unmapped_addrs = [0x044, 0x080, 0x100, 0x200, 0x800, 0xFFC]

            failures = []
            for addr in unmapped_addrs:
                read_packet, read_data = await self.tb.read_register(addr)
                pslverr = read_packet.fields.get('pslverr', None)

                if read_data != 0:
                    failures.append(
                        f"0x{addr:03X}: read returned 0x{read_data:08X}, "
                        f"expected 0")

                if not pslverr:
                    failures.append(
                        f"0x{addr:03X}: read PSLVERR={pslverr}, expected 1 "
                        f"(unmapped address in the 4KB APB window)")

                # Confirm writes are ignored: write a sentinel, read back,
                # must still be 0 / PSLVERR (not silently accepted/aliased).
                await self.tb.write_register(addr, 0xDEADBEEF)
                await ClockCycles(self.tb.pclk, 3)
                _, readback_after_write = await self.tb.read_register(addr)
                if readback_after_write != 0:
                    failures.append(
                        f"0x{addr:03X}: write of 0xDEADBEEF was NOT ignored "
                        f"- readback = 0x{readback_after_write:08X}")

            self.log.info(f"  Unmapped-address probe results: "
                           f"{len(failures)} failing address(es) of "
                           f"{len(unmapped_addrs)} probed")
            for f in failures:
                self.log.info(f"    {f}")

            if failures:
                self.log.error(
                    "GH58 item 11: strict decode failed for "
                    f"{len(failures)}/{len(unmapped_addrs)} unmapped "
                    f"addresses in the 4KB APB window - "
                    + "; ".join(failures))
                return False

            self.log.warning("GH58-11 unexpectedly GREEN")
            return True

        except Exception as e:
            self.log.error(f"GH58-11 test error: {e}")
            return False

    # ==================================================================
    # Item 13 (new, coordinator round 2): acceptance test for
    # SMBUS_CONTROL.soft_reset - expected GREEN, the RTL agent wired
    # this deliberately (smbus_core.sv: "SOFT RESET IS THE SAME RESET,
    # SYNCHRONOUSLY"; smbus_bit_phy.sv releases both lines on it;
    # smbus_byte_fifos.sv clears both FIFOs on it).
    # ==================================================================

    async def test_gh58_13_soft_reset_mid_transfer(self) -> bool:
        """soft_reset mid-transfer aborts cleanly and the engine recovers."""
        self.log.info("=== GH58-13: soft_reset aborts a mid-transfer block write ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.reset_fifos()

            _, control_before = await self.tb.read_register(
                SMBusRegisterMap.SMBUS_CONTROL)
            self.log.info(f"  CONTROL before soft_reset: 0x{control_before:08X}")

            # A block write long enough (8 bytes) that soft_reset lands
            # genuinely mid-transfer, not after natural completion.
            block_data = [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88]
            await self.tb.set_block_count(len(block_data))
            await self.tb.write_tx_fifo(block_data)

            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()

            await self.tb.start_transaction(SMBusRegisterMap.TRANS_BLOCK_WRITE,
                                             0x50, command=0x70)

            # Confirm busy, then let a few bytes go out before the abort.
            busy_confirmed = False
            for _ in range(20):
                await RisingEdge(self.tb.pclk)
                if (await self.tb.read_status())['busy']:
                    busy_confirmed = True
                    break
            await ClockCycles(self.tb.pclk, 200)  # comfortably mid-transfer

            status_mid = await self.tb.read_status()
            self.log.info(f"  Mid-transfer status: busy_confirmed="
                           f"{busy_confirmed}, status={status_mid}")

            # Assert soft_reset, preserving the other CONTROL bits.
            await self.tb.write_register(
                SMBusRegisterMap.SMBUS_CONTROL,
                control_before | SMBusRegisterMap.CONTROL_SOFT_RESET)

            await ClockCycles(self.tb.pclk, 10)

            status_after = await self.tb.read_status()
            fifo_after = await self.tb.read_fifo_status()
            _, control_after = await self.tb.read_register(
                SMBusRegisterMap.SMBUS_CONTROL)
            lines_released = (int(self.tb.dut.smb_scl_t.value) == 1 and
                               int(self.tb.dut.smb_sda_t.value) == 1)

            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()

            self.log.info(f"  After soft_reset: status={status_after}, "
                           f"fifo={fifo_after}, "
                           f"CONTROL=0x{control_after:08X}, "
                           f"lines_released={lines_released}")

            busy_dropped = not status_after['busy']
            fifos_empty = (fifo_after['tx_level'] == 0 and
                           fifo_after['rx_level'] == 0)
            soft_reset_bit_clear = (control_after & SMBusRegisterMap.CONTROL_SOFT_RESET) == 0
            # Other CONTROL bits (e.g. master_en) must be unchanged - only
            # the self-clearing soft_reset bit differs from control_before.
            other_bits_unchanged = ((control_after & ~SMBusRegisterMap.CONTROL_SOFT_RESET) ==
                                     (control_before & ~SMBusRegisterMap.CONTROL_SOFT_RESET))
            status_cleared = not (status_after['bus_error'] or
                                   status_after['timeout_error'] or
                                   status_after['pec_error'] or
                                   status_after['nak_received'] or
                                   status_after['complete'])

            recovery_ok = (busy_dropped and lines_released and fifos_empty and
                           soft_reset_bit_clear and other_bits_unchanged and
                           status_cleared)

            if not recovery_ok:
                self.log.error(
                    f"GH58-13: soft_reset mid-transfer did not recover "
                    f"cleanly - busy_dropped={busy_dropped}, "
                    f"lines_released={lines_released}, "
                    f"fifos_empty={fifos_empty} ({fifo_after}), "
                    f"soft_reset_bit_clear={soft_reset_bit_clear}, "
                    f"other_bits_unchanged={other_bits_unchanged} "
                    f"(before=0x{control_before:08X}, "
                    f"after=0x{control_after:08X}), "
                    f"status_cleared={status_cleared} ({status_after}).")
                await self._recover_and_reset()
                return False

            # M2 (coordinator round 3, folded in): soft_reset must clear the
            # STICKY INT_STATUS too, not just the live status/FIFOs/lines
            # above - a NAK's error_int latches independently in
            # smbus_int_status.sv and must not survive a soft_reset.
            await self.tb.enable_interrupts(error=True)
            core = self._core()
            error_latched = False
            await self.tb.write_data_byte(0x01)
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x01)  # no slave -> NAK
            for _ in range(300):
                await RisingEdge(self.tb.pclk)
                if int(core.int_status.value) & 0x02:
                    error_latched = True
                    break

            await self.tb.write_register(
                SMBusRegisterMap.SMBUS_CONTROL,
                SMBusRegisterMap.CONTROL_MASTER_EN | SMBusRegisterMap.CONTROL_SOFT_RESET)
            await ClockCycles(self.tb.pclk, 10)

            int_status_after_soft_reset = await self.tb.read_interrupt_status()
            interrupt_after_soft_reset = int(self.tb.dut.smb_interrupt.value)

            self.log.info(f"  M2: error_latched={error_latched}, after "
                           f"soft_reset INT_STATUS="
                           f"0x{int_status_after_soft_reset:02X}, "
                           f"smb_interrupt={interrupt_after_soft_reset}")

            m2_ok = (error_latched and int_status_after_soft_reset == 0 and
                     interrupt_after_soft_reset == 0)
            if not m2_ok:
                self.log.error(
                    f"GH58-13 (+M2): soft_reset must clear the sticky "
                    f"SMBUS_INT_STATUS, not just live status/FIFOs/lines - "
                    f"error_latched={error_latched}, INT_STATUS after "
                    f"soft_reset=0x{int_status_after_soft_reset:02X} "
                    f"(expected 0), smb_interrupt="
                    f"{interrupt_after_soft_reset} (expected 0). "
                    f"smbus_core.sv instantiates u_int_status with "
                    f"`.rst(rst)` only, not `.rst(rst || cfg_soft_reset)`, "
                    f"so the sticky bits in smbus_int_status.sv survive a "
                    f"soft_reset even though the LIVE condition that set "
                    f"them (r_nak_received etc.) is cleared by it.")
                await self._recover_and_reset()
                return False

            # A subsequent transaction must work normally.
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()
            await self.tb.write_data_byte(0x99)
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x71)

            # Whitebox polling (see GH58-2's note): a per-cycle APB read
            # here blows the suite's shared 500us cocotb timeout budget.
            core = self._core()
            post_reset_completed = False
            for _ in range(2000):
                await RisingEdge(self.tb.pclk)
                if int(core.status_complete.value):
                    post_reset_completed = True
                    break
                if (int(core.status_bus_error.value) or
                        int(core.status_timeout_error.value) or
                        int(core.status_pec_error.value)):
                    break

            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            await self._recover_and_reset()

            self.log.info(f"  Post-reset transaction completed: "
                           f"{post_reset_completed}")

            if post_reset_completed:
                self.log.info("GH58-13 GREEN: soft_reset recovers cleanly "
                               "mid-transfer and a subsequent transaction works")
                return True

            self.log.error("GH58-13: engine recovered from soft_reset but a "
                            "subsequent transaction did not complete")
            return False

        except Exception as e:
            self.log.error(f"GH58-13 test error: {e}")
            return False

    # ==================================================================
    # Item 14 (coordinator round 2, then folded M1 per round 3): fast_mode
    # timing must meet the SMBus fast-mode spec MINIMUMS on the wire, not
    # just an internal 4:1 divider ratio. Coordinator-confirmed current
    # values at the RDL default CLK_DIV=249: tLOW=1.26us, tBUF=0.63us -
    # both under their 1.3us minimums.
    # ==================================================================

    async def test_gh58_14_fast_mode_scl_ratio(self) -> bool:
        """fast_mode must meet the SMBus fast-mode spec minimums on the wire:
        tLOW>=1.3us, tHIGH>=0.6us, tBUF>=1.3us, tHD;STA>=0.6us."""
        self.log.info("=== GH58-14 (+M1): fast_mode SMBus spec-minimum timing ===")
        # RDL default CLK_DIV (100kHz standard / ~400kHz fast at 100MHz
        # core clock) - the realistic operating point the spec minimums
        # apply to, not an artificially chosen divider.
        CLK_DIV = 249
        T_LOW_MIN_NS = 1300
        T_HIGH_MIN_NS = 600
        T_BUF_MIN_NS = 1300
        T_HD_STA_MIN_NS = 600

        async def _measure_low_high_ns():
            # Let a few bits go by first so this isn't measuring START's
            # own atypical edge, then take one clean high phase followed
            # by one clean low phase from steady-state bit clocking.
            for _ in range(3):
                await RisingEdge(self.tb.dut.smb_scl_o)
            t_rise = cocotb.utils.get_sim_time('ns')
            await FallingEdge(self.tb.dut.smb_scl_o)
            t_fall = cocotb.utils.get_sim_time('ns')
            high_ns = t_fall - t_rise
            await RisingEdge(self.tb.dut.smb_scl_o)
            t_rise2 = cocotb.utils.get_sim_time('ns')
            low_ns = t_rise2 - t_fall
            return low_ns, high_ns

        async def _measure_start_hold_ns():
            # START: SDA falls while SCL still high (tHD;STA), then SCL
            # itself falls once the hold completes.
            await FallingEdge(self.tb.dut.smb_sda_o)
            t_sda_fall = cocotb.utils.get_sim_time('ns')
            await FallingEdge(self.tb.dut.smb_scl_o)
            t_scl_fall = cocotb.utils.get_sim_time('ns')
            return t_scl_fall - t_sda_fall

        async def _measure_stop_hold_ns():
            # tBUF proxy: STOP's own "release SCL, hold" phase (P1) - SCL
            # rises, then SDA rises (the STOP marker itself, P1->P2).
            core = self._core()
            for _ in range(400):
                await RisingEdge(self.tb.pclk)
                if int(core.status_fsm_state.value) == M_STOP:
                    break
            await RisingEdge(self.tb.dut.smb_scl_o)
            t_scl_rise = cocotb.utils.get_sim_time('ns')
            await RisingEdge(self.tb.dut.smb_sda_o)
            t_sda_rise = cocotb.utils.get_sim_time('ns')
            return t_sda_rise - t_scl_rise

        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True, fast_mode=True)
            await self.tb.configure_clock(clk_div=CLK_DIV)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.write_data_byte(0x5A)
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x01)
            t_low_ns, t_high_ns = await _measure_low_high_ns()
            await self._recover_and_reset()

            await self.tb.enable_master_mode(enable=True, fast_mode=True)
            await self.tb.configure_clock(clk_div=CLK_DIV)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.write_data_byte(0x5A)
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x01)
            t_hd_sta_ns = await _measure_start_hold_ns()
            await self._recover_and_reset()

            await self.tb.enable_master_mode(enable=True, fast_mode=True)
            await self.tb.configure_clock(clk_div=CLK_DIV)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_QUICK_CMD, 0x50)
            t_buf_ns = await _measure_stop_hold_ns()
            await self._recover_and_reset()

            self.log.info(f"  fast_mode @ CLK_DIV={CLK_DIV}: tLOW={t_low_ns}ns "
                           f"(min {T_LOW_MIN_NS}), tHIGH={t_high_ns}ns "
                           f"(min {T_HIGH_MIN_NS}), tHD;STA={t_hd_sta_ns}ns "
                           f"(min {T_HD_STA_MIN_NS}), tBUF={t_buf_ns}ns "
                           f"(min {T_BUF_MIN_NS})")

            low_ok = t_low_ns >= T_LOW_MIN_NS
            high_ok = t_high_ns >= T_HIGH_MIN_NS
            hd_sta_ok = t_hd_sta_ns >= T_HD_STA_MIN_NS
            buf_ok = t_buf_ns >= T_BUF_MIN_NS

            if low_ok and high_ok and hd_sta_ok and buf_ok:
                self.log.info("GH58-14 GREEN: fast_mode meets all four "
                               "SMBus spec timing minimums on the wire")
                return True

            self.log.error(
                f"GH58-14 (+M1): fast_mode timing set does not meet the "
                f"SMBus fast-mode spec minimums at CLK_DIV={CLK_DIV} - "
                f"tLOW={t_low_ns}ns (need >={T_LOW_MIN_NS}, ok={low_ok}), "
                f"tHIGH={t_high_ns}ns (need >={T_HIGH_MIN_NS}, ok={high_ok}), "
                f"tHD;STA={t_hd_sta_ns}ns (need >={T_HD_STA_MIN_NS}, "
                f"ok={hd_sta_ok}), tBUF={t_buf_ns}ns (need >={T_BUF_MIN_NS}, "
                f"ok={buf_ok}). smbus_bit_phy.sv's w_hold_quarters=1 in "
                f"fast mode (vs 2 in standard) applies uniformly to every "
                f"setup/hold phase (TX/RX release-and-wait, START/RESTART/"
                f"STOP hold) - one quarter at CLK_DIV=249's fast quarter "
                f"(~630ns) undershoots the 1.3us tLOW/tBUF minimums even "
                f"though it clears the looser 0.6us tHIGH/tHD;STA minimums.")
            return False

        except Exception as e:
            self.log.error(f"GH58-14 test error: {e}")
            return False

    # ==================================================================
    # GH58-R2 batch (coordinator round 3): reviewer-found RED tests
    # against the CURRENT RTL. Same file, no sweep build. Uses
    # SMBusMonitor for wire-level byte sequences and SMBusSlave.memory
    # for delivered data, per the coordinator's instruction.
    # ==================================================================

    async def _run_write_and_capture(self, trans_type, slave_addr, command,
                                      wait_cycles=3000):
        """Start a transaction against the real slave/monitor BFMs and
        return the packet THIS call's own transaction produced (or None).

        Bug fix (GH#58 round-3): recv_queue[-1] blindly returned whatever
        the LAST monitor session (possibly a different, earlier test)
        happened to leave behind - the queue is never cleared between
        .start()/.stop() cycles, and two tests could read the exact same
        stale packet object. This clears the queue immediately before
        starting THIS transaction, so anything in it afterward is
        unambiguously this call's own. Also runs the monitor self-check
        the coordinator asked for: a STOP-terminated transaction must
        leave exactly one new packet in the queue.
        """
        self.tb.smbus_slave.clock_stretch_cycles = 0
        self.tb.smbus_slave.start()
        self.tb.smbus_monitor.start()
        self.tb.smbus_monitor.recv_queue.clear()
        await self.tb.start_transaction(trans_type, slave_addr,
                                         command=command if command is not None else 0)
        core = self._core()
        for _ in range(wait_cycles):
            await RisingEdge(self.tb.pclk)
            if int(core.status_complete.value) or int(core.status_bus_error.value):
                break
        await ClockCycles(self.tb.pclk, 20)
        new_packets = list(self.tb.smbus_monitor.recv_queue)
        packet = new_packets[-1] if new_packets else None
        self.tb.smbus_slave.stop()
        self.tb.smbus_monitor.stop()

        # Monitor self-check (coordinator round-3 ask): a STOP-terminated
        # transaction must produce exactly one new packet.
        if packet is not None and packet.completed and len(new_packets) != 1:
            self.log.warning(
                f"Monitor self-check: expected exactly 1 new packet for a "
                f"STOP-terminated transaction, got {len(new_packets)}: "
                f"{[p.formatted() for p in new_packets]}")
        return packet

    async def test_gh58_r2_h1_write_word_fifo(self) -> bool:
        """Write Word must send FIFO[0],FIFO[1] in order and pop both.

        Mechanism: smbus_core.sv's w_tx_fifo_rd requires r_count_sent,
        which is ONLY ever set for block writes (w_sends_count). Write
        Word never sets it, so the FIFO is never popped - both data-byte
        loads (`r_tx_byte <= w_tx_from_fifo ? w_tx_fifo_rdata : ...`) peek
        the SAME head-of-queue byte, sending it twice and leaving the
        FIFO at level 2 instead of 0.
        """
        self.log.info("=== GH58-R2-H1: Write Word repeats byte 0, never pops TX FIFO ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.reset_fifos()
            await self.tb.write_tx_fifo([0xAA, 0xBB])

            packet = await self._run_write_and_capture(
                SMBusRegisterMap.TRANS_WRITE_WORD, 0x50, 0x10)
            fifo_after = await self.tb.read_fifo_status()
            await self._recover_and_reset()

            wire_data = packet.data if packet else None
            self.log.info(f"  wire data={wire_data}, tx_level after="
                           f"{fifo_after['tx_level']}")

            if wire_data == [0xAA, 0xBB] and fifo_after['tx_level'] == 0:
                self.log.warning("GH58-R2-H1 unexpectedly GREEN")
                return True

            self.log.error(
                f"GH58-R2-H1: Write Word expected wire data [0xAA, 0xBB] and "
                f"tx_level=0 after; got wire data={wire_data}, "
                f"tx_level={fifo_after['tx_level']}. w_tx_fifo_rd requires "
                f"r_count_sent, which Write Word never sets (only block "
                f"writes do), so the FIFO is never popped and both data "
                f"bytes are loaded from the same unmoved head-of-queue byte.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R2-H1 test error: {e}")
            return False

    async def test_gh58_r2_h2_block_write_fifo(self) -> bool:
        """Block Write must send count,B1,B2,B3 and empty the FIFO.

        Mechanism: the count byte's ACK sets r_count_sent<=1 (visible
        next cycle) and peeks (not pops) B1 from the FIFO in the SAME
        cycle - so w_tx_fifo_rd's `r_count_sent` gate is still reading
        the OLD value (0) and does not pop for B1. On B1's own ACK,
        r_count_sent now reads 1, so w_tx_fifo_rd pops - but the byte
        LOADED that same cycle is still the pre-pop rdata (B1 again);
        the pop only becomes visible the cycle after. This one-cycle
        skew means each loaded byte is one pop behind the FIFO pointer:
        B1 is sent twice, and B3 - never reached - is left in the FIFO.
        """
        self.log.info("=== GH58-R2-H2: Block Write repeats B1, drops B3 ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.reset_fifos()
            block_data = [0x11, 0x22, 0x33]
            await self.tb.set_block_count(len(block_data))
            await self.tb.write_tx_fifo(block_data)

            packet = await self._run_write_and_capture(
                SMBusRegisterMap.TRANS_BLOCK_WRITE, 0x50, 0x20)
            fifo_after = await self.tb.read_fifo_status()
            await self._recover_and_reset()

            wire_count = packet.byte_count if packet else None
            wire_data = packet.data if packet else None
            self.log.info(f"  wire count={wire_count}, wire data={wire_data}, "
                           f"tx_level after={fifo_after['tx_level']}")

            if (wire_count == 3 and wire_data == block_data and
                    fifo_after['tx_level'] == 0):
                self.log.warning("GH58-R2-H2 unexpectedly GREEN")
                return True

            self.log.error(
                f"GH58-R2-H2: Block Write expected wire count=3, "
                f"data={block_data}, tx_level=0 after; got count="
                f"{wire_count}, data={wire_data}, "
                f"tx_level={fifo_after['tx_level']}. The count byte's ACK "
                f"sets r_count_sent visible only NEXT cycle while peeking "
                f"(not popping) B1 in the SAME cycle; B1's own ACK then "
                f"pops while still loading the pre-pop (B1) value - every "
                f"loaded byte is one pop behind the FIFO pointer.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R2-H2 test error: {e}")
            return False

    async def test_gh58_r2_h3a_stop_alone_mid_transfer(self) -> bool:
        """SMBUS_COMMAND.stop written ALONE mid-transfer must abort onto
        a real STOP on the wire, release both lines, busy=0, and a later
        start must work.

        Mechanism (same class as GH58-2 sub-A / coordinator H3): the
        abort path (`w_abort_req`) issues a single-cycle r_phy_req for
        PHY_OP_STOP, but smbus_bit_phy only samples op_req while
        `!r_active`. With normal (non-stretched) bit timing the PHY is
        active for most of each bit period, so the abort request lands
        mid-primitive far more often than not and is silently dropped.
        """
        self.log.info("=== GH58-R2-H3a: SMBUS_COMMAND.stop alone mid-transfer ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.reset_fifos()
            block_data = [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88]
            await self.tb.set_block_count(len(block_data))
            await self.tb.write_tx_fifo(block_data)

            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()

            await self.tb.start_transaction(SMBusRegisterMap.TRANS_BLOCK_WRITE,
                                             0x50, command=0x40)
            core = self._core()
            for _ in range(20):
                await RisingEdge(self.tb.pclk)
                if int(core.status_busy.value):
                    break

            # Abort with COMMAND.stop alone (no start bit) while busy.
            await self.tb.write_register(SMBusRegisterMap.SMBUS_COMMAND,
                                          SMBusRegisterMap.COMMAND_STOP)

            busy_dropped = False
            for _ in range(3000):
                await RisingEdge(self.tb.pclk)
                if not int(core.status_busy.value):
                    busy_dropped = True
                    break

            lines_released = (int(self.tb.dut.smb_scl_t.value) == 1 and
                               int(self.tb.dut.smb_sda_t.value) == 1)

            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()

            self.log.info(f"  busy_dropped={busy_dropped}, "
                           f"lines_released={lines_released}")

            if not (busy_dropped and lines_released):
                self.log.error(
                    f"GH58-R2-H3a: SMBUS_COMMAND.stop alone mid-transfer - "
                    f"busy_dropped={busy_dropped}, "
                    f"lines_released={lines_released}. The abort's single-"
                    f"cycle PHY_OP_STOP request was likely dropped while "
                    f"the PHY was still active mid-bit (smbus_bit_phy only "
                    f"samples op_req while !r_active).")
                await self._recover_and_reset()
                return False

            # A later transaction must work.
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()
            await self.tb.write_data_byte(0x77)
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x41)
            later_completed = False
            for _ in range(3000):
                await RisingEdge(self.tb.pclk)
                if int(core.status_complete.value):
                    later_completed = True
                    break
                if int(core.status_timeout_error.value):
                    break
            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            await self._recover_and_reset()

            self.log.info(f"  later_completed={later_completed}")
            if later_completed:
                self.log.warning("GH58-R2-H3a unexpectedly GREEN")
                return True

            self.log.error("GH58-R2-H3a: recovered from the abort but a "
                            "later transaction did not complete (likely "
                            "wedged into an immediate timeout - dropped "
                            "STOP left the PHY thinking SCL is still low).")
            return False
        except Exception as e:
            self.log.error(f"GH58-R2-H3a test error: {e}")
            return False

    async def test_gh58_r2_h4_stretch_through_stop_hangs(self) -> bool:
        """A slave stretching only the FINAL STOP past SMBUS_TIMEOUT must
        still time out, release the bus and clear busy.

        Mechanism: the global timeout check explicitly excludes
        M_STOP (`(r_master_state != M_STOP) && w_phy_timeout`), and
        M_STOP's own arm only advances on `w_phy_done` - so a STOP that
        never completes (slave holding SCL through it) leaves the master
        wedged in M_STOP forever, busy stuck at 1, even though
        w_phy_timeout is already asserted underneath it.
        """
        self.log.info("=== GH58-R2-H4: slave stretches only the final STOP ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=500)  # 5us
            await self.tb.write_data_byte(0x5A)

            # No stretch on the data-phase ACKs; only on the LAST one
            # (attached to the byte immediately preceding STOP is not
            # separable in this BFM, so stretch throughout and rely on
            # the timeout being too short to fire before STOP begins is
            # NOT reliable - instead: keep the data phase unstretched by
            # using Quick Command (address ACK only, then STOP), and
            # additionally hold the slave's SCL release back further by
            # stretching that single ACK long enough to span into STOP.
            self.tb.smbus_slave.clock_stretch_cycles = 3000  # 30us > 5us timeout
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()

            await self.tb.start_transaction(SMBusRegisterMap.TRANS_QUICK_CMD, 0x50)

            core = self._core()
            reached_stop = False
            for _ in range(2000):
                await RisingEdge(self.tb.pclk)
                if int(core.status_fsm_state.value) == M_STOP:
                    reached_stop = True
                    break

            timeout_and_recovered = False
            for _ in range(6000):  # 60us
                await RisingEdge(self.tb.pclk)
                if (int(core.status_timeout_error.value) and
                        not int(core.status_busy.value)):
                    timeout_and_recovered = True
                    break

            status_final = await self.tb.read_status()
            lines_released = (int(self.tb.dut.smb_scl_t.value) == 1 and
                               int(self.tb.dut.smb_sda_t.value) == 1)

            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            await self._recover_and_reset()

            self.log.info(f"  reached_stop_state={reached_stop}, "
                           f"timeout_and_recovered={timeout_and_recovered}, "
                           f"status={status_final}, "
                           f"lines_released={lines_released}")

            if timeout_and_recovered and lines_released:
                self.log.warning("GH58-R2-H4 unexpectedly GREEN")
                return True

            self.log.error(
                f"GH58-R2-H4: a slave stretch spanning the final STOP "
                f"(30us) against SMBUS_TIMEOUT=500 clocks (5us) must still "
                f"time out and release the bus. Got reached_stop_state="
                f"{reached_stop}, timeout_and_recovered="
                f"{timeout_and_recovered}, status={status_final}, "
                f"lines_released={lines_released}. smbus_core.sv's global "
                f"timeout check excludes M_STOP "
                f"(`(state != M_STOP) && w_phy_timeout`), and M_STOP's own "
                f"arm only advances on w_phy_done - busy is stuck forever "
                f"if STOP itself never completes.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R2-H4 test error: {e}")
            return False

    async def test_gh58_r2_h5_block_read(self) -> bool:
        """Block Read: RX FIFO must hold exactly the slave's D1..Dcount,
        ACKing all but the last data byte (which is NAKed)."""
        self.log.info("=== GH58-R2-H5: Block Read byte accounting ===")
        try:
            # --- count = 4
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.reset_fifos()

            cmd = 0x50
            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.write_memory(cmd, [4, 0xD1, 0xD2, 0xD3, 0xD4])
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()

            await self.tb.start_transaction(SMBusRegisterMap.TRANS_BLOCK_READ,
                                             0x50, command=cmd)
            core = self._core()
            for _ in range(3000):
                await RisingEdge(self.tb.pclk)
                if int(core.status_complete.value) or int(core.status_bus_error.value):
                    break
            await ClockCycles(self.tb.pclk, 20)
            fifo_status = await self.tb.read_fifo_status()
            rx_bytes = await self.tb.read_rx_fifo(fifo_status['rx_level'])
            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            await self._recover_and_reset()

            self.log.info(f"  count=4 case: rx_level={fifo_status['rx_level']}, "
                           f"rx_bytes={[hex(b) for b in rx_bytes]}")
            count4_ok = rx_bytes == [0xD1, 0xD2, 0xD3, 0xD4]

            # --- count = 1
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.reset_fifos()

            self.tb.smbus_slave.write_memory(cmd, [1, 0xE1])
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()

            await self.tb.start_transaction(SMBusRegisterMap.TRANS_BLOCK_READ,
                                             0x50, command=cmd)
            for _ in range(3000):
                await RisingEdge(self.tb.pclk)
                if int(core.status_complete.value) or int(core.status_bus_error.value):
                    break
            await ClockCycles(self.tb.pclk, 20)
            fifo_status_1 = await self.tb.read_fifo_status()
            rx_bytes_1 = await self.tb.read_rx_fifo(fifo_status_1['rx_level'])
            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            await self._recover_and_reset()

            self.log.info(f"  count=1 case: rx_level={fifo_status_1['rx_level']}, "
                           f"rx_bytes={[hex(b) for b in rx_bytes_1]}")
            count1_ok = rx_bytes_1 == [0xE1]

            if count4_ok and count1_ok:
                self.log.warning("GH58-R2-H5 unexpectedly GREEN")
                return True

            self.log.error(
                f"GH58-R2-H5: Block Read byte accounting wrong - "
                f"count=4 case got {[hex(b) for b in rx_bytes]} "
                f"(expected [0xd1,0xd2,0xd3,0xd4], ok={count4_ok}); "
                f"count=1 case got {[hex(b) for b in rx_bytes_1]} "
                f"(expected [0xe1], ok={count1_ok}).")
            return False
        except Exception as e:
            self.log.error(f"GH58-R2-H5 test error: {e}")
            return False

    async def test_gh58_r2_h6_block_process_call(self) -> bool:
        """Block Process Call must write count+data BEFORE the repeated
        START, not jump straight to it.

        Mechanism: M_CMD_ACK checks `w_needs_restart` before checking
        `w_sends_count`, and TRANS_BLOCK_PROC sets BOTH - so it takes the
        same immediate-restart path as a pure read, skipping the write-
        side count/data phase entirely.
        """
        self.log.info("=== GH58-R2-H6: Block Process Call skips its write half ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.reset_fifos()

            cmd = 0x60
            block_data = [0xA1, 0xA2]
            await self.tb.set_block_count(len(block_data))
            await self.tb.write_tx_fifo(block_data)
            self.tb.smbus_slave.write_memory(cmd, [2, 0xB1, 0xB2])

            packet = await self._run_write_and_capture(
                SMBusRegisterMap.TRANS_BLOCK_PROC, 0x50, cmd)
            await self._recover_and_reset()

            wrote_before_restart = bool(packet and packet.data)
            self.log.info(f"  packet={packet.formatted() if packet else None}, "
                           f"wrote_before_restart={wrote_before_restart}")

            if wrote_before_restart:
                self.log.warning("GH58-R2-H6 unexpectedly GREEN")
                return True

            self.log.error(
                f"GH58-R2-H6: Block Process Call must send "
                f"S,Addr+W,Cmd,count,data...,Sr,Addr+R,... - got packet="
                f"{packet.formatted() if packet else None}, no write-side "
                f"count/data observed. M_CMD_ACK checks w_needs_restart "
                f"before w_sends_count, and BLOCK_PROC sets both, so it "
                f"takes the pure-read immediate-restart path.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R2-H6 test error: {e}")
            return False

    async def test_gh58_r2_m3_spurious_tx_thresh_at_reset(self) -> bool:
        """INT_STATUS must read 0 immediately after reset, with no access.

        Mechanism: smbus_int_status.sv's edge detector compares the
        LIVE condition against r_cond_d, which resets to 0. tx_fifo_empty
        is already 1 at time zero (FIFO starts empty), so the very first
        post-reset cycle sees a rising edge that never really happened -
        SMBUS_INT_STATUS.tx_thresh_int (bit 2) sets itself spontaneously.
        """
        self.log.info("=== GH58-R2-M3: spurious tx_thresh interrupt at reset ===")
        try:
            await self._recover_and_reset()
            int_status = await self.tb.read_interrupt_status()
            self.log.info(f"  INT_STATUS immediately after reset: "
                           f"0x{int_status:02X}")

            if int_status == 0:
                self.log.warning("GH58-R2-M3 unexpectedly GREEN")
                return True

            self.log.error(
                f"GH58-R2-M3: INT_STATUS must read 0 after reset with no "
                f"access; got 0x{int_status:02X}. smbus_int_status.sv's "
                f"edge detector (w_set = w_cond & ~r_cond_d) compares "
                f"against r_cond_d's reset value of 0, so an "
                f"already-true level (tx_fifo_empty=1 from time zero) "
                f"looks like a rising edge on the first post-reset cycle.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R2-M3 test error: {e}")
            return False

    async def test_gh58_r2_m4_pec_register_readback(self) -> bool:
        """SMBUS_PEC must read the PEC byte actually transmitted on the wire."""
        self.log.info("=== GH58-R2-M4: SMBUS_PEC readback after a PEC-enabled write ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True, use_pec=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.write_data_byte(0x5A)

            packet = await self._run_write_and_capture(
                SMBusRegisterMap.TRANS_SEND_BYTE, 0x50, 0)

            _, pec_reg = await self.tb.read_register(SMBusRegisterMap.SMBUS_PEC)
            pec_reg &= 0xFF
            await self._recover_and_reset()

            expected_pec = SMBusCRC.calculate([(0x50 << 1) | 0, 0x5A])
            self.log.info(f"  packet={packet.formatted() if packet else None}, "
                           f"SMBUS_PEC readback=0x{pec_reg:02X}, "
                           f"expected=0x{expected_pec:02X}")

            if pec_reg == expected_pec:
                self.log.warning("GH58-R2-M4 unexpectedly GREEN")
                return True

            self.log.error(
                f"GH58-R2-M4: SMBUS_PEC must read the PEC byte transmitted "
                f"on the wire (SMBusCRC.calculate over addr+data) = "
                f"0x{expected_pec:02X}; got 0x{pec_reg:02X}. w_pec_valid "
                f"also fires for the PEC byte's own transmission "
                f"(w_byte_tx_state includes M_PEC_WR), folding the "
                f"already-computed PEC back into the running CRC one more "
                f"time before pec_we latches it into the register.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R2-M4 test error: {e}")
            return False

    async def test_gh58_r2_m5_fifo_underrun_overrun_contract(self) -> bool:
        """TX underrun (BLOCK_COUNT > staged bytes) must abort cleanly with
        error_int and a STOP, not fabricate data on the wire."""
        self.log.info("=== GH58-R2-M5: TX FIFO underrun contract ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=3000)
            await self.tb.reset_fifos()
            await self.tb.enable_interrupts(error=True)

            staged = [0x11, 0x22, 0x33]
            await self.tb.set_block_count(8)  # claims 8, only 3 staged
            await self.tb.write_tx_fifo(staged)

            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()

            await self.tb.start_transaction(SMBusRegisterMap.TRANS_BLOCK_WRITE,
                                             0x50, command=0x50)
            core = self._core()
            aborted = False
            for _ in range(4000):
                await RisingEdge(self.tb.pclk)
                if int(core.status_fsm_state.value) == M_IDLE and int(core.int_status.value) & 0x02:
                    aborted = True
                    break
                if int(core.status_complete.value):
                    break

            fifo_after = await self.tb.read_fifo_status()
            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            await self._recover_and_reset()

            self.log.info(f"  aborted_with_error_int={aborted}, "
                           f"tx_level after={fifo_after['tx_level']}")

            if aborted:
                self.log.warning("GH58-R2-M5 unexpectedly GREEN")
                return True

            self.log.error(
                f"GH58-R2-M5: BLOCK_COUNT=8 with only 3 bytes staged must "
                f"abort with error_int set once the FIFO underflows, not "
                f"complete/fabricate data. aborted_with_error_int={aborted}, "
                f"tx_level after={fifo_after['tx_level']} - no underrun "
                f"detection exists in smbus_core.sv today (w_tx_fifo_rd "
                f"does not check tx_fifo_empty against w_more_data).")
            return False
        except Exception as e:
            self.log.error(f"GH58-R2-M5 test error: {e}")
            return False

    async def test_gh58_r2_m6_block_count_clamp(self) -> bool:
        """A slave count byte of 0x40 must clamp to FIFO_DEPTH (32), not 1.

        Mechanism: w_rx_count_clamped's zero-check compares only
        w_rx_byte[5:0] against 0, not the full 8-bit byte - 0x40's low 6
        bits are all zero, so a 64-byte count is misread as a zero count
        and clamped to 1 instead of the (also-clamped) 32.
        """
        self.log.info("=== GH58-R2-M6: block-count clamp of a 0x40 slave count ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.reset_fifos()

            cmd = 0x55
            self.tb.smbus_slave.write_memory(cmd, [0x40] + [0xC0 + i for i in range(40)])
            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()

            await self.tb.start_transaction(SMBusRegisterMap.TRANS_BLOCK_READ,
                                             0x50, command=cmd)
            core = self._core()
            for _ in range(6000):
                await RisingEdge(self.tb.pclk)
                if int(core.status_complete.value) or int(core.status_bus_error.value):
                    break
            await ClockCycles(self.tb.pclk, 20)
            _, block_count_reg = await self.tb.read_register(
                SMBusRegisterMap.SMBUS_BLOCK_COUNT)
            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            await self._recover_and_reset()

            block_count_reg &= 0x3F
            self.log.info(f"  BLOCK_COUNT readback after a 0x40 slave count: "
                           f"{block_count_reg} (expected 32)")

            if block_count_reg == 32:
                self.log.warning("GH58-R2-M6 unexpectedly GREEN")
                return True

            self.log.error(
                f"GH58-R2-M6: a slave count byte of 0x40 (64) must clamp "
                f"to FIFO_DEPTH=32; got BLOCK_COUNT={block_count_reg} "
                f"(1 if the zero-clamp path fired instead). "
                f"w_rx_count_clamped checks `w_rx_byte[5:0]==0`, not the "
                f"full 8-bit byte - 0x40's low 6 bits are all zero.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R2-M6 test error: {e}")
            return False

    async def test_gh58_r2_m8_bus_free_before_start(self) -> bool:
        """Sharpened (coordinator round 3, since the first version came out
        GREEN without discriminating anything - it never actually checked
        the wire). Contract implemented in the current RTL: START's own
        first phase waits (w_busfree_phase && !w_bus_free, folded into the
        SAME w_stall used for clock stretching, itself counted by the
        SMBUS_TIMEOUT stall check) until BOTH SCL and SDA sample high.

        (a) slave holds SCL low, software writes start: no SDA falling
            edge while SCL is held low, busy=1 throughout; release SCL ->
            a proper START (SDA falls with SCL already high) follows and
            the transaction completes.
        (b) slave holds SCL low longer than SMBUS_TIMEOUT: timeout status,
            no transaction ever appears on the wire, lines released,
            busy=0.
        """
        self.log.info("=== GH58-R2-M8: bus-free wait before START (sharpened) ===")
        try:
            # --- (a) short hold, then release -> real START, completes
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=5000)  # 50us, generous
            await self.tb.write_data_byte(0x5A)

            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()
            self.tb.smbus_monitor.recv_queue.clear()
            self.tb._slave_scl_shim.value = 0  # external hold, before start

            await self.tb.start_transaction(SMBusRegisterMap.TRANS_SEND_BYTE, 0x50)

            core = self._core()
            busy_seen_a = False
            sda_moved_while_held = False
            for _ in range(300):  # short hold, well under the 5000-cycle timeout
                await RisingEdge(self.tb.pclk)
                if int(core.status_busy.value):
                    busy_seen_a = True
                if int(self.tb.dut.smb_sda_i.value) == 0:
                    sda_moved_while_held = True

            self.tb._slave_scl_shim.value = 1  # release the hold

            completed_a = False
            for _ in range(4000):
                await RisingEdge(self.tb.pclk)
                if int(core.status_complete.value):
                    completed_a = True
                    break
                if int(core.status_bus_error.value) or int(core.status_timeout_error.value):
                    break

            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            await self._recover_and_reset()

            self.log.info(f"  (a) busy_seen={busy_seen_a}, "
                           f"sda_moved_while_held={sda_moved_while_held}, "
                           f"completed_after_release={completed_a}")

            sub_a_ok = busy_seen_a and not sda_moved_while_held and completed_a

            # --- (b) hold past SMBUS_TIMEOUT -> timeout, nothing on the
            # wire, lines released, busy=0
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=500)  # 5us, small
            await self.tb.write_data_byte(0x5A)

            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()
            self.tb.smbus_monitor.recv_queue.clear()
            self.tb._slave_scl_shim.value = 0  # held for the whole sub-test

            await self.tb.start_transaction(SMBusRegisterMap.TRANS_SEND_BYTE, 0x50)

            timeout_and_recovered = False
            for _ in range(6000):  # 60us
                await RisingEdge(self.tb.pclk)
                if int(core.status_timeout_error.value) and not int(core.status_busy.value):
                    timeout_and_recovered = True
                    break

            lines_released = (int(self.tb.dut.smb_scl_t.value) == 1 and
                               int(self.tb.dut.smb_sda_t.value) == 1)
            new_packets_b = list(self.tb.smbus_monitor.recv_queue)

            self.tb._slave_scl_shim.value = 1
            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            await self._recover_and_reset()

            self.log.info(f"  (b) timeout_and_recovered={timeout_and_recovered}, "
                           f"lines_released={lines_released}, "
                           f"packets_on_wire={len(new_packets_b)}")

            sub_b_ok = (timeout_and_recovered and lines_released and
                        len(new_packets_b) == 0)

            if sub_a_ok and sub_b_ok:
                self.log.info("GH58-R2-M8 GREEN: bus-free wait honoured in "
                               "both the short-hold-then-release and the "
                               "held-past-timeout cases")
                return True

            self.log.error(
                f"GH58-R2-M8: bus-free-before-START contract violated - "
                f"(a) busy_seen={busy_seen_a}, "
                f"sda_moved_while_held={sda_moved_while_held} (must be "
                f"False), completed_after_release={completed_a}, "
                f"sub_a_ok={sub_a_ok}; (b) timeout_and_recovered="
                f"{timeout_and_recovered}, lines_released={lines_released}, "
                f"packets_on_wire={len(new_packets_b)} (must be 0), "
                f"sub_b_ok={sub_b_ok}.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R2-M8 test error: {e}")
            return False

    async def test_gh58_r2_l3_master_en_clear_guard(self) -> bool:
        """Guard: starting with master_en clear. Report what happens."""
        self.log.info("=== GH58-R2-L3 (guard): start with master_en clear ===")
        try:
            await self._recover_and_reset()
            await self.tb.write_register(SMBusRegisterMap.SMBUS_CONTROL, 0)  # master_en=0
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.write_data_byte(0x5A)
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_SEND_BYTE, 0x50)

            core = self._core()
            observed_states = set()
            for _ in range(50):
                await RisingEdge(self.tb.pclk)
                observed_states.add(int(core.status_fsm_state.value))

            status = await self.tb.read_status()
            await self._recover_and_reset()

            self.log.info(f"  master_en=0: states visited="
                           f"{sorted(hex(s) for s in observed_states)}, "
                           f"status={status}")

            stayed_idle = observed_states == {M_IDLE}
            if stayed_idle:
                self.log.info("GH58-R2-L3 GREEN: cmd_start is correctly "
                               "gated by cfg_master_en (w_start_req = "
                               "cmd_start && cfg_master_en) - FSM never "
                               "left M_IDLE")
                return True

            self.log.error(
                f"GH58-R2-L3: with master_en clear, cmd_start should be "
                f"ignored (w_start_req = cmd_start && cfg_master_en) - the "
                f"FSM should stay in M_IDLE. States visited: "
                f"{sorted(hex(s) for s in observed_states)}, "
                f"status={status}.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R2-L3 test error: {e}")
            return False

    async def test_gh58_r2_l4_quick_cmd_rw_bit(self) -> bool:
        """Guard: Quick Command with an R/W bit. Report what the register
        map does (SMBUS_COMMAND has no dedicated R/W field for Quick
        Command in this RDL - trans_type alone selects it, and
        smbus_trans_decode's is_read list omits TRANS_QUICK_CMD)."""
        self.log.info("=== GH58-R2-L4 (guard): Quick Command R/W bit ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)

            packet = await self._run_write_and_capture(
                SMBusRegisterMap.TRANS_QUICK_CMD, 0x50, None)
            await self._recover_and_reset()

            rw_observed = packet.read_write if packet else None
            self.log.info(f"  Quick Command wire R/W bit={rw_observed} "
                           f"(packet={packet.formatted() if packet else None})")

            self.log.info(
                "GH58-R2-L4 (report, not pass/fail): SMBUS_COMMAND has no "
                "dedicated R/W field for Quick Command in the current RDL - "
                "software selects TRANS_QUICK_CMD (trans_type=0x0) only, "
                "and smbus_trans_decode.sv's is_read list does not include "
                "it, so r_read_phase is always 0 (write) for a Quick "
                "Command regardless of any 'read' intent - there is "
                "structurally no way to issue a Quick Command with R/W=1 "
                "through this register map today.")
            return True
        except Exception as e:
            self.log.error(f"GH58-R2-L4 test error: {e}")
            return False

    # ==================================================================
    # GH58-R3 batch (coordinator round 4): the round-3 review MEASURED
    # the root cause directly in smbus_bit_phy.sv - PHY_OP_STOP releases
    # SDA on `r_phase == 0`, the EXACT SAME predicate that releases SCL,
    # so SDA never rises while SCL is already sampled high: no real STOP
    # condition is ever generated on the wire, for ANY transaction type
    # or abort path. The monitor investigation in the round-3 (H1/H2)
    # work was chasing a DV symptom of this real RTL bug; the framework
    # fix that let the monitor "recover" a same-cycle SCL/SDA release as
    # STOP was reverted (see _wait_scl_edge_or_condition's history) - a
    # monitor that manufactures a STOP that never happened on the wire
    # would hide this finding, not expose it.
    # ==================================================================

    async def _watch_for_real_stop(self, window_cycles=2500):
        """Watch smb_scl_i/smb_sda_i for a GENUINE STOP: SDA rising
        between two consecutive pclk samples where SCL was ALREADY 1 on
        the sample BEFORE SDA changed (not the same cycle - a same-cycle
        release is the confirmed RTL bug, not a real STOP)."""
        prev_scl = int(self.tb.dut.smb_scl_i.value)
        prev_sda = int(self.tb.dut.smb_sda_i.value)
        for _ in range(window_cycles):
            await RisingEdge(self.tb.pclk)
            cur_scl = int(self.tb.dut.smb_scl_i.value)
            cur_sda = int(self.tb.dut.smb_sda_i.value)
            if prev_scl == 1 and cur_scl == 1 and prev_sda == 0 and cur_sda == 1:
                return True
            prev_scl, prev_sda = cur_scl, cur_sda
        return False

    async def _watch_bus_recovery_then_stop(self, window_cycles=6000):
        """After an abort where the slave BFM is left stuck holding SDA
        low (_send_ack waiting on a master SCL edge that an aborted
        master never produces), the RTL's standard bus-recovery
        sequence (PHY_OP_RECOVER) pulses SCL up to nine times with SDA
        released by the master, sampling SDA at the end of each high
        phase, until SDA reads high, then issues a real STOP.

        GATED (round-5 tightening): counting starts only once the abort
        has actually happened - the first observation of EITHER
        core.status_timeout_error asserted OR the PHY entering
        PHY_OP_RECOVER (white-box: core.u_bit_phy.r_op == 5). Before
        that point, ordinary in-transaction SCL edges legitimately
        coincide with the master releasing SDA (ACK reception,
        transmitting a data bit value of 1) and must NOT be counted as
        recovery clocks - counting from transaction start (the original
        round-4 mechanism) inflated the true count of 2 up to 5 by
        picking those up.

        Returns (recovery_clocks, stop_seen): recovery_clocks counts
        SCL rising edges on the wire, after the gate opens, observed
        with the master's own SDA drive released (smb_sda_t==1);
        stop_seen is the same genuine-STOP predicate as
        _watch_for_real_stop. Returns as soon as STOP is detected, or
        after window_cycles with stop_seen=False (e.g. GH58-R3-6, where
        the "slave" never frees SDA and recovery gives up after nine
        clocks with no STOP)."""
        core = self._core()
        PHY_OP_RECOVER = 5
        gate_open = False
        recovery_clocks = 0
        prev_scl = int(self.tb.dut.smb_scl_i.value)
        prev_sda = int(self.tb.dut.smb_sda_i.value)
        for _ in range(window_cycles):
            await RisingEdge(self.tb.pclk)
            cur_scl = int(self.tb.dut.smb_scl_i.value)
            cur_sda = int(self.tb.dut.smb_sda_i.value)
            if not gate_open and (int(core.status_timeout_error.value) or
                                   int(core.u_bit_phy.r_op.value) == PHY_OP_RECOVER):
                gate_open = True
            sda_released_by_master = int(self.tb.dut.smb_sda_t.value) == 1
            if (gate_open and prev_scl == 1 and cur_scl == 1 and
                    prev_sda == 0 and cur_sda == 1):
                return recovery_clocks, True
            if gate_open and prev_scl == 0 and cur_scl == 1 and sda_released_by_master:
                recovery_clocks += 1
            prev_scl, prev_sda = cur_scl, cur_sda
        return recovery_clocks, False

    def _expected_packet_count(self, trans_type):
        """SMBus 2.0 5.5.5: a "read" transaction with a command byte is
        two START-delimited segments (S Addr+W Cmd A, then Sr Addr+R
        data... P); the monitor closes a packet at each START, so these
        three types correctly produce TWO packets, the second beginning
        Addr+R. Block Process Call is also write-then-read (repeated
        START) and so also produces two packets. Everything else is one
        segment, one packet."""
        M = SMBusRegisterMap
        two_packet = {M.TRANS_READ_BYTE, M.TRANS_READ_WORD,
                      M.TRANS_BLOCK_READ, M.TRANS_BLOCK_PROC}
        return 2 if trans_type in two_packet else 1

    def _stop_window_cycles(self, trans_type):
        """Watcher window sized from the transaction's approximate byte
        length instead of a single constant for every type - a fixed
        2500-cycle constant is fine for a handful of bytes but silently
        starves a multi-segment block transfer (GH58-R3 round-4 finding:
        Block Process Call's read half ran ~77us against a 2500-cycle
        window when the slave BFM answered with a bogus 0xFF count)."""
        M = SMBusRegisterMap
        approx_bytes = {
            M.TRANS_QUICK_CMD: 1, M.TRANS_SEND_BYTE: 2,
            M.TRANS_RECV_BYTE: 2, M.TRANS_WRITE_BYTE: 3,
            M.TRANS_READ_BYTE: 4, M.TRANS_WRITE_WORD: 4,
            M.TRANS_READ_WORD: 5, M.TRANS_BLOCK_WRITE: 6,
            M.TRANS_BLOCK_READ: 6, M.TRANS_BLOCK_PROC: 9,
        }.get(trans_type, 6)
        # ~9 SCL edges/byte at this clk_div, generous per-edge pclk
        # budget, plus fixed START/STOP/ACK framing overhead.
        return 600 + approx_bytes * 300

    async def _setup_and_start(self, trans_type, cmd=0x10):
        """Configure and issue one transaction of the given type against
        the real slave/monitor BFMs, preloading whatever data/memory that
        type needs. Returns nothing; caller races _watch_for_real_stop
        against the transaction's own completion."""
        await self.tb.reset_fifos()
        slave_addr = 0x50
        if trans_type == SMBusRegisterMap.TRANS_QUICK_CMD:
            await self.tb.start_transaction(trans_type, slave_addr)
        elif trans_type == SMBusRegisterMap.TRANS_SEND_BYTE:
            await self.tb.write_data_byte(0x5A)
            await self.tb.start_transaction(trans_type, slave_addr)
        elif trans_type == SMBusRegisterMap.TRANS_RECV_BYTE:
            self.tb.smbus_slave.write_memory(0, [0xE7])
            await self.tb.start_transaction(trans_type, slave_addr)
        elif trans_type == SMBusRegisterMap.TRANS_WRITE_BYTE:
            await self.tb.write_data_byte(0x5A)
            await self.tb.start_transaction(trans_type, slave_addr, command=cmd)
        elif trans_type == SMBusRegisterMap.TRANS_READ_BYTE:
            self.tb.smbus_slave.write_memory(cmd, [0xE7])
            await self.tb.start_transaction(trans_type, slave_addr, command=cmd)
        elif trans_type == SMBusRegisterMap.TRANS_WRITE_WORD:
            await self.tb.write_tx_fifo([0xAA, 0xBB])
            await self.tb.start_transaction(trans_type, slave_addr, command=cmd)
        elif trans_type == SMBusRegisterMap.TRANS_READ_WORD:
            self.tb.smbus_slave.write_memory(cmd, [0xAA, 0xBB])
            await self.tb.start_transaction(trans_type, slave_addr, command=cmd)
        elif trans_type == SMBusRegisterMap.TRANS_BLOCK_WRITE:
            await self.tb.set_block_count(3)
            await self.tb.write_tx_fifo([0x11, 0x22, 0x33])
            await self.tb.start_transaction(trans_type, slave_addr, command=cmd)
        elif trans_type == SMBusRegisterMap.TRANS_BLOCK_READ:
            self.tb.smbus_slave.write_memory(cmd, [3, 0xD1, 0xD2, 0xD3])
            await self.tb.start_transaction(trans_type, slave_addr, command=cmd)
        elif trans_type == SMBusRegisterMap.TRANS_BLOCK_PROC:
            write_data = [0xA1, 0xA2]
            await self.tb.set_block_count(len(write_data))
            await self.tb.write_tx_fifo(write_data)
            # SMBusSlave._handle_write treats the first byte after the
            # address as the target address (=cmd), then stores the
            # write-count byte and each write-data byte at successive
            # addresses, advancing _current_addr by 1 (count) + len
            # (data) past cmd. The repeated-START read half then
            # continues from THAT address, not from cmd - preload the
            # read-half count+data there, not at cmd (coordinator R3
            # round-4 finding: preloading at cmd made the read half's
            # count byte come back as the BFM's 0xFF default, which
            # the RTL clamps to FIFO_DEPTH and runs a 32-byte read).
            read_addr = cmd + 1 + len(write_data)
            self.tb.smbus_slave.write_memory(read_addr, [2, 0xB1, 0xB2])
            await self.tb.start_transaction(trans_type, slave_addr, command=cmd)

    async def test_gh58_r3_1_stop_condition_every_type(self) -> bool:
        """Every transaction type, and every abort path, must produce a
        real STOP on the wire and the SMBus-2.0-correct number of monitor
        packets: one for a single-segment transaction, two for any type
        with a repeated START (Read Byte/Word, Block Read, Block Process
        Call), with the second packet starting Addr+R."""
        self.log.info("=== GH58-R3-1: real STOP condition for every transaction type ===")
        M = SMBusRegisterMap
        types = [
            (M.TRANS_QUICK_CMD, "QuickCmd"), (M.TRANS_SEND_BYTE, "SendByte"),
            (M.TRANS_RECV_BYTE, "RecvByte"), (M.TRANS_WRITE_BYTE, "WriteByte"),
            (M.TRANS_READ_BYTE, "ReadByte"), (M.TRANS_WRITE_WORD, "WriteWord"),
            (M.TRANS_READ_WORD, "ReadWord"), (M.TRANS_BLOCK_WRITE, "BlockWrite"),
            (M.TRANS_BLOCK_READ, "BlockRead"), (M.TRANS_BLOCK_PROC, "BlockProc"),
        ]
        core = self._core()
        failures = []
        try:
            for trans_type, name in types:
                await self._recover_and_reset()
                await self.tb.enable_master_mode(enable=True)
                await self.tb.configure_clock(clk_div=2)
                await self.tb.configure_timeout(timeout=200000)

                self.tb.smbus_slave.clock_stretch_cycles = 0
                self.tb.smbus_slave.start()
                self.tb.smbus_monitor.start()
                self.tb.smbus_monitor.recv_queue.clear()

                window = self._stop_window_cycles(trans_type)
                stop_task = cocotb.start_soon(self._watch_for_real_stop(window))
                await self._setup_and_start(trans_type)

                for _ in range(window):
                    await RisingEdge(self.tb.pclk)
                    if int(core.status_complete.value) or int(core.status_bus_error.value):
                        break
                await ClockCycles(self.tb.pclk, 50)
                stop_seen = await stop_task.join()
                pkts_list = list(self.tb.smbus_monitor.recv_queue)
                packets = len(pkts_list)
                expected_pkts = self._expected_packet_count(trans_type)

                self.tb.smbus_slave.stop()
                self.tb.smbus_monitor.stop()

                second_ok = True
                if expected_pkts == 2:
                    second_ok = (packets == 2 and pkts_list[1].read_write == 1 and
                                 pkts_list[1].slave_addr == 0x50)

                self.log.info(f"  {name}: stop_seen={stop_seen}, packets={packets} "
                              f"(expected {expected_pkts}), second_ok={second_ok}")
                if not (stop_seen and packets == expected_pkts and second_ok):
                    failures.append(
                        f"{name}(stop={stop_seen},pkts={packets},"
                        f"expected={expected_pkts},second_ok={second_ok})")

            await self._recover_and_reset()

            # --- Abort paths ---
            # cmd_stop alone, mid-transfer
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.reset_fifos()
            await self.tb.set_block_count(8)
            await self.tb.write_tx_fifo([0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88])
            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()
            self.tb.smbus_monitor.recv_queue.clear()
            stop_task = cocotb.start_soon(self._watch_for_real_stop(3000))
            await self.tb.start_transaction(M.TRANS_BLOCK_WRITE, 0x50, command=0x40)
            for _ in range(20):
                await RisingEdge(self.tb.pclk)
                if int(core.status_busy.value):
                    break
            await self.tb.write_register(SMBusRegisterMap.SMBUS_COMMAND,
                                          SMBusRegisterMap.COMMAND_STOP)
            for _ in range(2500):
                await RisingEdge(self.tb.pclk)
                if not int(core.status_busy.value):
                    break
            await ClockCycles(self.tb.pclk, 50)
            stop_seen_abort1 = await stop_task.join()
            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            self.log.info(f"  abort(cmd_stop alone): stop_seen={stop_seen_abort1}")
            if not stop_seen_abort1:
                failures.append("abort(cmd_stop_alone)")
            await self._recover_and_reset()

            # timeout abort - the slave BFM's _send_ack holds SDA low
            # waiting for a master SCL edge that an aborted master never
            # produces, so recovery requires the RTL's standard 9-clock
            # bus recovery (SCL pulsed with SDA released) to free it
            # before a real STOP is possible.
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=500)
            await self.tb.write_data_byte(0x5A)
            self.tb.smbus_slave.clock_stretch_cycles = 1500
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()
            self.tb.smbus_monitor.recv_queue.clear()
            recovery_task = cocotb.start_soon(self._watch_bus_recovery_then_stop(6000))
            await self.tb.start_transaction(M.TRANS_WRITE_BYTE, 0x50, command=0x01)
            for _ in range(6000):
                await RisingEdge(self.tb.pclk)
                if int(core.status_timeout_error.value) and not int(core.status_busy.value):
                    break
            await ClockCycles(self.tb.pclk, 50)
            recovery_clocks2, stop_seen_abort2 = await recovery_task.join()
            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            self.log.info(f"  abort(timeout): recovery_clocks={recovery_clocks2} "
                          f"(want exactly 3, zero-based: clock 0 SDA low, "
                          f"clock 1 SDA low (slave releases at its falling "
                          f"edge), clock 2 SDA sampled high -> stop pulsing), "
                          f"stop_seen={stop_seen_abort2}")
            if not (recovery_clocks2 == 3 and stop_seen_abort2):
                failures.append(
                    f"abort(timeout)(recovery_clocks={recovery_clocks2},"
                    f"stop={stop_seen_abort2})")
            await self._recover_and_reset()

            # TX underrun abort
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=3000)
            await self.tb.reset_fifos()
            await self.tb.set_block_count(8)
            await self.tb.write_tx_fifo([0x11, 0x22, 0x33])  # only 3 of 8 staged
            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()
            self.tb.smbus_monitor.recv_queue.clear()
            stop_task = cocotb.start_soon(self._watch_for_real_stop(4000))
            await self.tb.start_transaction(M.TRANS_BLOCK_WRITE, 0x50, command=0x50)
            for _ in range(4000):
                await RisingEdge(self.tb.pclk)
                if not int(core.status_busy.value):
                    break
            await ClockCycles(self.tb.pclk, 50)
            stop_seen_abort3 = await stop_task.join()
            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            self.log.info(f"  abort(tx_underrun): stop_seen={stop_seen_abort3}")
            if not stop_seen_abort3:
                failures.append("abort(tx_underrun)")
            await self._recover_and_reset()

            if not failures:
                self.log.warning("GH58-R3-1 unexpectedly GREEN")
                return True

            self.log.error(
                f"GH58-R3-1: wrong STOP/packet-count contract for: "
                f"{', '.join(failures)}.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R3-1 test error: {e}")
            return False

    async def _watch_for_real_start(self, window_cycles=1000):
        """Watch for a genuine START: SDA falling while SCL was ALREADY
        sampled high on the sample before."""
        prev_scl = int(self.tb.dut.smb_scl_i.value)
        prev_sda = int(self.tb.dut.smb_sda_i.value)
        for _ in range(window_cycles):
            await RisingEdge(self.tb.pclk)
            cur_scl = int(self.tb.dut.smb_scl_i.value)
            cur_sda = int(self.tb.dut.smb_sda_i.value)
            if prev_scl == 1 and cur_scl == 1 and prev_sda == 1 and cur_sda == 0:
                return True
            prev_scl, prev_sda = cur_scl, cur_sda
        return False

    async def test_gh58_r3_2_busy_zero_coincides_with_release(self) -> bool:
        """busy==0 must coincide with BOTH lines released and the abort's
        STOP genuinely complete - not just the core's own bookkeeping.
        Today: busy drops while SCL is still driven low for ~16 cycles,
        and a start written into that window is swallowed (address bits
        go out with no real START preceding them)."""
        self.log.info("=== GH58-R3-2: busy=0 must coincide with lines released ===")
        core = self._core()
        try:
            # --- (a) timeout path. The slave BFM's _send_ack holds SDA
            # low waiting for a master SCL edge that an aborted master
            # never produces, so recovery requires the RTL's standard
            # 9-clock bus-recovery sequence (SCL pulsed with SDA released
            # by the master) before a real STOP, released lines and
            # busy=0 are possible.
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=500)
            await self.tb.write_data_byte(0x5A)
            self.tb.smbus_slave.clock_stretch_cycles = 1500
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()
            recovery_task = cocotb.start_soon(self._watch_bus_recovery_then_stop(6000))
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x01)

            busy_was_1 = False
            for _ in range(6000):
                await RisingEdge(self.tb.pclk)
                b = int(core.status_busy.value)
                if b:
                    busy_was_1 = True
                if busy_was_1 and not b:
                    break

            recovery_clocks_a, stop_seen_a = await recovery_task.join()

            released_throughout_a = True
            for _ in range(20):
                scl_t = int(self.tb.dut.smb_scl_t.value)
                sda_t = int(self.tb.dut.smb_sda_t.value)
                if not (scl_t == 1 and sda_t == 1):
                    released_throughout_a = False
                await RisingEdge(self.tb.pclk)

            # Issue a fresh transaction right here and confirm it produces
            # a REAL START, not an unframed address.
            start_task = cocotb.start_soon(self._watch_for_real_start(1500))
            await self.tb.write_data_byte(0x5B)
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x02)
            for _ in range(2500):
                await RisingEdge(self.tb.pclk)
                if int(core.status_complete.value) or int(core.status_bus_error.value):
                    break
            await ClockCycles(self.tb.pclk, 30)
            real_start_seen_a = await start_task.join()

            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            await self._recover_and_reset()

            self.log.info(f"  (a) recovery_clocks={recovery_clocks_a} "
                           f"(want exactly 3, zero-based: clock 0 SDA low, "
                           f"clock 1 SDA low (slave releases at its falling "
                           f"edge), clock 2 SDA sampled high -> stop "
                           f"pulsing), stop_seen={stop_seen_a}, "
                           f"released_throughout={released_throughout_a}, "
                           f"real_start_after={real_start_seen_a}")
            recovery_ok_a = recovery_clocks_a == 3 and stop_seen_a
            sub_a_ok = recovery_ok_a and released_throughout_a and real_start_seen_a

            # --- (b) cmd_stop-alone sweep, >=40 points across a transfer
            NUM_POINTS = 40
            violations = []
            for point in range(NUM_POINTS):
                await self.tb.enable_master_mode(enable=True)
                await self.tb.configure_clock(clk_div=2)
                await self.tb.configure_timeout(timeout=200000)
                await self.tb.reset_fifos()
                await self.tb.set_block_count(8)
                await self.tb.write_tx_fifo([0x11, 0x22, 0x33, 0x44,
                                              0x55, 0x66, 0x77, 0x88])
                self.tb.smbus_slave.clock_stretch_cycles = 0
                self.tb.smbus_slave.start()
                self.tb.smbus_monitor.start()

                await self.tb.start_transaction(SMBusRegisterMap.TRANS_BLOCK_WRITE,
                                                 0x50, command=0x40)
                # Delay proportional to point index, spanning roughly one
                # full block-write transfer's worth of cycles.
                await ClockCycles(self.tb.pclk, 10 + point * 25)
                await self.tb.write_register(SMBusRegisterMap.SMBUS_COMMAND,
                                              SMBusRegisterMap.COMMAND_STOP)

                busy_was_1_p = False
                for _ in range(1200):
                    await RisingEdge(self.tb.pclk)
                    b = int(core.status_busy.value)
                    if b:
                        busy_was_1_p = True
                    if busy_was_1_p and not b:
                        break
                    if not busy_was_1_p and not b:
                        # never went busy (transaction already finished
                        # before the delay elapsed) - not a useful point
                        break

                scl_t = int(self.tb.dut.smb_scl_t.value)
                sda_t = int(self.tb.dut.smb_sda_t.value)
                released_p = (scl_t == 1 and sda_t == 1)

                self.tb.smbus_slave.stop()
                self.tb.smbus_monitor.stop()
                await self._recover_and_reset()

                if not released_p:
                    violations.append(point)

            self.log.info(f"  (b) sweep: {len(violations)}/{NUM_POINTS} points "
                           f"showed busy=0 without both lines released "
                           f"(points: {violations[:10]}{'...' if len(violations) > 10 else ''})")
            sub_b_ok = len(violations) == 0

            if sub_a_ok and sub_b_ok:
                self.log.warning("GH58-R3-2 unexpectedly GREEN")
                return True

            self.log.error(
                f"GH58-R3-2: busy=0 does not reliably coincide with both "
                f"lines released - (a) recovery_clocks={recovery_clocks_a} "
                f"(want exactly 3), stop_seen={stop_seen_a}, "
                f"released_throughout={released_throughout_a}, "
                f"real_start_after_release={real_start_seen_a}, sub_a_ok="
                f"{sub_a_ok}; (b) {len(violations)}/{NUM_POINTS} sweep points "
                f"violated it, sub_b_ok={sub_b_ok}.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R3-2 test error: {e}")
            return False

    async def test_gh58_r3_3_rx_fifo_full_receive_byte(self) -> bool:
        """RX FIFO full, then Receive Byte: the master must NAK that byte,
        STOP, set error_int, and the byte must not be silently lost with
        complete=1. Today: complete=1, bus_error=0, byte gone -
        w_rx_fifo_wr is asserted whenever a data byte completes in
        M_DATA_RD with no rx_fifo_full check at all."""
        self.log.info("=== GH58-R3-3: RX FIFO full then Receive Byte ===")
        core = self._core()
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.enable_interrupts(error=True)
            await self.tb.reset_fifos()

            cmd = 0x50
            fill_data = [32] + [0xC0 + i for i in range(32)]  # count=32 + 32 bytes
            self.tb.smbus_slave.write_memory(cmd, fill_data)
            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()

            await self.tb.start_transaction(SMBusRegisterMap.TRANS_BLOCK_READ,
                                             0x50, command=cmd)
            for _ in range(8000):
                await RisingEdge(self.tb.pclk)
                if int(core.status_complete.value) or int(core.status_bus_error.value):
                    break
            await ClockCycles(self.tb.pclk, 20)

            fifo_status = await self.tb.read_fifo_status()
            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()

            self.log.info(f"  After filling block read: rx_level="
                           f"{fifo_status['rx_level']}, rx_full="
                           f"{fifo_status['rx_full']}")

            if fifo_status['rx_level'] != 32 or not fifo_status['rx_full']:
                self.log.error(
                    f"GH58-R3-3: could not reach a full RX FIFO to set up "
                    f"the test (rx_level={fifo_status['rx_level']}, "
                    f"rx_full={fifo_status['rx_full']}) - treating as RED "
                    f"pending investigation.")
                await self._recover_and_reset()
                return False

            # Do NOT drain. Now attempt Receive Byte against the full FIFO.
            self.tb.smbus_slave.write_memory(0, [0xEE])
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()

            await self.tb.start_transaction(SMBusRegisterMap.TRANS_RECV_BYTE, 0x50)
            for _ in range(3000):
                await RisingEdge(self.tb.pclk)
                if int(core.status_complete.value) or int(core.status_bus_error.value):
                    break
            await ClockCycles(self.tb.pclk, 20)

            status_after = await self.tb.read_status()
            int_status_after = await self.tb.read_interrupt_status()
            fifo_after = await self.tb.read_fifo_status()

            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            await self._recover_and_reset()

            self.log.info(f"  After Receive Byte against full RX FIFO: "
                           f"status={status_after}, "
                           f"INT_STATUS=0x{int_status_after:02X}, "
                           f"rx_level={fifo_after['rx_level']}")

            byte_silently_completed = status_after['complete'] and not (
                status_after['bus_error'] or status_after['nak_received'] or
                (int_status_after & 0x02))

            if not byte_silently_completed:
                self.log.warning("GH58-R3-3 unexpectedly GREEN")
                return True

            self.log.error(
                f"GH58-R3-3: Receive Byte against a full RX FIFO must NAK, "
                f"STOP and set error_int, not silently complete. Got "
                f"status={status_after}, "
                f"INT_STATUS=0x{int_status_after:02X} - complete=1 with no "
                f"error reported means the byte was accepted off the wire "
                f"and then dropped, since M_DATA_RD's w_rx_fifo_wr has no "
                f"rx_fifo_full check at all.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R3-3 test error: {e}")
            return False

    # ==================================================================
    # Guards (coordinator round 4): expected GREEN, report either way.
    # ==================================================================

    async def test_gh58_r3_4_fast_mode_stop_buf_units_fixed(self) -> bool:
        """Guard: tSU;STO and tBUF must be 5 units in BOTH standard and
        fast mode (only tHD;STA/tSU;STA shrink in fast mode) -
        smbus_bit_phy.sv's U_SU_STO/U_BUF localparams have no
        cfg_fast_mode ternary, unlike U_HD_STA/U_SU_STA."""
        self.log.info("=== GH58-R3-4 (guard): tSU;STO/tBUF fixed at 5 units ===")
        core = self._core()
        try:
            results = {}
            for fast in (False, True):
                await self._recover_and_reset()
                await self.tb.enable_master_mode(enable=True, fast_mode=fast)
                await self.tb.configure_clock(clk_div=63)
                await self.tb.configure_timeout(timeout=200000)
                await self.tb.write_data_byte(0x5A)
                await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                                 0x50, command=0x01)
                # No slave started -> address NAKs -> M_ERROR -> STOP
                # primitive issued; whitebox-sample w_phase_units at
                # PHY_OP_STOP's phase 2 (SU_STO) and phase 3 (BUF).
                # Standard mode's units are ~3.5x fast mode's at this
                # clk_div, and the address byte alone is ~9 bits * 4
                # phases - budget generously for the slower mode.
                units_p2 = units_p3 = None
                for _ in range(6000):
                    await RisingEdge(self.tb.pclk)
                    if int(core.u_bit_phy.r_op.value) == 2:  # PHY_OP_STOP
                        phase = int(core.u_bit_phy.r_phase.value)
                        if phase == 2 and units_p2 is None:
                            units_p2 = int(core.u_bit_phy.w_phase_units.value)
                        if phase == 3 and units_p3 is None:
                            units_p3 = int(core.u_bit_phy.w_phase_units.value)
                    if units_p2 is not None and units_p3 is not None:
                        break
                await self._recover_and_reset()
                results[fast] = (units_p2, units_p3)
                self.log.info(f"  fast_mode={fast}: SU_STO units={units_p2}, "
                               f"BUF units={units_p3}")

            std_p2, std_p3 = results[False]
            fst_p2, fst_p3 = results[True]
            all_ok = (std_p2 == 5 and std_p3 == 5 and
                      fst_p2 == 5 and fst_p3 == 5)

            if all_ok:
                self.log.info("GH58-R3-4 GREEN: tSU;STO and tBUF both fixed "
                               "at 5 units regardless of fast_mode")
                return True

            self.log.error(
                f"GH58-R3-4: expected 5 units for both SU_STO and BUF in "
                f"both modes; got standard=({std_p2},{std_p3}), "
                f"fast=({fst_p2},{fst_p3}).")
            return False
        except Exception as e:
            self.log.error(f"GH58-R3-4 test error: {e}")
            return False

    async def test_gh58_r3_5_strobe_width_two_pclk(self) -> bool:
        """Guard: soft_reset/start/stop/fifo_reset field strobes are two
        pclk wide behind the peakrdl_to_cmdrsp bridge (it holds a write
        request for two cycles), and the engine still acts exactly once
        per software write."""
        self.log.info("=== GH58-R3-5 (guard): strobe width behind the bridge ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)

            # Fill both FIFOs with known data so a double-actuation of
            # soft_reset (if it happened) would still just leave them
            # empty either way - the STROBE WIDTH itself is the signal
            # under test, not a FIFO side effect.
            await self.tb.reset_fifos()
            await self.tb.write_tx_fifo([0x11, 0x22])

            _, control_before = await self.tb.read_register(
                SMBusRegisterMap.SMBUS_CONTROL)

            # Watcher started BEFORE the write (learned from GH58-3's
            # original bug): the APB write itself takes several pclk
            # cycles to commit, and a watcher started only AFTER awaiting
            # it can already be past the 2-cycle-wide strobe.
            samples = []

            async def _watch_strobe():
                for _ in range(30):
                    await RisingEdge(self.tb.pclk)
                    samples.append(int(self.tb.dut.w_cfg_soft_reset.value))

            watcher = cocotb.start_soon(_watch_strobe())
            await self.tb.write_register(
                SMBusRegisterMap.SMBUS_CONTROL,
                control_before | SMBusRegisterMap.CONTROL_SOFT_RESET)
            await watcher.join()

            widths = 0
            seen_high = False
            for v in samples:
                if v:
                    widths += 1
                    seen_high = True
                elif seen_high:
                    break

            fifo_after = await self.tb.read_fifo_status()
            _, control_after = await self.tb.read_register(
                SMBusRegisterMap.SMBUS_CONTROL)
            await self._recover_and_reset()

            self.log.info(f"  w_cfg_soft_reset asserted for {widths} pclk "
                           f"cycles; fifo_after={fifo_after}; "
                           f"CONTROL.soft_reset readback="
                           f"{bool(control_after & SMBusRegisterMap.CONTROL_SOFT_RESET)}")

            width_ok = widths == 2
            acted_once_ok = (fifo_after['tx_level'] == 0 and
                              fifo_after['rx_level'] == 0 and
                              not (control_after & SMBusRegisterMap.CONTROL_SOFT_RESET))

            if width_ok and acted_once_ok:
                self.log.info("GH58-R3-5 GREEN: strobe is exactly 2 pclk "
                               "wide and the engine acted exactly once")
                return True

            self.log.error(
                f"GH58-R3-5: expected a 2-pclk-wide soft_reset strobe with "
                f"the engine acting exactly once - got width={widths} "
                f"(expected 2), acted_once_ok={acted_once_ok} "
                f"(fifo_after={fifo_after}).")
            return False
        except Exception as e:
            self.log.error(f"GH58-R3-5 test error: {e}")
            return False

    async def test_gh58_r3_6_slave_never_releases_sda(self) -> bool:
        """A slave that never releases SDA, not even through all nine
        bus-recovery clocks: the master must give up, release BOTH
        lines, report bus_error (and timeout), busy=0, and must NOT
        fabricate a STOP condition it cannot actually drive (SDA is
        held low by the "slave" throughout, on the wire). After the
        stuck slave finally lets go, a fresh transaction must work
        normally.

        Models the always-stuck slave directly through the TB's
        open-drain bus-model shim (`_slave_sda_shim`), independent of
        the SMBusSlave BFM (which always eventually releases) - this is
        the wired-AND bus model already used by every other GH58-R2/R3
        test, not a hand-rolled driver."""
        self.log.info("=== GH58-R3-6: slave holds SDA low through all recovery clocks ===")
        core = self._core()
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=500)
            await self.tb.write_data_byte(0x5A)

            self.tb.smbus_monitor.start()
            self.tb.smbus_monitor.recv_queue.clear()
            # Force the wire-model shim low directly: a "slave" that
            # never releases SDA, for a window comfortably longer than
            # nine recovery clocks plus a real STOP could ever take.
            self.tb._slave_sda_shim.value = 0
            self.tb._slave_scl_shim.value = 1

            # Gated recovery watcher, started BEFORE the transaction so
            # it is running concurrently through the abort (same pattern
            # as GH58-R3-1/R3-2): with SDA never freed, every one of the
            # nine recovery clocks should be counted and no STOP should
            # ever appear.
            recovery_task = cocotb.start_soon(self._watch_bus_recovery_then_stop(6000))
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x01)

            for _ in range(6000):
                await RisingEdge(self.tb.pclk)
                if int(core.status_timeout_error.value) and not int(core.status_busy.value):
                    break

            recovery_clocks_r6, fake_stop_seen = await recovery_task.join()

            released_both = (int(self.tb.dut.smb_scl_t.value) == 1 and
                              int(self.tb.dut.smb_sda_t.value) == 1)
            busy_now = int(core.status_busy.value)
            bus_error_now = int(core.status_bus_error.value)
            timeout_now = int(core.status_timeout_error.value)

            self.tb.smbus_monitor.stop()

            self.log.info(
                f"  recovery_clocks={recovery_clocks_r6} (want exactly 9), "
                f"fake_stop_seen={fake_stop_seen} (must be False), "
                f"released_both={released_both}, busy={busy_now}, "
                f"bus_error={bus_error_now}, timeout={timeout_now}")

            # The stuck "slave" finally lets go - confirm a fresh
            # transaction against the real SMBusSlave BFM now works.
            self.tb._slave_sda_shim.value = 1
            self.tb._slave_scl_shim.value = 1
            await self._recover_and_reset()

            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()
            self.tb.smbus_monitor.recv_queue.clear()
            start_task = cocotb.start_soon(self._watch_for_real_start(1500))
            await self.tb.write_data_byte(0x5B)
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x02)
            for _ in range(2500):
                await RisingEdge(self.tb.pclk)
                if int(core.status_complete.value) or int(core.status_bus_error.value):
                    break
            await ClockCycles(self.tb.pclk, 30)
            real_start_after = await start_task.join()
            recovered_ok = (int(core.status_complete.value) == 1 and real_start_after)

            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            await self._recover_and_reset()

            self.log.info(f"  after shim release: real_start={real_start_after}, "
                          f"recovered_ok={recovered_ok}")

            ok = (recovery_clocks_r6 == 9 and (not fake_stop_seen) and
                  released_both and (not busy_now) and
                  bus_error_now and timeout_now and recovered_ok)

            if ok:
                self.log.info("GH58-R3-6 GREEN")
                return True

            self.log.error(
                f"GH58-R3-6: slave-never-releases-SDA contract violated - "
                f"recovery_clocks={recovery_clocks_r6} (want exactly 9), "
                f"fake_stop_seen={fake_stop_seen} (must be False), "
                f"released_both={released_both}, busy={busy_now}, "
                f"bus_error={bus_error_now}, timeout={timeout_now}, "
                f"recovered_ok={recovered_ok}. After nine recovery clocks "
                f"fail to free SDA, the master must give up, release both "
                f"lines and report bus_error rather than either wedging "
                f"forever or fabricating a STOP it cannot actually drive.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R3-6 test error: {e}")
            return False

    # ==================================================================
    # GH58-R4 batch (coordinator round 4 review): RED tests against the
    # CURRENT RTL, mechanisms traced by direct reading of smbus_core.sv
    # and smbus_bit_phy.sv (cross-checked against the reviewer's r4sim/
    # scratch Verilator harnesses for stimulus shapes). Same file, no
    # RTL edits, no ledger.
    # ==================================================================

    async def test_gh58_r4_1_complete_after_failed_recovery(self) -> bool:
        """HIGH: when a device holds SDA low so the final STOP escalates
        into bus recovery and all nine recovery clocks fail, complete=1
        lands together with bus_error=1. smbus_core.sv's
        `if (w_phy_done && w_recover_failed) r_bus_error <= 1'b1;` is
        UNCONDITIONAL every cycle (outside the master_state case), while
        M_STOP's own `r_complete <= !r_pec_error && !r_bus_error` reads
        the PRE-EDGE r_bus_error on the identical clock edge - the first
        time recovery fails, r_bus_error is still 0 when r_complete's
        RHS is evaluated, so both land as 1 on the same edge. Today:
        complete=1 AND bus_error=1, INT_STATUS=0x03, no STOP on the
        wire. Sweeps >=10 onset points for holding SDA low, bracketing
        the STOP-escalation window (M_STOP entry through the following
        few cycles, where the real SMBusSlave BFM is already idle and
        cannot fight the fault injection)."""
        self.log.info("=== GH58-R4-1: complete=1 after a failed bus recovery ===")
        core = self._core()

        async def _run_once(onset_cycles):
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.write_data_byte(0x5A)

            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()
            self.tb.smbus_monitor.recv_queue.clear()

            stop_task = cocotb.start_soon(self._watch_for_real_stop(4000))
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x01)
            for _ in range(onset_cycles):
                await RisingEdge(self.tb.pclk)
            self.tb._slave_sda_shim.value = 0   # "another device" holds SDA low

            for _ in range(4000):
                await RisingEdge(self.tb.pclk)
                if not int(core.status_busy.value):
                    break
            await ClockCycles(self.tb.pclk, 30)
            stop_seen = await stop_task.join()

            status = await self.tb.read_status()
            int_status = await self.tb.read_interrupt_status()

            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            self.tb._slave_sda_shim.value = 1
            await self._recover_and_reset()
            return stop_seen, status, int_status

        try:
            # Calibrate: cycle count (from start_transaction) at which
            # the FSM first reaches M_STOP, unperturbed.
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.write_data_byte(0x5A)
            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x01)
            stop_entry_cycle = None
            for i in range(4000):
                await RisingEdge(self.tb.pclk)
                if int(core.status_fsm_state.value) == M_STOP:
                    stop_entry_cycle = i
                    break
                if not int(core.status_busy.value):
                    break
            await ClockCycles(self.tb.pclk, 30)
            self.tb.smbus_slave.stop()
            await self._recover_and_reset()
            if stop_entry_cycle is None:
                self.log.error("GH58-R4-1: calibration never reached M_STOP")
                return False

            failures = []
            for off in range(10):
                onset = stop_entry_cycle + off
                stop_seen, status, int_status = await _run_once(onset)
                complete = status['complete']
                bus_error = status['bus_error']
                only_error = (int_status == SMBusRegisterMap.INT_ERROR_EN)
                ok = (not complete) and bus_error and (not stop_seen) and only_error
                self.log.info(
                    f"  onset=stop_entry+{off}: complete={complete}, "
                    f"bus_error={bus_error}, stop_seen={stop_seen}, "
                    f"INT_STATUS=0x{int_status:02x}, ok={ok}")
                if not ok:
                    failures.append(
                        f"stop_entry+{off}(cpl={complete},bus={bus_error},"
                        f"stop={stop_seen},int=0x{int_status:02x})")

            if not failures:
                self.log.warning("GH58-R4-1 unexpectedly GREEN")
                return True

            self.log.error(
                f"GH58-R4-1: complete=1 together with bus_error=1 after a "
                f"failed bus recovery for: {', '.join(failures)}.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R4-1 test error: {e}")
            return False

    async def test_gh58_r4_2_stale_idle_timeout(self) -> bool:
        """MED-HIGH: smbus_bit_phy.sv's stall counter (`w_scl_low =
        r_scl_drive_low || !w_scl_sync`) is not gated by r_active, so it
        runs whenever the WIRE reads SCL low even while the master is
        completely idle. (a) a foreign master (or long stretch) holding
        SCL low past SMBUS_TIMEOUT while idle, then releasing, then a
        fresh START: the stale phy_timeout level can still be sampled
        for one cycle before the new w_start_phy clears it, aborting
        before anything is framed. (b) writing start WHILE SCL (and SDA)
        are still foreign-held: the master must wait (bus-free wait),
        never pulsing SCL into someone else's in-flight transfer."""
        self.log.info("=== GH58-R4-2: stale idle-bus phy_timeout ===")
        core = self._core()

        async def _sub_a():
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=7)
            await self.tb.configure_timeout(timeout=500)
            await self.tb.write_data_byte(0x5A)

            self.tb._slave_scl_shim.value = 0   # foreign master: SCL held low
            self.tb._slave_sda_shim.value = 1
            for _ in range(1600):               # well past SMBUS_TIMEOUT=500
                await RisingEdge(self.tb.pclk)
            self.tb._slave_scl_shim.value = 1   # foreign master releases
            for _ in range(50):
                await RisingEdge(self.tb.pclk)

            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()
            self.tb.smbus_monitor.recv_queue.clear()
            stop_task = cocotb.start_soon(self._watch_for_real_stop(3000))
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x01)
            for _ in range(3000):
                await RisingEdge(self.tb.pclk)
                if (int(core.status_complete.value) or
                        int(core.status_bus_error.value) or
                        int(core.status_timeout_error.value)):
                    break
            await ClockCycles(self.tb.pclk, 30)
            stop_seen = await stop_task.join()
            status = await self.tb.read_status()
            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            await self._recover_and_reset()
            return stop_seen, status

        async def _sub_b():
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=7)
            await self.tb.configure_timeout(timeout=500)
            await self.tb.write_data_byte(0x5A)

            # Foreign master: SCL AND SDA both held low (a foreign "0"
            # data bit in flight) - nothing this core does may disturb
            # that transfer.
            self.tb._slave_scl_shim.value = 0
            self.tb._slave_sda_shim.value = 0
            for _ in range(200):
                await RisingEdge(self.tb.pclk)
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x01)

            pulses_while_foreign = 0
            prev_scl_t = int(self.tb.dut.smb_scl_t.value)
            for _ in range(1400):
                await RisingEdge(self.tb.pclk)
                cur_scl_t = int(self.tb.dut.smb_scl_t.value)
                if prev_scl_t == 0 and cur_scl_t == 1:
                    pulses_while_foreign += 1
                prev_scl_t = cur_scl_t

            self.tb._slave_scl_shim.value = 1
            self.tb._slave_sda_shim.value = 1
            for _ in range(2500):
                await RisingEdge(self.tb.pclk)
                if not int(core.status_busy.value):
                    break
            await ClockCycles(self.tb.pclk, 30)
            released = (int(self.tb.dut.smb_scl_t.value) == 1 and
                        int(self.tb.dut.smb_sda_t.value) == 1)
            await self._recover_and_reset()
            return pulses_while_foreign, released

        try:
            stop_seen_a, status_a = await _sub_a()
            self.log.info(
                f"  (a) after foreign SCL-low release: stop_seen={stop_seen_a}, "
                f"complete={status_a['complete']}, "
                f"timeout_error={status_a['timeout_error']}")
            sub_a_ok = (stop_seen_a and status_a['complete'] and
                        not status_a['timeout_error'])

            pulses_b, released_b = await _sub_b()
            self.log.info(
                f"  (b) while SCL+SDA foreign-held: pulses_while_foreign="
                f"{pulses_b} (want 0), released_after={released_b}")
            sub_b_ok = (pulses_b == 0) and released_b

            if sub_a_ok and sub_b_ok:
                self.log.warning("GH58-R4-2 unexpectedly GREEN")
                return True

            self.log.error(
                f"GH58-R4-2: stale idle-bus phy_timeout contract violated - "
                f"(a) stop_seen={stop_seen_a} (want True), complete="
                f"{status_a['complete']} (want True), timeout_error="
                f"{status_a['timeout_error']} (want False), sub_a_ok="
                f"{sub_a_ok}; (b) pulses_while_foreign={pulses_b} (want 0), "
                f"released_after={released_b}, sub_b_ok={sub_b_ok}.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R4-2 test error: {e}")
            return False

    async def test_gh58_r4_3_started_guard_stale_after_success(self) -> bool:
        """MED: r_started (smbus_core.sv) latches on the first START and
        is NEVER cleared except at reset, so the fast release-and-idle
        guard `(r_master_state==M_STOP) || (!r_started && w_sda_sync)`
        can only fire via M_STOP after any prior successful transaction.
        A stuck-SCL/SDA-free timeout that never reaches M_STOP on a
        LATER transaction now falls through to the slow abort+recover
        path even though SDA was free and nothing was ever framed.
        Measure busy duration for the identical stuck-SCL/SDA-free
        scenario before and after one clean transaction: both must be
        the fast path, about one SMBUS_TIMEOUT window."""
        self.log.info("=== GH58-R4-3: r_started guard stale after first success ===")
        core = self._core()
        TIMEOUT = 300

        async def _measure_stuck_scl_busy_cycles():
            self.tb._slave_scl_shim.value = 0    # stuck low, SDA free
            self.tb._slave_sda_shim.value = 1
            await self.tb.write_data_byte(0x5A)
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x01)
            seen_busy = False
            busy_cycles = 0
            for _ in range(10 * TIMEOUT):
                await RisingEdge(self.tb.pclk)
                b = int(core.status_busy.value)
                if b:
                    seen_busy = True
                    busy_cycles += 1
                elif seen_busy:
                    break
            self.tb._slave_scl_shim.value = 1
            self.tb._slave_sda_shim.value = 1
            return busy_cycles

        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=7)
            await self.tb.configure_timeout(timeout=TIMEOUT)
            busy_before = await _measure_stuck_scl_busy_cycles()
            await self._recover_and_reset()

            # One clean transaction, THEN the same stuck-SCL/SDA-free
            # scenario with NO reset in between - r_started must persist
            # (it is only cleared by an actual reset) for this to be a
            # meaningful test of the "after a success" case. An
            # intervening _recover_and_reset() here would clear
            # r_started right back to 0 and silently retest the SAME
            # "before" case twice (the bug this test found on its first
            # pass, before this fix).
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=7)
            await self.tb.configure_timeout(timeout=TIMEOUT)
            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            await self.tb.write_data_byte(0x5A)
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x01)
            for _ in range(3000):
                await RisingEdge(self.tb.pclk)
                if int(core.status_complete.value) or int(core.status_bus_error.value):
                    break
            await ClockCycles(self.tb.pclk, 30)
            self.tb.smbus_slave.stop()
            await self.tb.reset_fifos()

            # Same stuck-SCL/SDA-free scenario, now AFTER one success -
            # deliberately NOT preceded by _recover_and_reset().
            busy_after = await _measure_stuck_scl_busy_cycles()
            await self._recover_and_reset()

            ratio = busy_after / max(busy_before, 1)
            self.log.info(
                f"  busy_before={busy_before} cyc, busy_after={busy_after} "
                f"cyc (ratio={ratio:.2f}), TIMEOUT={TIMEOUT}")
            ok = (ratio < 2.0) and (busy_after < TIMEOUT * 3)

            if ok:
                self.log.warning("GH58-R4-3 unexpectedly GREEN")
                return True

            self.log.error(
                f"GH58-R4-3: busy duration for a stuck-SCL/SDA-free "
                f"timeout grew after a successful transaction - "
                f"busy_before={busy_before} cyc, busy_after={busy_after} "
                f"cyc (ratio={ratio:.2f}), TIMEOUT={TIMEOUT}.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R4-3 test error: {e}")
            return False

    async def test_gh58_r4_4_recovery_clock_timing(self) -> bool:
        """MED: recovery clocks must use standard-mode timing regardless
        of cfg_fast_mode (smbus_bit_phy.sv: `w_use_fast = cfg_fast_mode
        && (r_op != PHY_OP_RECOVER)`), meeting tLOW>=4.7us and
        tHIGH>=4.0us at the RDL-default CLK_DIV=249, in both fast_mode
        settings. Today tLOW=2.5us."""
        self.log.info("=== GH58-R4-4: recovery-clock tLOW/tHIGH at RDL-default CLK_DIV ===")
        core = self._core()
        CLK_DIV = 249
        T_LOW_MIN_NS = 4700
        T_HIGH_MIN_NS = 4000
        PHY_OP_RECOVER = 5

        async def _measure_recovery_low_high_ns(fast_mode):
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True, fast_mode=fast_mode)
            await self.tb.configure_clock(clk_div=CLK_DIV)
            await self.tb.configure_timeout(timeout=4000)
            await self.tb.write_data_byte(0x5A)

            self.tb._slave_sda_shim.value = 0   # stuck low -> forces recovery
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x01)
            for _ in range(60000):
                await RisingEdge(self.tb.pclk)
                if int(core.u_bit_phy.r_op.value) == PHY_OP_RECOVER:
                    break

            await RisingEdge(self.tb.dut.smb_scl_o)
            await FallingEdge(self.tb.dut.smb_scl_o)
            t_fall = cocotb.utils.get_sim_time('ns')
            await RisingEdge(self.tb.dut.smb_scl_o)
            t_rise = cocotb.utils.get_sim_time('ns')
            low_ns = t_rise - t_fall
            await FallingEdge(self.tb.dut.smb_scl_o)
            t_fall2 = cocotb.utils.get_sim_time('ns')
            high_ns = t_fall2 - t_rise

            self.tb._slave_sda_shim.value = 1
            await self._recover_and_reset()
            return low_ns, high_ns

        try:
            results = {}
            for fast in (False, True):
                low_ns, high_ns = await _measure_recovery_low_high_ns(fast)
                results[fast] = (low_ns, high_ns)
                self.log.info(
                    f"  fast_mode={fast}: recovery tLOW={low_ns}ns "
                    f"(min {T_LOW_MIN_NS}), tHIGH={high_ns}ns "
                    f"(min {T_HIGH_MIN_NS})")

            failures = []
            for fast, (low_ns, high_ns) in results.items():
                if low_ns < T_LOW_MIN_NS or high_ns < T_HIGH_MIN_NS:
                    failures.append(
                        f"fast_mode={fast}(tLOW={low_ns}ns,tHIGH={high_ns}ns)")

            if not failures:
                self.log.info(
                    "GH58-R4-4 GREEN: recovery clocks meet standard-mode "
                    "tLOW/tHIGH in both fast_mode settings")
                return True

            self.log.error(
                f"GH58-R4-4: recovery clocks do not meet standard-mode "
                f"tLOW>=4.7us/tHIGH>=4.0us at CLK_DIV={CLK_DIV} for: "
                f"{', '.join(failures)}.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R4-4 test error: {e}")
            return False

    async def test_gh58_r4_9_recovery_no_same_edge_drop(self) -> bool:
        """GUARD (expected GREEN): during bus recovery, the SCL-low and
        SDA-low drives ahead of the eventual STOP must not land on the
        same wire edge - SDA falls only after SCL has ALREADY been
        sampled low on a prior cycle, never simultaneously with SCL's
        own fall."""
        self.log.info("=== GH58-R4-9 (guard): recovery same-edge SCL/SDA drop ===")
        core = self._core()
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=500)
            await self.tb.write_data_byte(0x5A)

            self.tb._slave_sda_shim.value = 0
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_BYTE,
                                             0x50, command=0x01)

            prev_scl = int(self.tb.dut.smb_scl_i.value)
            prev_sda = int(self.tb.dut.smb_sda_i.value)
            violations = []
            for c in range(8000):
                await RisingEdge(self.tb.pclk)
                cur_scl = int(self.tb.dut.smb_scl_i.value)
                cur_sda = int(self.tb.dut.smb_sda_i.value)
                if prev_sda == 1 and cur_sda == 0 and cur_scl == 0 and prev_scl == 1:
                    violations.append(c)
                prev_scl, prev_sda = cur_scl, cur_sda
                if int(core.status_bus_error.value) or int(core.status_complete.value):
                    break

            self.tb._slave_sda_shim.value = 1
            await self._recover_and_reset()

            self.log.info(
                f"  same-edge SCL/SDA drops: {len(violations)} (want 0)"
                f"{' at cycles ' + str(violations[:5]) if violations else ''}")
            if not violations:
                self.log.info("GH58-R4-9 GREEN")
                return True

            self.log.error(
                f"GH58-R4-9: found {len(violations)} cycle(s) where SCL "
                f"and SDA both dropped on the identical wire edge during "
                f"recovery: {violations[:10]}.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R4-9 test error: {e}")
            return False

    async def test_gh58_r4_8_full_density_abort_sweep(self) -> bool:
        """GUARD (expected GREEN): extend the existing 40-point cmd_stop
        sweep (GH58-R3-2 sub-b) to EVERY cycle of one Write Word
        transaction, for both cmd_stop and soft_reset - no line may be
        driven after busy=0 at any abort-write cycle."""
        self.log.info("=== GH58-R4-8 (guard): full-density cmd_stop/soft_reset sweep ===")
        core = self._core()

        async def _run_and_check(abort_kind, at_cycle):
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.write_tx_fifo([0xAA, 0xBB])
            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()

            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_WORD,
                                             0x50, command=0x10)
            await ClockCycles(self.tb.pclk, at_cycle)
            if abort_kind == 'stop':
                await self.tb.write_register(SMBusRegisterMap.SMBUS_COMMAND,
                                              SMBusRegisterMap.COMMAND_STOP)
            else:
                _, control_before = await self.tb.read_register(
                    SMBusRegisterMap.SMBUS_CONTROL)
                await self.tb.write_register(
                    SMBusRegisterMap.SMBUS_CONTROL,
                    control_before | SMBusRegisterMap.CONTROL_SOFT_RESET)

            busy_was_1 = False
            for _ in range(1200):
                await RisingEdge(self.tb.pclk)
                b = int(core.status_busy.value)
                if b:
                    busy_was_1 = True
                if busy_was_1 and not b:
                    break
                if not busy_was_1 and not b:
                    break

            scl_t = int(self.tb.dut.smb_scl_t.value)
            sda_t = int(self.tb.dut.smb_sda_t.value)
            released = (scl_t == 1 and sda_t == 1)

            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            await self._recover_and_reset()
            return released

        try:
            # Calibrate one clean Write Word's length in pclk cycles.
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.write_tx_fifo([0xAA, 0xBB])
            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_WRITE_WORD,
                                             0x50, command=0x10)
            length = 0
            for _ in range(1200):
                await RisingEdge(self.tb.pclk)
                length += 1
                if not int(core.status_busy.value) and length > 2:
                    break
            self.tb.smbus_slave.stop()
            await self._recover_and_reset()
            self.log.info(f"  calibrated Write Word length = {length} pclk cycles")

            violations = []
            for at in range(1, length + 1):
                if not await _run_and_check('stop', at):
                    violations.append(('cmd_stop', at))
            for at in range(1, length + 1):
                if not await _run_and_check('soft_reset', at):
                    violations.append(('soft_reset', at))

            self.log.info(
                f"  swept {2 * length} points (cmd_stop + soft_reset x "
                f"{length} cycles each): {len(violations)} violation(s)")
            if not violations:
                self.log.info(
                    "GH58-R4-8 GREEN: no line driven after busy=0 at any "
                    "cycle of a full Write Word, for cmd_stop or soft_reset")
                return True

            self.log.error(
                f"GH58-R4-8: found {len(violations)} point(s) where a "
                f"line was still driven after busy=0: {violations[:10]}.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R4-8 test error: {e}")
            return False

    async def test_gh58_r4_10_tx_fifo_pstrb(self) -> bool:
        """LOW: an APB write to SMBUS_TX_FIFO with PSTRB=4'b0010 (the
        FIFO's own data byte lane, lane 0, NOT selected) must push
        nothing - tx_level must stay unchanged. Today it pushes 0x00,
        i.e. the write-triggered FIFO push ignores byte enables
        entirely. Uses the framework APB master's native PSTRB support
        (APBPacket.pstrb), not a hand-rolled driver."""
        self.log.info("=== GH58-R4-10: TX FIFO push must honor PSTRB ===")
        # APBPacket is imported at module scope. It used to be imported here
        # behind a try/except that returned TRUE when the import failed, so a
        # framework rename would have turned this test green while it drove
        # nothing at all -- a test that passes on the failure of its own
        # precondition (RLB-006). The import is unconditional now: if the
        # framework cannot provide it, the module fails to load and every
        # smbus test says so.
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.reset_fifos()
            before = await self.tb.read_fifo_status()

            write_packet = APBPacket(
                pwrite=1,
                paddr=SMBusRegisterMap.SMBUS_TX_FIFO,
                pwdata=0x000000AB,
                pstrb=0b0010,     # lane 1, not lane 0 (the FIFO data byte)
                pprot=0,
                data_width=32,
                addr_width=12,
                strb_width=4,
            )
            write_packet.direction = 'WRITE'
            await self.tb.apb4_master.send(write_packet)
            for _ in range(30):
                await RisingEdge(self.tb.pclk)

            after = await self.tb.read_fifo_status()
            await self._recover_and_reset()

            self.log.info(
                f"  tx_level before={before['tx_level']}, "
                f"after PSTRB=0b0010 write={after['tx_level']}")
            ok = after['tx_level'] == before['tx_level']

            if ok:
                self.log.info("GH58-R4-10 GREEN: byte-disabled TX_FIFO write "
                              "pushed nothing")
                return True

            self.log.error(
                f"GH58-R4-10: a write to SMBUS_TX_FIFO with PSTRB=0b0010 "
                f"(data byte lane not selected) pushed a byte anyway - "
                f"tx_level went from {before['tx_level']} to "
                f"{after['tx_level']}.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R4-10 test error: {e}")
            return False

    # ==================================================================
    # GH58-R5 batch (coordinator round 5): GH58-13 exercises soft_reset
    # (CONTROL.soft_reset), which clears FIFOs only as a side effect of
    # restarting the whole engine - it checks tx_level/rx_level==0,
    # sticky INT_STATUS cleared, and a subsequent transaction, all after
    # soft_reset, but never exercises CONTROL.fifo_reset on its own.
    # Coordinator asked for that gap to be checked explicitly.
    # ==================================================================

    async def test_rlb011_arbitration_lost(self) -> bool:
        """RLB-011: multi-master arbitration.

        Another master transmitting at the same time pulls SDA low while this
        one is sending a 1. That is arbitration lost: this master must release
        both lines at once - re-driving them would corrupt the winner's
        transfer - report SMBUS_STATUS.arb_lost, and go idle without framing
        a STOP. A later transaction must work normally."""
        self.log.info("=== RLB-011: arbitration lost ===")
        from .smbus_tb import SMBusRegisterMap as M
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True, use_pec=False)

            # Address 0x55 has 1 bits for a rival to contradict. The rival
            # must appear AFTER this master has framed its START and is
            # transmitting: holding SDA low beforehand simply parks the
            # master in its bus-free wait, which is correct behaviour and not
            # arbitration at all.
            await self.tb.start_transaction(trans_type=M.TRANS_SEND_BYTE,
                                            slave_addr=0x55, command=0)
            # wait for the first SCL low phase, i.e. the address byte is under way
            for _ in range(200000):
                await ClockCycles(self.tb.pclk, 1)
                if int(self.tb.dut.smb_scl_t.value) == 0:
                    break
            await ClockCycles(self.tb.pclk, 200)
            self.tb._slave_sda_shim.value = 0        # the other master wins
            lost = False
            for _ in range(4000):
                await ClockCycles(self.tb.pclk, 10)
                _, st = await self.tb.read_register(M.SMBUS_STATUS)
                if st & M.STATUS_ARB_LOST:
                    lost = True
                    break
            released = (int(self.tb.dut.smb_scl_t.value) == 1)
            busy_after = bool((await self.tb.read_register(M.SMBUS_STATUS))[1]
                              & M.STATUS_BUSY)
            self.tb._slave_sda_shim.value = 1        # rival finishes
            await ClockCycles(self.tb.pclk, 2000)
            self.log.info(f"  arb_lost={lost} scl_released={released} "
                          f"busy_after={busy_after}")

            # The block must still work once the bus is free.
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True, use_pec=False)
            self.tb.smbus_slave.start()
            await self.tb.start_transaction(trans_type=M.TRANS_SEND_BYTE,
                                            slave_addr=0x50, command=0)
            recovered = await self.tb.wait_for_complete(timeout_cycles=40000)
            self.tb.smbus_slave.stop()
            self.log.info(f"  transaction after arbitration loss: {recovered}")

            ok = lost and released and (not busy_after) and recovered
            if ok:
                self.log.info("RLB-011 arbitration GREEN")
                return True
            self.log.error(
                f"RLB-011 arbitration: arb_lost={lost} scl_released={released} "
                f"busy_cleared={not busy_after} later_transaction={recovered}")
            return False
        except Exception as e:
            self.log.error(f"RLB-011 arbitration test error: {e}")
            return False

    async def test_rlb011_quick_command_read(self) -> bool:
        """RLB-011: the read-direction Quick Command.

        The R/W bit IS the payload of a quick command, so both directions have
        to be reachable. Transaction type 0xA sends the address byte with
        R/W = 1 and nothing else; type 0x0 keeps the write direction."""
        self.log.info("=== RLB-011: quick command, read direction ===")
        from .smbus_tb import SMBusRegisterMap as M
        try:
            results = {}
            for name, ttype in (("write", M.TRANS_QUICK_CMD),
                                ("read", M.TRANS_QUICK_CMD_RD)):
                await self._recover_and_reset()
                await self.tb.enable_master_mode(enable=True, use_pec=False)
                self.tb.smbus_monitor.recv_queue.clear()
                self.tb.smbus_slave.start()
                self.tb.smbus_monitor.start()
                await self.tb.start_transaction(trans_type=ttype,
                                                slave_addr=0x50, command=0)
                done = await self.tb.wait_for_complete(timeout_cycles=40000)
                await ClockCycles(self.tb.pclk, 300)
                self.tb.smbus_monitor.stop()
                self.tb.smbus_slave.stop()
                pkts = list(self.tb.smbus_monitor.recv_queue)
                dirs = [getattr(p, 'read_write', None) for p in pkts]
                results[name] = (done, dirs)
                self.log.info(f"  quick {name}: completed={done} "
                              f"address directions seen={dirs}")

            write_ok = results["write"][0] and 1 not in results["write"][1]
            read_ok = results["read"][0] and 1 in results["read"][1]
            if write_ok and read_ok:
                self.log.info("RLB-011 quick command read GREEN")
                return True
            self.log.error(
                f"RLB-011 quick command: write={results['write']} (want "
                f"completed with no R/W=1), read={results['read']} (want "
                f"completed with an R/W=1 address byte)")
            return False
        except Exception as e:
            self.log.error(f"RLB-011 quick command read test error: {e}")
            return False

    async def test_gh58_r5_1_fifo_reset_clears_stale_tx_data(self) -> bool:
        """Coordinator round-5 ask: GH58-13 (soft_reset) checks FIFO
        levels, sticky status, and a subsequent transaction - but only
        via soft_reset, never CONTROL.fifo_reset alone. Stage 5 bytes,
        write SMBUS_CONTROL.fifo_reset (engine otherwise untouched),
        confirm tx_level reads 0 immediately, then confirm a following
        block write sends ONLY what is staged AFTER the reset - none of
        the 5 stale bytes."""
        self.log.info("=== GH58-R5-1: fifo_reset clears stale TX data ===")
        try:
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.reset_fifos()

            stale_data = [0x11, 0x22, 0x33, 0x44, 0x55]
            await self.tb.write_tx_fifo(stale_data)
            fifo_staged = await self.tb.read_fifo_status()
            self.log.info(f"  staged {len(stale_data)} bytes: "
                          f"tx_level={fifo_staged['tx_level']}")

            await self.tb.reset_fifos()   # writes CONTROL.fifo_reset, RMW
            fifo_after_reset = await self.tb.read_fifo_status()
            self.log.info(f"  after fifo_reset: "
                          f"tx_level={fifo_after_reset['tx_level']}")
            tx_level_cleared = fifo_after_reset['tx_level'] == 0

            fresh_data = [0xA1, 0xA2]
            await self.tb.set_block_count(len(fresh_data))
            await self.tb.write_tx_fifo(fresh_data)

            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()
            self.tb.smbus_monitor.start()
            self.tb.smbus_monitor.recv_queue.clear()

            await self.tb.start_transaction(SMBusRegisterMap.TRANS_BLOCK_WRITE,
                                             0x50, command=0x60)
            core = self._core()
            for _ in range(3000):
                await RisingEdge(self.tb.pclk)
                if int(core.status_complete.value) or int(core.status_bus_error.value):
                    break
            await ClockCycles(self.tb.pclk, 20)

            packets = list(self.tb.smbus_monitor.recv_queue)
            self.tb.smbus_slave.stop()
            self.tb.smbus_monitor.stop()
            await self._recover_and_reset()

            packet_ok = (len(packets) == 1 and packets[0].data == fresh_data)
            wire_data = packets[0].data if packets else None
            self.log.info(
                f"  post-reset block write wire data={wire_data} "
                f"(expected {fresh_data}), packet_ok={packet_ok}")

            if tx_level_cleared and packet_ok:
                self.log.info("GH58-R5-1 GREEN: fifo_reset alone clears "
                              "stale TX data and a following block write "
                              "sends only newly-staged bytes")
                return True

            self.log.error(
                f"GH58-R5-1: fifo_reset did not fully clear stale TX "
                f"data - tx_level_cleared={tx_level_cleared} (tx_level "
                f"after reset={fifo_after_reset['tx_level']}), "
                f"packet_ok={packet_ok} (wire data={wire_data}, "
                f"expected {fresh_data}).")
            return False
        except Exception as e:
            self.log.error(f"GH58-R5-1 test error: {e}")
            return False

    # ==================================================================
    # GH58-R6 batch (coordinator round 6 review): the round-5 simple_fifo
    # fix has a one-cycle shadow - r_count clears on the `clear` edge
    # but fifo_sync is held in reset one cycle longer (r_clr_hold), so
    # an RX push landing in that shadow cycle is counted but not
    # stored. No RTL edits, no ledger.
    # ==================================================================

    async def _run_r6_1_point(self, onset, push_cycle, delta, fifo_depth):
        """One sweep point for GH58-R6-1: issue CONTROL.fifo_reset
        `onset` pclk cycles after start_transaction, let the transfer
        resolve, then drain RX_FIFO and check level/empty/pop-count
        consistency."""
        core = self._core()
        await self._recover_and_reset()
        await self.tb.enable_master_mode(enable=True)
        await self.tb.configure_clock(clk_div=2)
        await self.tb.configure_timeout(timeout=200000)
        self.tb.smbus_slave.write_memory(0x60, [4, 0xD1, 0xD2, 0xD3, 0xD4])
        self.tb.smbus_slave.clock_stretch_cycles = 0
        self.tb.smbus_slave.start()

        _, control_before = await self.tb.read_register(
            SMBusRegisterMap.SMBUS_CONTROL)

        await self.tb.start_transaction(SMBusRegisterMap.TRANS_BLOCK_READ,
                                         0x50, command=0x60)
        await ClockCycles(self.tb.pclk, onset)
        await self.tb.write_register(
            SMBusRegisterMap.SMBUS_CONTROL,
            control_before | SMBusRegisterMap.CONTROL_FIFO_RESET)

        # The transfer itself must resolve - complete or abort, never
        # hang - regardless of what fifo_reset lands on.
        outcome = 'hang'
        for _ in range(3000):
            await RisingEdge(self.tb.pclk)
            if int(core.status_complete.value):
                outcome = 'complete'
                break
            if int(core.status_bus_error.value):
                outcome = 'bus_error'
                break
        await ClockCycles(self.tb.pclk, 20)

        fifo_status = await self.tb.read_fifo_status()
        level_before = fifo_status['rx_level']

        pops = 0
        for _ in range(fifo_depth + 2):
            fs = await self.tb.read_fifo_status()
            if fs['rx_level'] == 0:
                break
            await self.tb.read_register(SMBusRegisterMap.SMBUS_RX_FIFO)
            pops += 1

        fifo_after_drain = await self.tb.read_fifo_status()
        rx_level_after = fifo_after_drain['rx_level']
        rx_empty_after = fifo_after_drain['rx_empty']
        drain_reached_zero = (rx_level_after == 0)

        self.tb.smbus_slave.stop()
        await self._recover_and_reset()

        # No byte counted that was not stored: the drain must pop
        # exactly the level it saw before draining, reach rx_level==0
        # AND rx_empty==1 together, and the transfer itself must have
        # resolved cleanly.
        ok = (drain_reached_zero and rx_empty_after and
              (pops == level_before) and outcome in ('complete', 'bus_error'))

        return {
            'push_cycle': push_cycle, 'delta': delta, 'onset': onset,
            'level_before': level_before, 'pops': pops,
            'rx_level_after': rx_level_after, 'rx_empty_after': rx_empty_after,
            'drain_reached_zero': drain_reached_zero, 'outcome': outcome,
            'ok': ok,
        }

    async def test_gh58_r6_1_fifo_reset_during_receive_keeps_level_consistent(self) -> bool:
        """RED: round-6 review finding. The round-5 simple_fifo fix has
        a one-cycle shadow - r_count clears on the `clear` edge but
        fifo_sync is held in reset one cycle longer (r_clr_hold), so an
        RX push landing in that shadow cycle is COUNTED (r_count) but
        NOT STORED (fifo_sync's memory is still held in reset).
        rx_level then reads 1 with rx_empty=1 forever, and a driver
        polling rx_level hangs on the stale memory head.

        Calibrates the RX push cycles white-box (core.r_rx_fifo_wr
        rising edges) for a clean Block Read of 4 bytes, and the APB
        write-to-strobe latency for CONTROL.fifo_reset (white-box:
        dut.w_cfg_fifo_reset), then places the fifo_reset write so its
        2-cycle strobe ends exactly one cycle before each push, plus a
        few cycles either side - about 20 points total. TX via APB and
        via the engine were proved unreachable by the reviewer's own
        sweeps and soft_reset is immune, so this targets RX only."""
        self.log.info("=== GH58-R6-1: fifo_reset during receive keeps rx_level consistent ===")
        core = self._core()
        FIFO_DEPTH = 32

        async def _calibrate_push_cycles():
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            self.tb.smbus_slave.write_memory(0x60, [4, 0xD1, 0xD2, 0xD3, 0xD4])
            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()

            # Counted the SAME way the per-point sweep applies `onset`
            # below: cycles via RisingEdge(pclk) starting AFTER
            # start_transaction() has fully RETURNED (its own APB write
            # takes several cycles to complete) - a watcher started
            # concurrently with the call itself (the original version
            # of this calibration) undercounts by that many cycles and
            # silently misaligns every downstream onset, producing a
            # false GREEN that never actually lands in the shadow
            # window.
            await self.tb.start_transaction(SMBusRegisterMap.TRANS_BLOCK_READ,
                                             0x50, command=0x60)
            pushes = []
            prev = int(core.r_rx_fifo_wr.value)
            c = 0
            for _ in range(3000):
                await RisingEdge(self.tb.pclk)
                c += 1
                cur = int(core.r_rx_fifo_wr.value)
                if prev == 0 and cur == 1:
                    pushes.append(c)
                prev = cur
                if int(core.status_complete.value) or int(core.status_bus_error.value):
                    break
            await ClockCycles(self.tb.pclk, 20)
            self.tb.smbus_slave.stop()
            await self._recover_and_reset()
            return pushes

        async def _calibrate_strobe_latency():
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            samples = []

            async def _watch_strobe():
                for _ in range(40):
                    await RisingEdge(self.tb.pclk)
                    samples.append(int(self.tb.dut.w_cfg_fifo_reset.value))

            _, control_before = await self.tb.read_register(
                SMBusRegisterMap.SMBUS_CONTROL)
            watcher = cocotb.start_soon(_watch_strobe())
            await self.tb.write_register(
                SMBusRegisterMap.SMBUS_CONTROL,
                control_before | SMBusRegisterMap.CONTROL_FIFO_RESET)
            await watcher.join()
            await self._recover_and_reset()

            latency = None
            width = 0
            for i, v in enumerate(samples):
                if v and latency is None:
                    latency = i + 1
                elif latency is not None and v:
                    width += 1
                elif latency is not None and not v:
                    break
            if latency is not None:
                width += 1
            return latency, width

        try:
            pushes = await _calibrate_push_cycles()
            self.log.info(f"  calibrated rx pushes at cycles: {pushes}")
            if len(pushes) != 4:
                self.log.error(
                    f"GH58-R6-1: calibration expected 4 RX pushes for a "
                    f"4-byte Block Read, got {pushes}")
                return False

            latency, width = await _calibrate_strobe_latency()
            self.log.info(f"  calibrated fifo_reset strobe: latency="
                          f"{latency} cycles, width={width}")
            if latency is None:
                self.log.error(
                    "GH58-R6-1: calibration never saw w_cfg_fifo_reset assert")
                return False

            results = []
            for push_cycle in pushes:
                # A 2-cycle-wide strobe covering [x, x+1] should END one
                # cycle before the push (x+1 == push_cycle-1), so
                # x == push_cycle-2, and the write must be issued
                # `latency` cycles before that.
                anchor_onset = push_cycle - 2 - latency
                for delta in (-2, -1, 0, 1, 2):
                    onset = max(1, anchor_onset + delta)
                    results.append(await self._run_r6_1_point(
                        onset, push_cycle, delta, FIFO_DEPTH))

            failures = [r for r in results if not r['ok']]
            self.log.info(f"  swept {len(results)} points, "
                          f"{len(failures)} failure(s)")
            for r in failures:
                self.log.error(
                    f"  FAIL push_cycle={r['push_cycle']} delta={r['delta']} "
                    f"onset={r['onset']}: level_before_drain="
                    f"{r['level_before']}, pops={r['pops']}, "
                    f"rx_level_after={r['rx_level_after']}, "
                    f"rx_empty_after={r['rx_empty_after']}, "
                    f"drain_reached_zero={r['drain_reached_zero']}, "
                    f"outcome={r['outcome']}")

            if not failures:
                self.log.info("GH58-R6-1 GREEN: rx_level/rx_empty/pop-count "
                              "stay consistent through every swept "
                              "fifo_reset-during-receive point")
                return True

            self.log.error(
                f"GH58-R6-1: {len(failures)}/{len(results)} points leave "
                f"rx_level inconsistent with rx_empty after fifo_reset "
                f"lands in the RX-push shadow cycle - simple_fifo's "
                f"`clear` clears r_count one cycle before fifo_sync's own "
                f"reset (r_clr_hold) releases, so a push landing in that "
                f"shadow cycle is counted but not stored.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R6-1 test error: {e}")
            return False

    @staticmethod
    def _reconstruct_wire_bytes(packet):
        """SMBusMonitor._parse_transaction() classifies trans_type
        PURELY from how many bytes-after-address it saw before STOP,
        not from the actual protocol semantics - a Block Write aborted
        after only [cmd, count] or [cmd, count, data0] gets relabeled
        SEND_BYTE/WRITE_BYTE/WRITE_WORD by that length heuristic and
        `.data` is sliced accordingly (e.g. WRITE_BYTE's `.data` is
        `[data_bytes[1]]`, which for a 2-byte aborted block write is
        the COUNT byte, not a data byte - `.data=[4]` is not
        fabrication, it is the monitor correctly reporting the wire
        with the "wrong" label). This reverses that classification
        back into the raw bytes-after-address sequence so a short
        transfer can be compared against a PREFIX of the full expected
        sequence regardless of which type the monitor guessed."""
        t = packet.trans_type
        if t == SMBusTransactionType.QUICK_CMD:
            return []
        if t in (SMBusTransactionType.SEND_BYTE, SMBusTransactionType.RECV_BYTE):
            return list(packet.data)
        if t in (SMBusTransactionType.WRITE_BYTE, SMBusTransactionType.READ_BYTE,
                 SMBusTransactionType.WRITE_WORD, SMBusTransactionType.READ_WORD):
            return [packet.command] + list(packet.data)
        # BLOCK_WRITE / BLOCK_READ / BLOCK_PROC
        return [packet.command, packet.byte_count] + list(packet.data)

    async def _run_r6_2_tx_point(self, onset, pop_cycle, delta, staged_data):
        """One sweep point for GH58-R6-2 part A: issue
        CONTROL.fifo_reset `onset` pclk cycles after start_transaction,
        during a Block Write's TX byte-load phase, then confirm
        tx_level/tx_empty agree and nothing fabricated went out on the
        wire."""
        core = self._core()
        await self._recover_and_reset()
        await self.tb.enable_master_mode(enable=True)
        await self.tb.configure_clock(clk_div=2)
        await self.tb.configure_timeout(timeout=200000)
        await self.tb.reset_fifos()
        await self.tb.set_block_count(len(staged_data))
        await self.tb.write_tx_fifo(staged_data)
        self.tb.smbus_slave.clock_stretch_cycles = 0
        self.tb.smbus_slave.start()
        self.tb.smbus_monitor.start()
        self.tb.smbus_monitor.recv_queue.clear()

        _, control_before = await self.tb.read_register(
            SMBusRegisterMap.SMBUS_CONTROL)

        await self.tb.start_transaction(SMBusRegisterMap.TRANS_BLOCK_WRITE,
                                         0x50, command=0x60)
        await ClockCycles(self.tb.pclk, onset)
        await self.tb.write_register(
            SMBusRegisterMap.SMBUS_CONTROL,
            control_before | SMBusRegisterMap.CONTROL_FIFO_RESET)

        outcome = 'hang'
        for _ in range(3000):
            await RisingEdge(self.tb.pclk)
            if int(core.status_complete.value):
                outcome = 'complete'
                break
            if int(core.status_bus_error.value):
                outcome = 'bus_error'
                break
        await ClockCycles(self.tb.pclk, 20)

        fifo_status = await self.tb.read_fifo_status()
        tx_level = fifo_status['tx_level']
        tx_empty = fifo_status['tx_empty']
        levels_agree = (tx_level == 0) == tx_empty

        packets = list(self.tb.smbus_monitor.recv_queue)
        # Nothing fabricated: whatever went out (reconstructed from the
        # monitor's raw bytes-after-address, undoing its length-based
        # trans_type guess - see _reconstruct_wire_bytes) must be an
        # exact PREFIX of [command, block_count] + staged_data, in
        # order - never more bytes than could legitimately have gone
        # out, never a value that wasn't actually staged/loaded.
        command_byte = 0x60
        expected_full = [command_byte, len(staged_data)] + staged_data
        wire_data = self._reconstruct_wire_bytes(packets[0]) if packets else None
        wire_ok = (wire_data is None or
                   (len(wire_data) <= len(expected_full) and
                    wire_data == expected_full[:len(wire_data)]))

        self.tb.smbus_slave.stop()
        self.tb.smbus_monitor.stop()
        await self._recover_and_reset()

        ok = levels_agree and wire_ok and outcome in ('complete', 'bus_error')

        return {
            'pop_cycle': pop_cycle, 'delta': delta, 'onset': onset,
            'tx_level': tx_level, 'tx_empty': tx_empty,
            'levels_agree': levels_agree, 'wire_data': wire_data,
            'wire_ok': wire_ok, 'outcome': outcome, 'ok': ok,
        }

    async def _run_r6_2_width_point(self, num_writes, staged_data):
        """One point for GH58-R6-2 part B: chain `num_writes`
        consecutive CONTROL.fifo_reset writes with no gap between them
        (a single write's natural strobe is 2 pclk cycles; chaining is
        the only way to exercise a longer window from the APB side),
        landing during the TX byte-load phase, and confirm the transfer
        still resolves cleanly and tx_level/tx_empty still agree
        whatever the resulting measured width."""
        core = self._core()
        await self._recover_and_reset()
        await self.tb.enable_master_mode(enable=True)
        await self.tb.configure_clock(clk_div=2)
        await self.tb.configure_timeout(timeout=200000)
        await self.tb.reset_fifos()
        await self.tb.set_block_count(len(staged_data))
        await self.tb.write_tx_fifo(staged_data)
        self.tb.smbus_slave.clock_stretch_cycles = 0
        self.tb.smbus_slave.start()

        _, control_before = await self.tb.read_register(
            SMBusRegisterMap.SMBUS_CONTROL)

        await self.tb.start_transaction(SMBusRegisterMap.TRANS_BLOCK_WRITE,
                                         0x50, command=0x60)
        await ClockCycles(self.tb.pclk, 30)   # comfortably mid byte-load

        samples = []

        async def _watch_strobe():
            for _ in range(60):
                await RisingEdge(self.tb.pclk)
                samples.append(int(self.tb.dut.w_cfg_fifo_reset.value))

        watcher = cocotb.start_soon(_watch_strobe())
        for _ in range(num_writes):
            await self.tb.write_register(
                SMBusRegisterMap.SMBUS_CONTROL,
                control_before | SMBusRegisterMap.CONTROL_FIFO_RESET)
        await watcher.join()

        measured_width = sum(1 for v in samples if v)

        outcome = 'hang'
        for _ in range(3000):
            await RisingEdge(self.tb.pclk)
            if int(core.status_complete.value):
                outcome = 'complete'
                break
            if int(core.status_bus_error.value):
                outcome = 'bus_error'
                break
        await ClockCycles(self.tb.pclk, 20)

        fifo_status = await self.tb.read_fifo_status()
        tx_level = fifo_status['tx_level']
        tx_empty = fifo_status['tx_empty']
        levels_agree = (tx_level == 0) == tx_empty

        self.tb.smbus_slave.stop()
        await self._recover_and_reset()

        ok = levels_agree and outcome in ('complete', 'bus_error')

        return {
            'num_writes': num_writes, 'measured_width': measured_width,
            'tx_level': tx_level, 'tx_empty': tx_empty,
            'levels_agree': levels_agree, 'outcome': outcome, 'ok': ok,
        }

    async def test_gh58_r6_2_fifo_reset_tx_and_width_harmless(self) -> bool:
        """Extends GH58-R6-1 (which only swept the RX side) to the TX
        side and the mixed case, per the coordinator's round-6 ask.

        Part A: fifo_reset injected around each TX-FIFO pop cycle
        (white-box: core.w_tx_fifo_rd rising edges) during a Block
        Write's byte-load phase - the transfer must complete or abort
        with bus_error, tx_level and tx_empty must agree afterwards,
        and nothing fabricated may go out on the wire (whatever was
        sent must be an exact prefix of what was actually staged).

        Part B: chain 1, 2 and 3 consecutive CONTROL.fifo_reset writes
        (a single write's natural register-bridge strobe is 2 pclk
        cycles; chaining writes is the only way to exercise a longer
        window from the APB side) and confirm the resulting - whatever
        it measures out to - window is harmless: the transfer still
        resolves and tx_level/tx_empty still agree. Both expected
        GREEN (the round-6 fix is a single clear window gating both
        the fifo_sync enables and the level counters together, so the
        RX-specific shadow this round-6 batch closed should not have a
        TX-side or long-window analogue)."""
        self.log.info("=== GH58-R6-2: fifo_reset TX side + longer-window harmless ===")
        core = self._core()
        staged_data = [0x11, 0x22, 0x33, 0x44]

        async def _calibrate_tx_pop_cycles():
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            await self.tb.configure_clock(clk_div=2)
            await self.tb.configure_timeout(timeout=200000)
            await self.tb.reset_fifos()
            await self.tb.set_block_count(len(staged_data))
            await self.tb.write_tx_fifo(staged_data)
            self.tb.smbus_slave.clock_stretch_cycles = 0
            self.tb.smbus_slave.start()

            await self.tb.start_transaction(SMBusRegisterMap.TRANS_BLOCK_WRITE,
                                             0x50, command=0x60)
            pops = []
            prev = int(core.w_tx_fifo_rd.value)
            c = 0
            for _ in range(3000):
                await RisingEdge(self.tb.pclk)
                c += 1
                cur = int(core.w_tx_fifo_rd.value)
                if prev == 0 and cur == 1:
                    pops.append(c)
                prev = cur
                if int(core.status_complete.value) or int(core.status_bus_error.value):
                    break
            await ClockCycles(self.tb.pclk, 20)
            self.tb.smbus_slave.stop()
            await self._recover_and_reset()
            return pops

        async def _calibrate_strobe_latency():
            await self._recover_and_reset()
            await self.tb.enable_master_mode(enable=True)
            samples = []

            async def _watch_strobe():
                for _ in range(40):
                    await RisingEdge(self.tb.pclk)
                    samples.append(int(self.tb.dut.w_cfg_fifo_reset.value))

            _, control_before = await self.tb.read_register(
                SMBusRegisterMap.SMBUS_CONTROL)
            watcher = cocotb.start_soon(_watch_strobe())
            await self.tb.write_register(
                SMBusRegisterMap.SMBUS_CONTROL,
                control_before | SMBusRegisterMap.CONTROL_FIFO_RESET)
            await watcher.join()
            await self._recover_and_reset()

            latency = None
            for i, v in enumerate(samples):
                if v and latency is None:
                    latency = i + 1
                    break
            return latency

        try:
            pops = await _calibrate_tx_pop_cycles()
            self.log.info(f"  calibrated tx pops at cycles: {pops}")
            if len(pops) != len(staged_data):
                self.log.error(
                    f"GH58-R6-2: calibration expected {len(staged_data)} "
                    f"TX pops for a {len(staged_data)}-byte Block Write, "
                    f"got {pops}")
                return False

            latency = await _calibrate_strobe_latency()
            self.log.info(f"  calibrated fifo_reset strobe latency={latency}")
            if latency is None:
                self.log.error(
                    "GH58-R6-2: calibration never saw w_cfg_fifo_reset assert")
                return False

            # --- Part A: TX-pop sweep
            results_a = []
            for pop_cycle in pops:
                anchor_onset = pop_cycle - 2 - latency
                for delta in (-2, -1, 0, 1, 2):
                    onset = max(1, anchor_onset + delta)
                    results_a.append(await self._run_r6_2_tx_point(
                        onset, pop_cycle, delta, staged_data))

            failures_a = [r for r in results_a if not r['ok']]
            self.log.info(f"  Part A: swept {len(results_a)} TX points, "
                          f"{len(failures_a)} failure(s)")
            for r in failures_a:
                self.log.error(
                    f"  FAIL(A) pop_cycle={r['pop_cycle']} delta={r['delta']} "
                    f"onset={r['onset']}: tx_level={r['tx_level']}, "
                    f"tx_empty={r['tx_empty']}, "
                    f"levels_agree={r['levels_agree']}, "
                    f"wire_data={r['wire_data']}, wire_ok={r['wire_ok']}, "
                    f"outcome={r['outcome']}")

            # --- Part B: longer-window harmless
            results_b = []
            for num_writes in (1, 2, 3):
                results_b.append(await self._run_r6_2_width_point(
                    num_writes, staged_data))

            failures_b = [r for r in results_b if not r['ok']]
            for r in results_b:
                self.log.info(
                    f"  Part B: num_writes={r['num_writes']} -> measured "
                    f"width={r['measured_width']} pclk, tx_level="
                    f"{r['tx_level']}, tx_empty={r['tx_empty']}, "
                    f"levels_agree={r['levels_agree']}, "
                    f"outcome={r['outcome']}, ok={r['ok']}")

            all_failures = failures_a + failures_b
            if not all_failures:
                self.log.info(
                    "GH58-R6-2 GREEN: TX-side fifo_reset injection stays "
                    "consistent at every swept point, and longer "
                    "fifo_reset windows remain harmless")
                return True

            self.log.error(
                f"GH58-R6-2: {len(failures_a)}/{len(results_a)} TX-side "
                f"points and {len(failures_b)}/{len(results_b)} "
                f"longer-window points failed.")
            return False
        except Exception as e:
            self.log.error(f"GH58-R6-2 test error: {e}")
            return False

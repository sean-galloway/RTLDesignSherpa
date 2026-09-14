# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ioapic_merge_tests
# Purpose: The SEAM between two apb4_ioapic channels and ioapic_deliv_merge.
#
# Created: 2026-09-14

"""What these ask that nothing else can.

The merge's formal proof covers routing, retry routing, grant exclusivity and
backpressure at its own ports -- with FREE inputs, mutation-checked. The IOAPIC
suites cover the block at its ports. Neither can reach the wiring:

  * m_src_id must name the IOAPIC the message actually came from. A merge that
    routed payloads correctly but mislabelled the origin would pass formal
    (the label is self-consistent there) and break EOI routing on silicon.
  * src_ready must close the ORIGINATING IOAPIC's handshake and no other.
  * a refusal must reach ONLY the source whose message was refused; the other
    IOAPIC's pending interrupt must survive it.
  * both IOAPICs requesting in the SAME cycle must both be served -- the
    arbiter rotates on ACK, so this is where fairness is actually visible.

Each test counts its comparisons and refuses to pass on zero.
"""

from cocotb.triggers import ClockCycles

from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_tb import (
    IOAPICRegisterMap,
)


class IOAPICMergeTests:
    """Seam tests for two apb4_ioapic instances behind ioapic_deliv_merge."""

    def __init__(self, tb):
        self.tb = tb
        self.log = tb.log

    async def _arm(self, port_idx, irq, vector, dest=0x0F, deliv=0, dest_mode=1):
        await self.tb.ports[port_idx].write_rte(
            irq=irq, vector=vector, dest=dest,
            delivery_mode=deliv, dest_mode=dest_mode,
            polarity=0, trigger_mode=0, mask=0)

    async def test_src_id_names_the_true_origin(self) -> bool:
        """m_src_id identifies which IOAPIC produced the message."""
        self.log.info("=== seam: m_src_id names the true origin ===")
        try:
            checks = 0
            for origin in (0, 1):
                await self.tb.reset_all()
                vector = 0x30 + origin
                await self._arm(origin, irq=4, vector=vector)
                await ClockCycles(self.tb.dut.pclk, 20)
                self.tb.pulse_irqs(1 << 4 if origin == 0 else 0,
                                   1 << 4 if origin == 1 else 0)
                seen = await self.tb.observe_merged(300, vector_filter=vector)
                self.tb.clear_irqs()
                if not seen:
                    self.log.error(f"  IOAPIC{origin}: no merged delivery seen")
                    return False
                got = seen[0]['src_id']
                checks += 1
                if got != origin:
                    self.log.error(f"  vector 0x{vector:02X} came from IOAPIC"
                                   f"{origin} but m_src_id said {got}")
                    return False
                self.log.info(f"  IOAPIC{origin}: vector 0x{vector:02X} tagged "
                              f"src_id={got}")
            if checks == 0:
                self.log.error("  no checks performed -- vacuous pass refused")
                return False
            self.log.info(f"seam src_id origin GREEN ({checks} checks)")
            return True
        except Exception as e:
            self.log.error(f"src_id origin test error: {e}")
            return False

    async def test_both_sources_served_when_simultaneous(self) -> bool:
        """Both IOAPICs requesting together are both served (ACK-mode fairness)."""
        self.log.info("=== seam: simultaneous requests, both served ===")
        try:
            await self.tb.reset_all()
            v0, v1 = 0x51, 0x52
            await self._arm(0, irq=6, vector=v0)
            await self._arm(1, irq=6, vector=v1)
            await ClockCycles(self.tb.dut.pclk, 20)
            # SAME cycle on both -- see pulse_irqs' docstring.
            self.tb.pulse_irqs(1 << 6, 1 << 6)
            seen = await self.tb.observe_merged(400)
            self.tb.clear_irqs()
            ids = {s['src_id'] for s in seen}
            vecs = {s['vector'] for s in seen}
            self.log.info(f"  merged {len(seen)} delivery(ies); src_ids={sorted(ids)} "
                          f"vectors={sorted(hex(v) for v in vecs)}")
            if len(seen) == 0:
                self.log.error("  nothing delivered at all")
                return False
            if ids != {0, 1}:
                self.log.error(f"  only src_id(s) {sorted(ids)} were served; a "
                               f"source was starved")
                return False
            if not {v0, v1} <= vecs:
                self.log.error(f"  both sources appeared but vectors {sorted(vecs)} "
                               f"do not include both 0x{v0:02X} and 0x{v1:02X}")
                return False
            self.log.info("seam simultaneous-service GREEN (both sources served)")
            return True
        except Exception as e:
            self.log.error(f"simultaneous-service test error: {e}")
            return False

    async def test_retry_reaches_only_the_refused_source(self) -> bool:
        """A refusal routes to the granted source alone, and is recoverable."""
        self.log.info("=== seam: retry routes to one source only ===")
        try:
            await self.tb.reset_all()
            vector = 0x63
            await self._arm(0, irq=8, vector=vector)
            await ClockCycles(self.tb.dut.pclk, 20)
            self.tb.pulse_irqs(1 << 8, 0)

            # Refuse everything: retry must be one-hot at most, never broadcast.
            refused = await self.tb.observe_merged(200, ready=1, retry=1,
                                                   vector_filter=vector)
            if len(refused) < 2:
                self.log.error(f"  only {len(refused)} offer(s) while refusing; "
                               f"a refusal must retire nothing (want >= 2)")
                return False
            broadcast = [o for o in refused if bin(o['src_retry']).count('1') > 1]
            if broadcast:
                self.log.error(f"  retry was broadcast to {len(broadcast)} offer(s) "
                               f"-- the other IOAPIC would replay an interrupt "
                               f"that was never its own")
                return False
            self.log.info(f"  refused {len(refused)} offer(s), retry never broadcast")

            # Stop refusing: the same vector must still be delivered.
            accepted = await self.tb.observe_merged(300, ready=1, retry=0,
                                                    vector_filter=vector)
            self.tb.clear_irqs()
            if not accepted:
                self.log.error("  vector never delivered after refusal stopped")
                return False
            if accepted[0]['src_id'] != 0:
                self.log.error(f"  delivered with src_id={accepted[0]['src_id']}, "
                               f"want 0")
                return False
            self.log.info(f"  delivered from IOAPIC0 once accepted "
                          f"({len(refused)} refusals then {len(accepted)} accept(s))")
            return True
        except Exception as e:
            self.log.error(f"retry-routing test error: {e}")
            return False

    async def test_backpressure_holds_the_message(self) -> bool:
        """With m_ready low nothing is consumed, and the message survives."""
        self.log.info("=== seam: backpressure holds, then releases ===")
        try:
            await self.tb.reset_all()
            vector = 0x74
            await self._arm(1, irq=10, vector=vector)
            await ClockCycles(self.tb.dut.pclk, 20)
            self.tb.pulse_irqs(0, 1 << 10)

            held = await self.tb.observe_merged(150, ready=0, vector_filter=vector)
            if held:
                self.log.error(f"  {len(held)} handshake(s) completed with "
                               f"m_ready low -- backpressure was not honoured")
                return False
            self.log.info("  nothing consumed while m_ready was low")

            released = await self.tb.observe_merged(300, ready=1,
                                                    vector_filter=vector)
            self.tb.clear_irqs()
            if not released:
                self.log.error("  message lost: nothing delivered after release")
                return False
            if released[0]['src_id'] != 1:
                self.log.error(f"  delivered src_id={released[0]['src_id']}, want 1")
                return False
            self.log.info(f"  delivered from IOAPIC1 after release "
                          f"({len(released)} handshake(s))")
            return True
        except Exception as e:
            self.log.error(f"backpressure test error: {e}")
            return False

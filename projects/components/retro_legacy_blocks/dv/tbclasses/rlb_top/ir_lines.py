# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ir_lines
# Purpose: The per-IR-line verdict for the rlb_top interrupt fabric (RLB TASK-018)
#
# Created: 2026-09-29

"""Which IR lines carried an interrupt -- as a PURE function.

Extracted from `RLBTopTests._ir_lines_ok` for the same reason TASK-017 extracted
`diff_to_packets`: this is the only real logic in the check, and inside a method
that reaches through `self.tb.pic_lines.monitors` it cannot be tested without
standing up a whole simulation. Here it is checkable in plain Python, with no
cocotb import at all.

The FAIL-CLOSED cases live here too, reached with `None` for an absent probe.
They are the most important behaviour to pin: `IRQMonitorGroup` warns and SKIPS
a signal the DUT does not expose, so a missing probe must fail rather than let
the check pass while inspecting a monitor that is not there. If that branch ever
regressed to `True`, all seven rlb_top fabric tests would still report PASSED
while asserting nothing.
"""

# rlb_top masks IR2 off every other source and forces it from the slave's INT,
# so the cascade -- and only the cascade -- may appear there.
CASCADE_IR = 2


def master_expectation(expected_irqs):
    """The master 8259's expected IR set for these fabric IRQs.

    IRQ 0-7 land on the master directly. Any IRQ >= 8 goes to the SLAVE, whose
    INT drives master IR2, so the cascade bit must appear exactly when a
    slave-side source is expected -- and must NOT appear when only master-side
    sources are.
    """
    want = set(expected_irqs)
    master = {i for i in want if i < 8}
    if any(i >= 8 for i in want):
        master.add(CASCADE_IR)
    return master


def ir_lines_verdict(fabric_asserted, master_asserted, expected_irqs):
    """-> (ok, reason). `None` for either argument means that probe was absent.

    Order matches the original method exactly: fabric-absent, fabric-mismatch,
    master-absent, master-mismatch. A caller that reorders these changes which
    diagnostic a failing test prints.
    """
    want = set(expected_irqs)

    if fabric_asserted is None:
        return False, ("w_fabric_irq probe absent -- the per-IR-line check "
                       "cannot run, and passing without it would be vacuous")
    got = set(fabric_asserted)
    if got != want:
        return False, (f"fabric IR lines wrong: asserted={sorted(got)} "
                       f"expected={sorted(want)} "
                       f"(missing={sorted(want - got)} "
                       f"extra={sorted(got - want)})")

    if master_asserted is None:
        return False, ("w_master_pic_irq probe absent -- the master-side "
                       "per-IR-line check cannot run")
    want_master = master_expectation(want)
    got_master = set(master_asserted)
    if got_master != want_master:
        return False, (f"master IR lines wrong: asserted={sorted(got_master)} "
                       f"expected={sorted(want_master)} "
                       f"(missing={sorted(want_master - got_master)} "
                       f"extra={sorted(got_master - want_master)})")

    return True, None

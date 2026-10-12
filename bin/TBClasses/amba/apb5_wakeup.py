# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: apb5_wakeup
# Purpose: Directed PWAKEUP checks for the apb5_* family (IHI 0024E 3.7.2)
# Subsystem: framework
#
# Spec facts these checks encode (IHI 0024E 3.7.2, Table 3-7):
#   - PWAKEUP is a REQUESTER output; a Completer only receives it.
#   - It is recommended HIGH at least one cycle before PSEL.
#   - Once PWAKEUP and PSEL are HIGH together it must stay HIGH until PREADY.
#   - It is recommended LOW when no further transfers are required.
#   - It is meant to be routed to a clock controller, so a clock-gated
#     Completer should wake on it alone, before PSEL arrives.
"""PWAKEUP direction and clock-gate wake checks shared by apb5 tests."""

import cocotb
from cocotb.triggers import FallingEdge, RisingEdge


async def check_requester_pwakeup(dut, log, drive_command, n_cmds=12,
                                  wait_states=2, settle=12):
    """Requester side: the master drives PWAKEUP per IHI 0024E 3.7.2.

    ``drive_command(i)`` is an async callable that queues command ``i`` on
    the master's fub port. The TB plays the Completer with ``wait_states``
    PREADY-low cycles per transfer so the hold-until-PREADY rule is tested.
    """
    clk = dut.pclk
    dut.m_apb_PREADY.value = 0
    dut.m_apb_PRDATA.value = 0
    dut.m_apb_PSLVERR.value = 0
    errors = []
    stats = {'psel_rises': 0, 'early_rises': 0}

    async def completer():
        access = 0
        while True:
            await RisingEdge(clk)
            if int(dut.m_apb_PSEL.value) and int(dut.m_apb_PENABLE.value) \
                    and not int(dut.m_apb_PREADY.value):
                access += 1
            else:
                access = 0
            dut.m_apb_PREADY.value = 1 if access >= wait_states else 0

    async def watch():
        prev_psel = 0
        prev_wake = 0
        while True:
            await FallingEdge(clk)
            psel = int(dut.m_apb_PSEL.value)
            wake = int(dut.m_apb_PWAKEUP.value)
            if psel and not prev_psel:
                stats['psel_rises'] += 1
                if prev_wake:
                    stats['early_rises'] += 1
                else:
                    errors.append(f"PSEL rose without PWAKEUP high the cycle before "
                                  f"(launch {stats['psel_rises']})")
            if psel and not wake:
                errors.append("PWAKEUP low while PSEL high (must hold until PREADY)")
            prev_psel, prev_wake = psel, wake

    cocotb.start_soon(completer())
    cocotb.start_soon(watch())

    for _ in range(4):
        await RisingEdge(clk)
    await FallingEdge(clk)
    assert int(dut.m_apb_PWAKEUP.value) == 0, "PWAKEUP high with no request pending"

    for i in range(n_cmds):
        await drive_command(i)
        if i % 3 == 2:                       # some launches from a quiet bus
            for _ in range(settle):
                await RisingEdge(clk)
    for _ in range(settle * 4):
        await RisingEdge(clk)
    await FallingEdge(clk)

    assert stats['psel_rises'] > 0, "no transfers launched -- check is vacuous"
    assert not errors, f"{len(errors)} PWAKEUP violation(s); first: {errors[0]}"
    assert int(dut.m_apb_PWAKEUP.value) == 0, \
        "PWAKEUP still high with no further transfers required"
    log.info(f"PWAKEUP led PSEL on {stats['early_rises']}/{stats['psel_rises']} launches")


async def check_completer_cg_wakes_on_pwakeup(dut, log, idle_count=4,
                                              wake_budget=4, hold=16):
    """Completer side: a clock-gated slave wakes on PWAKEUP alone.

    The caller has reset the DUT with every APB input LOW. This enables
    gating, waits for the gate to close (non-vacuity), raises only PWAKEUP
    and requires the gate to open within ``wake_budget`` cycles and stay
    open while PWAKEUP is held well past the idle count, then drops PWAKEUP
    and requires the gate to close again.
    """
    clk = dut.pclk
    dut.cfg_cg_idle_count.value = idle_count
    dut.cfg_cg_enable.value = 1

    async def wait_for(cond, limit, what):
        for _ in range(limit):
            await FallingEdge(clk)
            if cond():
                return
        raise AssertionError(what)

    gating = lambda: int(dut.cg_gating.value) == 1  # noqa: E731
    await wait_for(gating, 200, "clock gate never closed while idle -- check is vacuous")

    dut.s_apb_PWAKEUP.value = 1
    await wait_for(lambda: not gating(), wake_budget,
                   f"PWAKEUP alone did not open the clock gate within {wake_budget} cycles")
    for _ in range(hold):
        await FallingEdge(clk)
        assert not gating(), "clock gated while PWAKEUP held HIGH"

    dut.s_apb_PWAKEUP.value = 0
    await wait_for(gating, 200, "gate did not close after PWAKEUP dropped")
    log.info("Clock gate opened on PWAKEUP before any PSEL, and closed after it")

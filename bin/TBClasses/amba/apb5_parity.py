# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: apb5_parity
# Purpose: Reference model of APB5 interface parity protection (IHI 0024E ch. 5)
# Subsystem: framework
#
# Spec facts this model encodes (IHI 0024E 5.3 and Table 5-1):
#   - ODD parity: payload plus check bit always hold an odd number of ones.
#   - Multi-bit check signals carry one bit per 8 payload bits; check bit [n]
#     covers payload[8n+7:8n], and a short top byte is checked over the bits
#     that exist (missing bits are LOW).
#   - Single-bit critical controls (PSEL, PENABLE, PREADY, PSLVERR, PWAKEUP)
#     have a check bit that is the inversion of the signal.
#   - PCTRLCHK covers PPROT, PWRITE and PNSE (PNSE absent here, so LOW).
#   - PSTRBCHK is a single bit over all of PSTRB.
#   - Each check signal is only required to be correct while its Check Enable
#     term is true; the term per signal is in CHECKS below.
"""APB5 parity reference model shared by the apb5_* directed parity tests."""

import random

import cocotb
from cocotb.triggers import FallingEdge, RisingEdge, Timer
from cocotb.utils import get_sim_time


def odd_bit(value):
    """One odd-parity check bit over the whole of ``value``."""
    return 0 if bin(int(value)).count('1') % 2 else 1


def odd_check(value, width):
    """Per-byte odd-parity check vector for a ``width``-bit payload."""
    value = int(value) & ((1 << width) - 1)
    chk = 0
    for n in range((width + 7) // 8):
        chk |= odd_bit((value >> (8 * n)) & 0xFF) << n
    return chk


def _v(dut, prefix, name):
    return int(getattr(dut, f"{prefix}{name}").value)


# Check enable terms of Table 5-1, as predicates over a bus sample.
def _en_reset(s):
    return s['presetn'] == 1


def _en_psel(s):
    return s['PSEL'] == 1


def _en_wr(s):
    return s['PSEL'] == 1 and s['PWRITE'] == 1


def _en_penable(s):
    return s['PSEL'] == 1 and s['PENABLE'] == 1


def _en_rsp(s):
    return _en_penable(s) and s['PREADY'] == 1


def _en_rdata(s):
    return _en_rsp(s) and s['PWRITE'] == 0


class APB5Parity:
    """Expected check values and per-cycle checking for one APB5 port.

    ``prefix`` is the DUT port prefix (``m_apb_`` / ``s_apb_``). Widths are
    the DUT parameters. Requester-driven checks are the request signals;
    completer-driven checks are the response signals.
    """

    # PWAKEUP is a Requester output (IHI 0024E 3.7.2, Table 3-7), so its
    # check travels requester to completer with the request signals.
    REQUESTER = ('PADDRCHK', 'PCTRLCHK', 'PSELCHK', 'PENABLECHK',
                 'PWDATACHK', 'PSTRBCHK', 'PAUSERCHK', 'PWUSERCHK',
                 'PWAKEUPCHK')
    COMPLETER = ('PRDATACHK', 'PREADYCHK', 'PSLVERRCHK',
                 'PRUSERCHK', 'PBUSERCHK')

    def __init__(self, dut, prefix, addr_width, data_width, prot_width=3,
                 auser_width=4, wuser_width=4, ruser_width=4, buser_width=4):
        self.dut = dut
        self.prefix = prefix
        self.aw = addr_width
        self.dw = data_width
        self.sw = data_width // 8
        self.pw = prot_width
        # name -> (enable predicate, expected-value function over a sample)
        self.checks = {
            'PADDRCHK':   (_en_psel,    lambda s: odd_check(s['PADDR'], self.aw)),
            'PCTRLCHK':   (_en_psel,    lambda s: odd_bit((s['PWRITE'] << self.pw) | s['PPROT'])),
            'PSELCHK':    (_en_reset,   lambda s: odd_bit(s['PSEL'])),
            'PENABLECHK': (_en_psel,    lambda s: odd_bit(s['PENABLE'])),
            'PWDATACHK':  (_en_wr,      lambda s: odd_check(s['PWDATA'], self.dw)),
            'PSTRBCHK':   (_en_wr,      lambda s: odd_bit(s['PSTRB'])),
            'PAUSERCHK':  (_en_psel,    lambda s: odd_check(s['PAUSER'], auser_width)),
            'PWUSERCHK':  (_en_wr,      lambda s: odd_check(s['PWUSER'], wuser_width)),
            'PRDATACHK':  (_en_rdata,   lambda s: odd_check(s['PRDATA'], self.dw)),
            'PREADYCHK':  (_en_penable, lambda s: odd_bit(s['PREADY'])),
            'PSLVERRCHK': (_en_rsp,     lambda s: odd_bit(s['PSLVERR'])),
            'PWAKEUPCHK': (_en_reset,   lambda s: odd_bit(s['PWAKEUP'])),
            'PRUSERCHK':  (_en_rdata,   lambda s: odd_check(s['PRUSER'], ruser_width)),
            'PBUSERCHK':  (_en_rsp,     lambda s: odd_check(s['PBUSER'], buser_width)),
        }

    BUS = ('PSEL', 'PENABLE', 'PADDR', 'PWRITE', 'PWDATA', 'PSTRB', 'PPROT',
           'PAUSER', 'PWUSER', 'PRDATA', 'PREADY', 'PSLVERR', 'PWAKEUP',
           'PRUSER', 'PBUSER')

    def sample(self):
        s = {name: _v(self.dut, self.prefix, name) for name in self.BUS}
        s['presetn'] = int(self.dut.presetn.value)
        return s

    def expected(self, name, s=None):
        s = self.sample() if s is None else s
        return self.checks[name][1](s)

    def mismatches(self, names, s=None):
        """Names in ``names`` whose check is enabled and wrong this cycle."""
        s = self.sample() if s is None else s
        bad = []
        for name in names:
            enable, exp = self.checks[name]
            if enable(s) and _v(self.dut, self.prefix, name) != exp(s):
                bad.append(name)
        return bad

    def drive(self, names, corrupt=None):
        """Drive correct check values for ``names``; XOR in ``corrupt`` masks."""
        corrupt = corrupt or {}
        s = self.sample()
        for name in names:
            val = self.checks[name][1](s) ^ corrupt.get(name, 0)
            getattr(self.dut, f"{self.prefix}{name}").value = val

    def start_driver(self, names, clk, settle_ns=1):
        """Background task: re-drive ``names`` shortly after every clock edge.

        The bus signals the checks cover are driven at the rising edge (by
        the TB or by the DUT's flops); recomputing ``settle_ns`` later keeps
        every check correct for the rest of the cycle. ``self.corrupt`` may
        be set to a {name: mask} dict to inject errors.
        """
        self.corrupt = {}

        async def _run():
            # Settle first: the TB may change the bus in this same timestep.
            while True:
                await Timer(settle_ns, unit='ns')
                self.drive(names, self.corrupt)
                await RisingEdge(clk)

        return cocotb.start_soon(_run())


async def _apb_xfer(dut, clk, pfx, rng, aw, dw, auw, wuw, pwrite, timeout=200):
    """One hand-driven APB5 transfer (setup + access until PREADY).

    PWAKEUP is raised one cycle ahead of PSEL and held through PREADY, as
    IHI 0024E 3.7.2 recommends/requires, then dropped.
    """
    sig = lambda n: getattr(dut, f"{pfx}{n}")  # noqa: E731
    sig('PWAKEUP').value = 1
    await RisingEdge(clk)
    sig('PSEL').value = 1
    sig('PENABLE').value = 0
    sig('PWRITE').value = pwrite
    sig('PADDR').value = rng.getrandbits(aw)
    sig('PWDATA').value = rng.getrandbits(dw)
    sig('PSTRB').value = rng.getrandbits(dw // 8)
    sig('PPROT').value = rng.getrandbits(3)
    sig('PAUSER').value = rng.getrandbits(auw)
    sig('PWUSER').value = rng.getrandbits(wuw)
    await RisingEdge(clk)
    sig('PENABLE').value = 1
    await RisingEdge(clk)
    while not int(sig('PREADY').value):
        timeout -= 1
        assert timeout > 0, "PREADY timeout"
        await RisingEdge(clk)
    sig('PSEL').value = 0
    sig('PENABLE').value = 0
    sig('PWAKEUP').value = 0
    await RisingEdge(clk)


async def run_completer_parity_test(dut, log, widths, seed):
    """Directed IHI 0024E ch. 5 test for an APB5 completer (s_apb_ port).

    The caller has reset the DUT and started a backend responder. This
    drives the requester side with spec-correct *CHK bits, checks every
    completer *CHK the DUT drives each cycle its Check Enable term holds,
    requires no error flag on clean traffic, then corrupts each requester
    *CHK in turn and requires exactly the matching flag. ``widths`` is
    (addr, data, auser, wuser, ruser, buser).
    """
    aw, dw, auw, wuw, ruw, buw = widths
    pfx = 's_apb_'
    clk = dut.pclk
    rng = random.Random(seed)
    par = APB5Parity(dut, pfx, aw, dw, auser_width=auw, wuser_width=wuw,
                     ruser_width=ruw, buser_width=buw)
    for n in ('PSEL', 'PENABLE', 'PWRITE', 'PADDR', 'PWDATA', 'PSTRB',
              'PPROT', 'PAUSER', 'PWUSER', 'PWAKEUP'):
        getattr(dut, f"{pfx}{n}").value = 0
    par.start_driver(APB5Parity.REQUESTER, clk)

    rsp_errors = []
    flag_hits = set()
    stats = {'rsp_cycles': 0}

    async def watch():
        while True:
            await FallingEdge(clk)
            bad = par.mismatches(APB5Parity.COMPLETER)
            if bad:
                rsp_errors.append((get_sim_time('ns'), bad))
            if int(getattr(dut, f"{pfx}PREADY").value):
                stats['rsp_cycles'] += 1
            if int(dut.parity_error_wdata.value):
                flag_hits.add('wdata')
            if int(dut.parity_error_ctrl.value):
                flag_hits.add('ctrl')

    cocotb.start_soon(watch())

    async def xfer(pwrite):
        await _apb_xfer(dut, clk, pfx, rng, aw, dw, auw, wuw, pwrite)
        await RisingEdge(clk)

    for i in range(40):
        await xfer(i % 2)
    assert stats['rsp_cycles'] > 0, "no PREADY cycles observed -- check is vacuous"
    assert not rsp_errors, (
        f"{len(rsp_errors)} cycle(s) with a wrong completer check bit "
        f"(odd parity, IHI 0024E 5.3); first: {rsp_errors[0]}")
    assert not flag_hits, f"error flag(s) {flag_hits} raised on clean traffic"

    injections = [
        ('PADDRCHK',   1 << (((aw + 7) // 8) - 1), 0, 'ctrl'),  # top (short) byte
        ('PADDRCHK',   1,                          1, 'ctrl'),
        ('PCTRLCHK',   1,                          0, 'ctrl'),
        ('PSELCHK',    1,                          0, 'ctrl'),
        ('PENABLECHK', 1,                          1, 'ctrl'),
        ('PAUSERCHK',  1,                          0, 'ctrl'),
        ('PWDATACHK',  1 << (dw // 8 - 1),         1, 'wdata'),  # top byte lane
        ('PSTRBCHK',   1,                          1, 'wdata'),
        ('PWUSERCHK',  1,                          1, 'wdata'),
        ('PWAKEUPCHK', 1,                          0, 'ctrl'),   # PRESETn-enabled
    ]
    for name, mask, pwrite, flag in injections:
        await RisingEdge(clk)
        flag_hits.clear()
        par.corrupt = {name: mask}
        await xfer(pwrite)
        par.corrupt = {}
        await RisingEdge(clk)
        await RisingEdge(clk)
        assert flag_hits == {flag}, (
            f"corrupting {name} (mask {mask:#x}) raised {flag_hits or 'nothing'}, "
            f"expected only parity_error_{flag}")

    # PWDATACHK is only checked while PSEL & PWRITE (Table 5-1).
    flag_hits.clear()
    par.corrupt = {'PWDATACHK': 1}
    await xfer(0)
    par.corrupt = {}
    await RisingEdge(clk)
    await RisingEdge(clk)
    assert not flag_hits, f"PWDATACHK flagged on a read: {flag_hits}"
    log.info(f"=== APB5 completer parity PASSED ({stats['rsp_cycles']} PREADY cycles) ===")

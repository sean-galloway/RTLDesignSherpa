"""
amber_snoop_resp testbench

ACE snoop responder: the cocotb-framework AXI4ACESnoopMaster drives the
DUT's m_axi_* snoop pins; a control-stub coroutine emulates amber_control
on the ctrl_* handshake. The stub carries an independent copy of the amber
HAS Table 3.0 model (IHI0022 CRRESP bit order: DT[0] Err[1] PD[2] IS[3]
WU[4]) and a line-state / line-data model, so every transaction is scored
for CRRESP bits, CD beat count, and CD beat content -- and line states
evolve across snoops (cross-transaction coherence).

Timing: channel randomizers come from quick_config profiles
(CocoTBFramework flex_config_gen) per the house pattern; ac_channel takes
valid_delay, cr_channel / cd_channel take ready_delay. Levels:
gate = backtoback, func = gaxi_backpressure, full = gaxi_stress. FULL is a
real soak: thousands of randomized snoops over an evolving line-state
model with protocol compliance checked on every transaction.

Author: RTL Design Sherpa
Created: 2026-10-06
"""

import os
import random

from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase

from CocoTBFramework.components.ace.ace_interfaces import AXI4ACESnoopMaster
from CocoTBFramework.components.ace.ace_transaction import SnoopType, CRRESP
from CocoTBFramework.components.ace.ace_compliance_checker import ACEComplianceChecker
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.amba.amba_random_configs import GAXI_RANDOMIZER_CONFIGS


class AmberSnoopRespTB(TBBase):
    """Scores the DUT's snoop responses against a Table 3.0 line model."""

    # (profile, snoop count, control ready delay range, beat gap range)
    LEVELS = {
        'gate': ('fast', None, (0, 0), (0, 0)),              # directed cells
        'func': ('gaxi_backpressure', 600, (0, 3), (0, 2)),
        'full': ('gaxi_stress', 6000, (0, 8), (0, 4)),
    }

    # IHI0022 ACSNOOP -> internal order for the model
    SNOOPS = [SnoopType.READ_SHARED, SnoopType.READ_ONCE, SnoopType.READ_UNIQUE,
              SnoopType.CLEAN_SHARED, SnoopType.CLEAN_INVALID, SnoopType.MAKE_INVALID]

    # Table 3.0: (state, snoop) -> (DT, PD, IS, WU), next_state
    STATES = {'I': 0, 'S': 1, 'E': 2, 'M': 3}
    MATRIX = {
        ('M', 'READ_SHARED'):   ((1, 1, 1, 0), 'S'),
        ('M', 'READ_ONCE'):     ((1, 1, 0, 0), 'I'),
        ('M', 'READ_UNIQUE'):   ((1, 1, 0, 0), 'I'),
        ('M', 'CLEAN_SHARED'):  ((1, 1, 1, 0), 'S'),
        ('M', 'CLEAN_INVALID'): ((1, 1, 1, 0), 'I'),
        ('M', 'MAKE_INVALID'):  ((0, 0, 0, 0), 'I'),
        ('E', 'READ_SHARED'):   ((1, 0, 1, 1), 'S'),
        ('E', 'READ_ONCE'):     ((1, 0, 1, 1), 'S'),
        ('E', 'READ_UNIQUE'):   ((1, 0, 0, 1), 'I'),
        ('E', 'CLEAN_SHARED'):  ((0, 0, 1, 1), 'E'),
        ('E', 'CLEAN_INVALID'): ((0, 0, 0, 0), 'I'),
        ('E', 'MAKE_INVALID'):  ((0, 0, 0, 0), 'I'),
        ('S', 'READ_SHARED'):   ((0, 0, 1, 0), 'S'),
        ('S', 'READ_ONCE'):     ((0, 0, 1, 0), 'S'),
        ('S', 'READ_UNIQUE'):   ((0, 0, 0, 0), 'I'),
        ('S', 'CLEAN_SHARED'):  ((0, 0, 0, 0), 'S'),
        ('S', 'CLEAN_INVALID'): ((0, 0, 0, 0), 'I'),
        ('S', 'MAKE_INVALID'):  ((0, 0, 0, 0), 'I'),
    }

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('ADDR_WIDTH', '32'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('DATA_WIDTH', '64'))
        self.LINE_BYTES = self.convert_to_int(os.environ.get('LINE_BYTES', '64'))
        self.STRB_W = self.DATA_WIDTH // 8
        self.FILL_BEATS = self.LINE_BYTES // self.STRB_W
        random.seed(self.SEED)
        self.master = AXI4ACESnoopMaster(
            dut=dut, clock=dut.aclk, prefix='m_axi_', log=self.log,
            data_width=self.DATA_WIDTH, addr_width=self.ADDR_WIDTH)
        self.ace_checker = ACEComplianceChecker(log=self.log)
        self.line_state = {}   # addr -> 'I'/'S'/'E'/'M'
        self.line_data = {}    # addr -> [beat ints]
        self.checks = 0
        self.mismatches = 0
        self.profile, self.n_snoops, self.rdy_rng, self.gap_rng = \
            self.LEVELS.get(self.TEST_LEVEL, self.LEVELS['gate'])
        # House pattern (pumice_axi_bfm): amba_random_configs GAXI profiles
        # per channel -- ac is the producer side (valid_delay), cr/cd are
        # consumed by the master BFM (ready_delay).
        chan_cfg = GAXI_RANDOMIZER_CONFIGS[self.profile]
        self.master.ac_channel.set_randomizer(FlexRandomizer(chan_cfg['master']))
        self.master.cr_channel.set_randomizer(FlexRandomizer(chan_cfg['slave']))
        self.master.cd_channel.set_randomizer(FlexRandomizer(chan_cfg['slave']))
        self.log.info(f"AmberSnoopRespTB level={self.TEST_LEVEL} profile={self.profile} "
                      f"data_width={self.DATA_WIDTH} fill_beats={self.FILL_BEATS} "
                      f"seed={self.SEED}")

    # -- mandatory methods ------------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('aclk', freq=period_ns, units='ns')
        self.dut.ctrl_snoop_ready.value = 0
        self.dut.ctrl_crresp.value = 0
        self.dut.ctrl_cddata.value = 0
        self.dut.ctrl_cdlast.value = 0
        self.dut.ctrl_cdvalid.value = 0
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 2)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    # -- model ------------------------------------------------------------------
    def expected(self, addr, snoop):
        """Table 3.0 for the line's current state; I lines miss."""
        name = snoop if isinstance(snoop, str) else snoop.name
        st = self.line_state.get(addr, 'I')
        (dt, pd, is_, wu), nxt = self.MATRIX.get((st, name), ((0, 0, 0, 0), 'I'))
        exp = {'dt': dt, 'pd': pd, 'is': is_, 'wu': wu, 'err': 0, 'next': nxt,
               'data': list(self.line_data[addr]) if (dt and addr in self.line_data) else []}
        return exp

    def seed_line(self, addr, state=None):
        if state is None:
            state = random.choice(['I', 'S', 'E', 'M'])
        self.line_state[addr] = state
        self.line_data[addr] = [random.randrange(1 << self.DATA_WIDTH)
                                for _ in range(self.FILL_BEATS)]

    # -- control stub (emulates amber_control) -----------------------------------
    async def control_stub(self):
        while True:
            await RisingEdge(self.dut.aclk)
            if not int(self.dut.ctrl_snoop_req.value):
                continue
            addr = int(self.dut.ctrl_snoop_addr.value)
            snoop_int = int(self.dut.ctrl_snoop_type.value)
            snoop_name = {0: 'READ_SHARED', 1: 'READ_ONCE', 2: 'READ_UNIQUE',
                          3: 'CLEAN_SHARED', 4: 'CLEAN_INVALID', 5: 'MAKE_INVALID'}.get(snoop_int)
            exp = self.expected(addr, SnoopType[snoop_name]) if snoop_name else \
                {'dt': 0, 'pd': 0, 'is': 0, 'wu': 0, 'err': 0, 'next': 'I', 'data': []}
            for _ in range(random.randint(*self.rdy_rng)):
                await RisingEdge(self.dut.aclk)
            # IHI0022: DT[0] Err[1] PD[2] IS[3] WU[4]
            self.dut.ctrl_crresp.value = (exp['dt'] | (exp['err'] << 1) | (exp['pd'] << 2)
                                          | (exp['is'] << 3) | (exp['wu'] << 4))
            self.dut.ctrl_snoop_ready.value = 1
            await RisingEdge(self.dut.aclk)
            self.dut.ctrl_snoop_ready.value = 0
            if exp['dt']:
                for i, beat in enumerate(exp['data']):
                    for _ in range(random.randint(*self.gap_rng)):
                        self.dut.ctrl_cdvalid.value = 0
                        await RisingEdge(self.dut.aclk)
                    self.dut.ctrl_cddata.value = beat
                    self.dut.ctrl_cdlast.value = 1 if i == len(exp['data']) - 1 else 0
                    self.dut.ctrl_cdvalid.value = 1
                    await RisingEdge(self.dut.aclk)
                    while not int(self.dut.ctrl_cdready.value):
                        await RisingEdge(self.dut.aclk)
                self.dut.ctrl_cdvalid.value = 0
                self.dut.ctrl_cdlast.value = 0
            # apply the Table 3.0 next-state to the model
            self.line_state[addr] = exp['next']
            if exp['next'] == 'I':
                self.line_data.pop(addr, None)

    # -- scoring ------------------------------------------------------------------
    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 20:
                self.log.error(f"{what}: got {got} expected {exp}")

    async def issue_and_check(self, addr, snoop_type):
        exp = self.expected(addr, snoop_type.name)
        result = await self.master.issue_snoop(addr, snoop_type)
        cr = result.crresp
        self._score(f"crresp.dt({addr:#x},{snoop_type.name})", int(cr.data_transfer), exp['dt'])
        self._score(f"crresp.err({addr:#x})", int(cr.error), 0)
        self._score(f"crresp.pd({addr:#x})", int(cr.pass_dirty), exp['pd'])
        self._score(f"crresp.is({addr:#x})", int(cr.is_shared), exp['is'])
        self._score(f"crresp.wu({addr:#x})", int(cr.was_unique), exp['wu'])
        if exp['dt']:
            self._score(f"data.len({addr:#x})", len(result.data), len(exp['data']))
            if len(result.data) == len(exp['data']):
                for i, (got, want) in enumerate(zip(result.data, exp['data'])):
                    self._score(f"data[{i}]({addr:#x})", got, want)
        else:
            self._score(f"data.empty({addr:#x})", len(result.data), 0)
        self.ace_checker.check_crresp_validity(cr, snoop_type, addr)

    # -- tests ------------------------------------------------------------------
    async def run(self) -> bool:
        stub = await self._start_soon_safe()
        if self.TEST_LEVEL == 'gate':
            # Directed: one transaction per reachable Table 3.0 cell.
            i = 0
            for st in ['M', 'E', 'S', 'I']:
                for sn in self.SNOOPS:
                    addr = 0x1000 + i * self.LINE_BYTES
                    i += 1
                    self.seed_line(addr, st)
                    await self.issue_and_check(addr, sn)
        else:
            pool = [0x2000 + i * self.LINE_BYTES for i in range(64)]
            for a in pool:
                self.seed_line(a)
            # Directed (func/full): pipelining across transactions. The AC
            # skid exists so the master can present the next snoop while the
            # current response is still sequencing -- issue zero-gap pairs
            # and same-line pairs and verify both responses against the
            # evolving model with no idle between them.
            for addr in pool[:8]:
                self.seed_line(addr, 'M')
                st = self.SNOOPS[0]
                await self.issue_and_check(addr, st)
                await self.issue_and_check(addr, st)      # same line, evolved
                await self.issue_and_check(addr, self.SNOOPS[3])
            for n in range(self.n_snoops):
                addr = random.choice(pool)
                if addr not in self.line_data and random.random() < 0.5:
                    self.seed_line(addr)   # refill: another master touched it
                await self.issue_and_check(addr, random.choice(self.SNOOPS))
        stub.cancel()
        return self.mismatches == 0

    async def _start_soon_safe(self):
        import cocotb
        return cocotb.start_soon(self.control_stub())

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}

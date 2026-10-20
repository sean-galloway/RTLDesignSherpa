# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: alu_infer_tb
# Purpose: Testbench class for the ALU-INFER bf16 inference ALU
# Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
# Subsystem: alu-infer
#
# Author: sean galloway
# Created: 2026-10-17
# Updated: 2026-10-20 -- converted to the RDS-DV methodology: both valid/ready
#          interfaces are owned by CocoTBFramework GAXI BFMs (master on issue,
#          slave on result, passive monitors on both), stimulus and checking
#          live in this TB class, and the runner in dv/tests is a thin
#          TEST_TYPE dispatcher (the stream-area standard).

"""ALU-INFER testbench.

Interface ownership (no test code drives or samples a handshake directly):

  issue side  -- ``valid``/``ready`` + op_line_a/op_line_b/threshold_imm/
                 func_sel/acc_ctrl -- driven by a GAXIMaster (prefix ``''``,
                 multi-signal fields).
  result side -- ``result_valid``/``result_ready`` + result_line/result_flags
                 -- received by a GAXISlave (prefix ``'result'``).

A passive GAXIMonitor rides each interface and logs every completed transfer
with an ns timestamp (completed-packet tracking), which is what the latency
and ordering checks anchor on.  Deterministic timing tests steer the slave's
ready with ``set_ready_policy('always'/'stall')``; the functional soak can
run under a randomized GAXI timing profile (``GAXI_TIMING_PROFILE`` env, the
``GAXI_RANDOMIZER_CONFIGS`` table the whole repo shares).

All golden models (BF16 RNE references with the library's proven FTZ and
1-ULP contracts) live here as module-level functions; the test_* methods
carry one scenario each, dispatched by the runner via TEST_TYPE.
"""

import os
import random

import cocotb
from cocotb.triggers import RisingEdge, ReadOnly
from cocotb.utils import get_sim_time

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_repo_root
from CocoTBFramework.components.gaxi.gaxi_factories import (
    create_gaxi_master, create_gaxi_slave, create_gaxi_monitor,
)
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.amba.amba_random_configs import GAXI_RANDOMIZER_CONFIGS
from TBClasses.common.bf16_testing import (
    BF16Utils, BF16_SPECIAL_GRID,
)

from .alu_infer_ext_tests import AluInferExtTests
from .alu_infer_golden import (
    FMT_BF16, FMT_INT8, FMT_FP32, FMT_FP8, CVT_ILLEGAL, ACT_OPS, BF16_ONLY_OPS,
    OP_REDUCE, OP_PWL, OP_PWL_LUT, OP_CVT, OP_ALTFMT, OP_LEAKY, OP_RECIP,
)

# ----------------------------------------------------------------------------
# Golden model -- BF16 references matching the rtl/math library contracts
# (moved here unchanged from the pre-BFM suite; see bf16_testing.py for the
# proven adder/multiplier tolerance contracts these mirror).
# ----------------------------------------------------------------------------


def pack_bf16_line(lane0: int, lane1: int) -> int:
    return ((lane1 & 0xFFFF) << 16) | (lane0 & 0xFFFF)


def unpack_bf16_line(line: int):
    return line & 0xFFFF, (line >> 16) & 0xFFFF


def is_subnormal_bf16(x: int) -> bool:
    exp = (x >> 7) & 0xFF
    mant = x & 0x7F
    return (exp == 0) and (mant != 0)


def ftz_bf16(x: int) -> int:
    """Flush a BF16 subnormal to signed zero; leave other values unchanged."""
    if is_subnormal_bf16(x):
        return x & 0x8000
    return x


def func_sel_word(opcode: int, sub_op: int = 0, reserved: int = 0) -> int:
    return (reserved << 7) | (sub_op << 5) | opcode


def bf16_to_float(x: int) -> float:
    return BF16Utils.bf16_to_float(x)


def float_to_bf16(x: float) -> int:
    return BF16Utils.float_to_bf16_rne(x)


def expected_add(a: int, b: int) -> int:
    a = ftz_bf16(a)
    b = ftz_bf16(b)
    return ftz_bf16(float_to_bf16(bf16_to_float(a) + bf16_to_float(b)))


def expected_sub(a: int, b: int) -> int:
    a = ftz_bf16(a)
    b = ftz_bf16(b)
    return ftz_bf16(float_to_bf16(bf16_to_float(a) - bf16_to_float(b)))


def expected_mul(a: int, b: int) -> int:
    a = ftz_bf16(a)
    b = ftz_bf16(b)
    return ftz_bf16(float_to_bf16(bf16_to_float(a) * bf16_to_float(b)))


def expected_min(a: int, b: int) -> int:
    fa, fb = bf16_to_float(a), bf16_to_float(b)
    # Match math_bf16_min NaN propagation: NaN returns the non-NaN operand.
    if BF16Utils.bf16_is_nan(a) and BF16Utils.bf16_is_nan(b):
        return a
    if BF16Utils.bf16_is_nan(a):
        return b
    if BF16Utils.bf16_is_nan(b):
        return a
    # Signed zeros: min returns -0 iff at least one operand is -0.
    if fa == 0.0 and fb == 0.0:
        return 0x8000 if ((a & 0x8000) | (b & 0x8000)) else 0x0000
    return float_to_bf16(min(fa, fb))


def expected_max(a: int, b: int) -> int:
    fa, fb = bf16_to_float(a), bf16_to_float(b)
    if BF16Utils.bf16_is_nan(a) and BF16Utils.bf16_is_nan(b):
        return a
    if BF16Utils.bf16_is_nan(a):
        return b
    if BF16Utils.bf16_is_nan(b):
        return a
    # Signed zeros: max returns -0 only when both operands are -0.
    if fa == 0.0 and fb == 0.0:
        return 0x8000 if ((a & 0x8000) & (b & 0x8000)) else 0x0000
    return float_to_bf16(max(fa, fb))


def expected_relu(a: int) -> int:
    if BF16Utils.bf16_is_nan(a):
        return a
    if a & 0x8000:
        return 0x0000
    return a


def fp32_fma(a_bf16: int, b_bf16: int, c_fp32: int) -> int:
    """Return FP32 accumulator update, matching the math_bf16_fma library contract.

    The product of two BF16 values is exact in doubles.  Per the library
    (math_bf16_fma.sv), a product whose unbiased exponent is below the FP32
    minimum-normal range (|product| < 2^-126, w_prod_exp_adj < 1) is flushed
    to zero BEFORE the addend is applied, and an underflowed-product result
    returns the addend verbatim (w_prod_is_zero -> ow_result = i_c).  IEEE
    fused rounding would instead keep the product sign on the rounded zero;
    the ALU inherits the library's contract (the same proven-contract
    discipline as the adder/multiplier 1-ULP tolerance).  Otherwise the only
    rounding is the FP32 add.  Result is returned as FP32 bits.
    """
    prod = bf16_to_float(a_bf16) * bf16_to_float(b_bf16)
    acc = BF16Utils.fp32_to_float(c_fp32)
    if prod != 0.0 and abs(prod) < 2.0**-126:
        # Library FTZ on the product: result is the addend verbatim.
        return c_fp32
    sum_val = prod + acc
    # Clamp finite overflow to infinity so struct.pack never raises.
    if sum_val > 3.4028234e38:
        sum_val = float('inf')
    elif sum_val < -3.4028234e38:
        sum_val = float('-inf')
    return BF16Utils.float_to_fp32(sum_val)


def bf16_from_fp32(fp32: int) -> int:
    return float_to_bf16(BF16Utils.fp32_to_float(fp32))


def bf16_is_nan(x: int) -> bool:
    return BF16Utils.bf16_is_nan(x)


def bf16_is_zero(x: int) -> bool:
    return BF16Utils.bf16_is_zero(x)


def bf16_is_inf(x: int) -> bool:
    return BF16Utils.bf16_is_inf(x)


def bf16_ulp_diff(a: int, b: int) -> int:
    """Absolute ULP difference ignoring sign/payload; safe for NaN/special."""
    return abs((a & 0x7FFF) - (b & 0x7FFF))


def bf16_addsub_match(got: int, exp: int, a: int, b: int) -> bool:
    """Match add/sub result to golden, matching BF16AdderTB contract.

    Exact match for NaN/special/zero/inf and for normal values.  Up to 1 ULP
    is tolerated only when |exp_a - exp_b| > 3 AND signs match, reflecting
    the library adder's 11-bit alignment precision limit (loses the tie-break
    bit for large exponent differences).  This is the same contract proven in
    bin/TBClasses/common/bf16_testing.py::BF16AdderTB.test_single_add.
    """
    if bf16_is_nan(got) and bf16_is_nan(exp):
        return True
    if got == exp:
        return True
    got_special = bf16_is_zero(got) or bf16_is_inf(got)
    exp_special = bf16_is_zero(exp) or bf16_is_inf(exp)
    if got_special or exp_special:
        return False
    exp_a = (a >> 7) & 0xFF
    exp_b = (b >> 7) & 0xFF
    if abs(exp_a - exp_b) <= 3:
        return False
    sign_match = (got >> 15) == (exp >> 15)
    return sign_match and bf16_ulp_diff(got, exp) <= 1


def bf16_mul_match(got: int, exp: int) -> bool:
    """Match mul result to golden, matching BF16MultiplierTB contract.

    Exact match for NaN/special/zero/inf.  Up to 1 ULP is tolerated for normal
    values when signs match.  This mirrors
    bin/TBClasses/common/bf16_testing.py::BF16MultiplierTB.test_single_mult.
    """
    if bf16_is_nan(got) and bf16_is_nan(exp):
        return True
    if got == exp:
        return True
    got_special = bf16_is_zero(got) or bf16_is_inf(got)
    exp_special = bf16_is_zero(exp) or bf16_is_inf(exp)
    if got_special or exp_special:
        return False
    sign_match = (got >> 15) == (exp >> 15)
    return sign_match and bf16_ulp_diff(got, exp) <= 1


# ----------------------------------------------------------------------------
# Opcodes (alu-infer PRD §3)
# ----------------------------------------------------------------------------
OP_COPY = 0
OP_ADD = 1
OP_SUB = 2
OP_MUL = 3
OP_MAC = 4
OP_MINMAX = 5
OP_CMP = 6
OP_RELU = 7


class AluInferTB(AluInferExtTests, TBBase):
    """Testbench for alu_infer_top: GAXI BFMs on both valid/ready interfaces."""

    # Per-level stimulus depths (TEST_LEVEL env, set per cell by the runner).
    SEEDS = {'gate': [0xA1], 'func': [0, 1, 2, 3, 4, 5, 6, 7],
             'full': [0, 1, 2, 3, 4, 5, 6, 7]}
    SOAK_COUNT = {'gate': 32, 'func': 256, 'full': 256}
    GRID_PAIRS_GATE = [(0, 0), (0, 1), (1, 4), (4, 4), (7, 8),
                       (2, 3), (5, 6), (0, 7), (8, 8)]

    def __init__(self, dut):
        super().__init__(dut)
        self.dut = dut
        self.line_w = int(dut.LINE_W.value)
        self.pipe_depth = int(dut.PIPE_DEPTH.value)
        self.adder_latency = self._param('ADDER_LATENCY', 3)
        self.mul_latency = self._param('MUL_LATENCY', 0)
        self.mac_latency = self._param('MAC_LATENCY', 0)
        self.en = {k: self._param(k, 1) for k in
                   ('EN_INT8', 'EN_FP32', 'EN_FP8', 'EN_REDUCE', 'EN_PWL', 'EN_ACT', 'EN_CVT')}
        self.err_pulses = 0
        self.level = os.environ.get('TEST_LEVEL', 'gate').lower()

        self.cycle = 0
        self._recv_cursor = 0

        self.issue_master = None
        self.result_slave = None
        self.mon_issue = None
        self.mon_result = None

    def _param(self, name, default):
        """A DUT parameter, or the RTL default when the simulator hides it."""
        try:
            return int(getattr(self.dut, name).value)
        except Exception:
            return default

    # ------------------------------------------------------------------
    # Setup
    # ------------------------------------------------------------------

    async def setup_clocks_and_reset(self):
        """Standard clock/reset, then BFM creation (stream-area pattern)."""
        # Park the handshake inputs during reset; the BFMs take ownership at
        # creation time below.
        self.dut.valid.value = 0
        self.dut.result_ready.value = 0
        await self.start_clock('clk', freq=10, units='ns')
        self.dut.aresetn.value = 0
        await self.wait_clocks('clk', 10)
        self.dut.aresetn.value = 1
        await self.wait_clocks('clk', 5)
        self._create_bfms()
        cocotb.start_soon(self._count_cycles())
        cocotb.start_soon(self._count_err_pulses())

    async def _count_cycles(self):
        while True:
            await RisingEdge(self.dut.clk)
            self.cycle += 1

    def _create_bfms(self):
        """GAXI BFMs for both valid/ready interfaces, plus passive monitors.

        Issue side: DUT signals are unprefixed (``valid``, ``ready``,
        ``op_line_a`` ...) -> master prefix ``''``.  Result side: DUT signals
        are ``result_valid``, ``result_ready``, ``result_line``,
        ``result_flags`` -> slave prefix ``'result'`` with fields named
        ``line``/``flags``.
        """
        fc_issue = FieldConfig()
        fc_issue.add_field(FieldDefinition(name='op_line_a', bits=self.line_w,
                                           format='hex', description='operand A lines'))
        fc_issue.add_field(FieldDefinition(name='op_line_b', bits=self.line_w,
                                           format='hex', description='operand B lines'))
        fc_issue.add_field(FieldDefinition(name='threshold_imm', bits=16,
                                           format='hex', description='compare immediate'))
        fc_issue.add_field(FieldDefinition(name='func_sel', bits=9,
                                           format='hex', description='opcode + sub-op'))
        fc_issue.add_field(FieldDefinition(name='acc_ctrl', bits=2,
                                           format='dec', description='MAC accumulator control'))

        fc_result = FieldConfig()
        fc_result.add_field(FieldDefinition(name='line', bits=self.line_w,
                                            format='hex', description='result lines'))
        fc_result.add_field(FieldDefinition(name='flags', bits=self.line_w,
                                            format='hex', description='result flags'))

        self.issue_master = create_gaxi_master(
            dut=self.dut, title='issue', prefix='', clock=self.dut.clk,
            field_config=fc_issue, multi_sig=True, log=self.log)
        self.result_slave = create_gaxi_slave(
            dut=self.dut, title='result', prefix='result', clock=self.dut.clk,
            field_config=fc_result, multi_sig=True, log=self.log)
        self.mon_issue = create_gaxi_monitor(
            dut=self.dut, title='mon_issue', prefix='', clock=self.dut.clk,
            field_config=fc_issue, multi_sig=True, log=self.log)
        self.mon_result = create_gaxi_monitor(
            dut=self.dut, title='mon_result', prefix='result', clock=self.dut.clk,
            field_config=fc_result, multi_sig=True, log=self.log)
        self.mon_issue.enable_completed_packet_tracking()
        self.mon_result.enable_completed_packet_tracking()

        # Default consumer: always ready.  Timing tests override with
        # set_ready_policy('stall') / FlexRandomizer sequences.
        self.result_slave.set_ready_policy('always')
        self.set_gaxi_timing_profile(os.environ.get('GAXI_TIMING_PROFILE', 'backtoback'))

    def set_gaxi_timing_profile(self, profile_name='backtoback'):
        """Apply a GAXI timing profile: master valid_delay + slave ready_delay."""
        if profile_name == 'mixed':
            profile_name = 'gaxi_realistic'
        if profile_name not in GAXI_RANDOMIZER_CONFIGS:
            self.log.warning(f"Unknown GAXI timing profile '{profile_name}', using 'backtoback'")
            profile_name = 'backtoback'
        cfg = GAXI_RANDOMIZER_CONFIGS[profile_name]
        self.issue_master.randomizer = FlexRandomizer(cfg['master'])
        self.result_slave.randomizer = FlexRandomizer(cfg['slave'])
        self.log.info(f"GAXI timing profile: {profile_name}")

    def set_issue_delay_seq(self, seq):
        """Deterministic valid_delay sequence on the issue master (cycle-exact)."""
        self.issue_master.randomizer = FlexRandomizer({'valid_delay': list(seq)})

    def set_result_ready_seq(self, seq):
        """Deterministic ready_delay sequence on the result slave (cycle-exact)."""
        self.result_slave.randomizer = FlexRandomizer({'ready_delay': list(seq)})

    def stall_results(self):
        """Consumer stall: result_ready falls immediately."""
        self.result_slave.set_ready_policy('stall')

    def drain_results(self):
        """Consumer ready: result_ready rises (within a cycle)."""
        self.result_slave.set_ready_policy('always')

    # ------------------------------------------------------------------
    # BFM-level transactions
    # ------------------------------------------------------------------

    CLK_NS = 10   # setup_clocks_and_reset starts a 10 ns clock

    def _make_packet(self, opcode, a=0, b=0, imm=0, sub_op=0, acc_ctrl=0, fmt=0):
        """Build one invocation packet for the issue master."""
        return self.issue_master.create_packet(
            op_line_a=a, op_line_b=b, threshold_imm=imm,
            func_sel=func_sel_word(opcode, sub_op, fmt), acc_ctrl=acc_ctrl)

    async def issue(self, opcode, a=0, b=0, imm=0, sub_op=0, acc_ctrl=0, fmt=0):
        """Send one invocation; returns the packet (end_time = issue edge)."""
        pkt = self._make_packet(opcode, a=a, b=b, imm=imm, sub_op=sub_op,
                                acc_ctrl=acc_ctrl, fmt=fmt)
        await self.issue_master.send(pkt)
        return pkt

    async def issue_burst(self, pkts):
        """Stream queued invocations back-to-back (zero-bubble where ready).

        send() drains the pipeline per call and can never stream; queuing the
        whole burst first keeps valid asserted across beats (framework doc).
        Returns the packet list; each packet's end_time is its issue edge.
        """
        await self.issue_master.send_burst(pkts)
        return pkts

    async def recv_packet(self, timeout_cycles=128):
        """Next retired result packet from the result slave."""
        start = self.cycle
        while len(self.result_slave.get_observed_packets()) <= self._recv_cursor:
            await RisingEdge(self.dut.clk)
            if self.cycle - start > timeout_cycles:
                raise AssertionError("Timeout waiting for result")
        pkt = self.result_slave.get_observed_packets()[self._recv_cursor]
        self._recv_cursor += 1
        return pkt

    async def recv_result(self, timeout_cycles=128):
        """Next retired result as (line, flags)."""
        pkt = await self.recv_packet(timeout_cycles)
        return int(pkt.line), int(pkt.flags)

    async def recv_packets(self, n, timeout_cycles=256):
        """Drain n retired result packets, in retirement (issue) order."""
        return [await self.recv_packet(timeout_cycles) for _ in range(n)]

    async def recv_results(self, n, timeout_cycles=256):
        """Drain n retired results as a [(line, flags)] list, in order."""
        pkts = await self.recv_packets(n, timeout_cycles)
        return [(int(p.line), int(p.flags)) for p in pkts]

    # ------------------------------------------------------------------
    # Passive sampling helpers (ReadOnly-phase protocol observation only --
    # the assertions the BFMs cannot express, e.g. "offered but stalled").
    # ------------------------------------------------------------------

    def _result_offered(self):
        return int(self.dut.result_valid.value) == 1

    def _issue_ready(self):
        return int(self.dut.ready.value) == 1

    async def _watch_first_offer(self, timeout_cycles=64):
        """Passively record (time_ns, result_line) of the first offered result.

        Polls in the ReadOnly phase; while waiting, asserts the issue side
        stays ready (the tag FIFO has room -- the elastic property).  Used by
        the tag-join test, where the consumer is stalled and an offered-but-
        unconsumed result is exactly what must be observed.
        """
        for _ in range(timeout_cycles):
            await ReadOnly()
            assert self._issue_ready(), "ready fell while the tag FIFO had room"
            if self._result_offered():
                return get_sim_time('ns'), int(self.dut.result_line.value)
            await RisingEdge(self.dut.clk)
        raise AssertionError("result never offered")

    async def measure_latency(self, opcode, a, b):
        """Retirement-cycle index of the result, 0-based after the issue edge.

        Anchored on packet timestamps: the issue master stamps the packet at
        the accepting edge, the result slave stamps mid-cycle of the retiring
        cycle, so floor(delta/CLK) is the cycle count.  A combinational row
        (offered the cycle right after its issue edge) measures 0; the adder
        row measures ADDER_LATENCY -- the pre-BFM suite's exact semantics.
        """
        self.drain_results()
        pkt = await self.issue(opcode, a=a, b=b)
        rpkt = await self.recv_packet()
        # 0-based retirement-cycle index after the issue edge (the slave
        # stamps mid-cycle of the retiring cycle; floor absorbs the offset).
        return (int(rpkt.end_time) - int(pkt.end_time)) // self.CLK_NS

    # ------------------------------------------------------------------
    # Test scenarios (dispatched by the runner via TEST_TYPE)
    # ------------------------------------------------------------------

    async def test_copy_timing(self):
        """Shell/handshake, copy opcode, natural-latency timing, in-order II=1.

        Timing is anchored on the BFMs' packet timestamps: the issue master
        stamps each packet at its accepting edge, the result slave stamps each
        observed packet at its retiring edge.  A combinational row must retire
        exactly one cycle after issue; a burst streamed with send_burst must
        retire one result per cycle (II=1, proven from handshake deltas).
        """
        self.log.info("=== copy_timing: handshake + natural latency + II=1 stream ===")
        self.drain_results()

        # Single copy: the combinational row lands at the issue edge, so the
        # result is offered in the cycle immediately after the issue edge.
        # Timestamps: the master stamps the accepting edge; the slave stamps
        # mid-cycle of the retiring cycle, so floor(delta/CLK) is the
        # 0-based retirement-cycle index after the issue edge.
        a0 = pack_bf16_line(0x3F80, 0x4000)  # 1.0, 2.0
        pkt = await self.issue(OP_COPY, a=a0)
        rpkt = await self.recv_packet()
        delta = (int(rpkt.end_time) - int(pkt.end_time)) // self.CLK_NS
        assert delta == 0, \
            f"copy retired in cycle {delta} after the issue edge; expected 0 " \
            "(the cycle immediately after)"
        assert (int(rpkt.line), int(rpkt.flags)) == (a0, 0), \
            f"copy result mismatch: got 0x{int(rpkt.line):08X}, exp 0x{a0:08X}"

        # Back-to-back copies streamed as a burst: every result must retire in
        # issue order, one per cycle.
        num = max(6, self.pipe_depth)
        sent = [pack_bf16_line(0x3F80 + i, 0x4000 + i) for i in range(num)]
        pkts = [self._make_packet(OP_COPY, a=a) for a in sent]
        await self.issue_burst(pkts)

        rpkts = await self.recv_packets(num, timeout_cycles=num + 64)
        for i in range(num):
            got = (int(rpkts[i].line), int(rpkts[i].flags))
            assert got == (sent[i], 0), \
                f"stream {i} mismatch: got 0x{got[0]:08X}, exp 0x{sent[i]:08X}"
        times = [int(p.end_time) for p in rpkts]
        for i in range(1, num):
            assert times[i] - times[i - 1] == self.CLK_NS, \
                f"stream bubble before result {i}: {times[i] - times[i - 1]}ns"
        self.log.info(f"copy_timing PASSED (PIPE_DEPTH={self.pipe_depth}, II=1 verified)")

    async def test_add_sub(self):
        """Add/sub golden against the Python float RNE reference."""
        self.log.info("=== add_sub: golden ===")
        self.drain_results()

        cases = [
            (0x3F80, 0x4000, expected_add),  # 1 + 2
            (0x3F80, 0xBF80, expected_add),  # 1 + -1
            (0x4000, 0x3F80, expected_sub),  # 2 - 1
            (0x3F80, 0x4000, expected_sub),  # 1 - 2
            (0x4040, 0x3F80, expected_add),  # 3 + 1
            (0xC000, 0x4000, expected_add),  # -2 + 2
        ]

        for a_lane0, b_lane0, golden in cases:
            a_lane1 = a_lane0 ^ 0x8000  # opposite sign in lane 1 for variety
            a = pack_bf16_line(a_lane0, a_lane1)
            b = pack_bf16_line(b_lane0, b_lane0)
            opcode = OP_ADD if golden is expected_add else OP_SUB
            expected = pack_bf16_line(golden(a_lane0, b_lane0), golden(a_lane1, b_lane0))

            await self.issue(opcode, a=a, b=b)
            line, flags = await self.recv_result()
            g0, e0 = line & 0xFFFF, expected & 0xFFFF
            g1, e1 = (line >> 16) & 0xFFFF, (expected >> 16) & 0xFFFF
            assert bf16_addsub_match(g0, e0, a_lane0, b_lane0) and \
                   bf16_addsub_match(g1, e1, a_lane1, b_lane0), \
                f"{golden.__name__} mismatch: got 0x{line:08X}, exp 0x{expected:08X}"
            assert flags == 0

        self.log.info("add_sub PASSED")

    async def test_mul(self):
        """Mul golden against the Python float RNE reference."""
        self.log.info("=== mul: golden ===")
        self.drain_results()

        cases = [
            (0x3F80, 0x4000),  # 1 * 2
            (0x4000, 0x4000),  # 2 * 2
            (0xBF80, 0x4000),  # -1 * 2
            (0x3F00, 0x4000),  # 0.5 * 2
            (0x0000, 0x7F80),  # 0 * inf
            (0x7F80, 0x7F80),  # inf * inf
        ]

        for a_lane0, b_lane0 in cases:
            a = pack_bf16_line(a_lane0, a_lane0)
            b = pack_bf16_line(b_lane0, b_lane0)
            expected = pack_bf16_line(expected_mul(a_lane0, b_lane0),
                                      expected_mul(a_lane0, b_lane0))
            await self.issue(OP_MUL, a=a, b=b)
            line, flags = await self.recv_result()
            g0, e0 = line & 0xFFFF, expected & 0xFFFF
            g1, e1 = (line >> 16) & 0xFFFF, (expected >> 16) & 0xFFFF
            assert bf16_mul_match(g0, e0) and bf16_mul_match(g1, e1), \
                f"mul mismatch: got 0x{line:08X}, exp 0x{expected:08X}"
            assert flags == 0

        self.log.info("mul PASSED")

    async def test_minmax(self):
        """Min/max, both sub-ops."""
        self.log.info("=== minmax ===")
        self.drain_results()

        cases = [
            (0x4000, 0x3F80),  # 2, 1
            (0xBF80, 0x3F80),  # -1, 1
            (0x7F80, 0x3F80),  # inf, 1
            (0x7FC0, 0x3F80),  # NaN, 1
        ]

        for a_lane0, b_lane0 in cases:
            a = pack_bf16_line(a_lane0, b_lane0)
            b = pack_bf16_line(b_lane0, a_lane0)
            exp_min = pack_bf16_line(expected_min(a_lane0, b_lane0),
                                     expected_min(b_lane0, a_lane0))
            exp_max = pack_bf16_line(expected_max(a_lane0, b_lane0),
                                     expected_max(b_lane0, a_lane0))

            await self.issue(OP_MINMAX, sub_op=0, a=a, b=b)
            line, flags = await self.recv_result()
            assert line == exp_min, f"min mismatch: got 0x{line:08X}, exp 0x{exp_min:08X}"
            assert flags == 0

            await self.issue(OP_MINMAX, sub_op=1, a=a, b=b)
            line, flags = await self.recv_result()
            assert line == exp_max, f"max mismatch: got 0x{line:08X}, exp 0x{exp_max:08X}"
            assert flags == 0

        self.log.info("minmax PASSED")

    async def test_compare(self):
        """Compare vs B and vs imm; result_line is zero, mask packed low in flags."""
        self.log.info("=== compare ===")
        self.drain_results()

        cases_vs_b = [
            (pack_bf16_line(0x3F80, 0x4000), pack_bf16_line(0x4000, 0x3F80)),  # 1<2, 2>1
            (pack_bf16_line(0x7FC0, 0x3F80), pack_bf16_line(0x3F80, 0x7FC0)),  # NaN unordered
        ]

        for a, b in cases_vs_b:
            a0, a1 = unpack_bf16_line(a)
            b0, b1 = unpack_bf16_line(b)
            exp_flags = ((1 if bf16_to_float(a1) < bf16_to_float(b1) else 0) << 1) | \
                        (1 if bf16_to_float(a0) < bf16_to_float(b0) else 0)

            await self.issue(OP_CMP, sub_op=0, a=a, b=b)
            line, flags = await self.recv_result()
            assert line == 0, f"compare result_line must be zero, got 0x{line:08X}"
            assert (flags & 0x3) == exp_flags, \
                f"compare flags mismatch: got 0x{flags:08X}, exp 0x{exp_flags:08X}"

        # Compare vs immediate: lane 0 = 1.0 < 2.0, lane 1 = 2.0 < 2.0 (false).
        a = pack_bf16_line(0x3F80, 0x4000)
        imm = 0x4000
        exp_flags = 0x1  # only lane0 is less
        await self.issue(OP_CMP, sub_op=1, a=a, imm=imm)
        line, flags = await self.recv_result()
        assert line == 0
        assert (flags & 0x3) == exp_flags

        self.log.info("compare PASSED")

    async def test_relu(self):
        """ReLU incl. negative, -0, +0, -inf, NaN."""
        self.log.info("=== relu ===")
        self.drain_results()

        cases = [
            pack_bf16_line(0x3F80, 0xBF80),  # 1.0, -1.0
            pack_bf16_line(0x0000, 0x8000),  # +0, -0
            pack_bf16_line(0xFF80, 0x7FC0),  # -inf, NaN
        ]

        for a in cases:
            a0, a1 = unpack_bf16_line(a)
            expected = pack_bf16_line(expected_relu(a0), expected_relu(a1))
            await self.issue(OP_RELU, a=a)
            line, flags = await self.recv_result()
            assert line == expected, f"relu mismatch: got 0x{line:08X}, exp 0x{expected:08X}"
            assert flags == 0

        self.log.info("relu PASSED")

    async def test_mac(self):
        """MAC CLEAR/ACC/DRAIN/HOLD with the FP32 accumulator."""
        self.log.info("=== mac: CLEAR/ACC/DRAIN/HOLD ===")
        self.drain_results()

        # CLEAR -> result should be +0.
        await self.issue(OP_MAC, a=0, b=0, acc_ctrl=2)
        line, flags = await self.recv_result()
        assert line == 0, f"CLEAR result mismatch: got 0x{line:08X}"
        assert flags == 0

        acc = 0
        # ACC 2.0 * 1.0 -> acc = 2.0
        a = pack_bf16_line(0x4000, 0x4000)
        b = pack_bf16_line(0x3F80, 0x3F80)
        acc = fp32_fma(0x4000, 0x3F80, acc)
        exp = bf16_from_fp32(acc)
        await self.issue(OP_MAC, a=a, b=b, acc_ctrl=1)
        line, flags = await self.recv_result()
        assert line == (exp << 16) | exp, \
            f"ACC mismatch: got 0x{line:08X}, exp 0x{(exp << 16) | exp:08X}"
        assert flags == 0

        # ACC 1.0 * 1.0 -> acc = 3.0
        a = pack_bf16_line(0x3F80, 0x3F80)
        b = pack_bf16_line(0x3F80, 0x3F80)
        acc = fp32_fma(0x3F80, 0x3F80, acc)
        exp = bf16_from_fp32(acc)
        await self.issue(OP_MAC, a=a, b=b, acc_ctrl=1)
        line, flags = await self.recv_result()
        assert line == (exp << 16) | exp
        assert flags == 0

        # DRAIN -> acc unchanged, result is rounded acc.
        await self.issue(OP_MAC, a=0, b=0, acc_ctrl=3)
        line, flags = await self.recv_result()
        assert line == (exp << 16) | exp
        assert flags == 0

        # HOLD -> same.
        await self.issue(OP_MAC, a=0, b=0, acc_ctrl=0)
        line, flags = await self.recv_result()
        assert line == (exp << 16) | exp
        assert flags == 0

        self.log.info("mac PASSED")

    async def test_backpressure(self):
        """Elastic backpressure: results hold, tag FIFO fills, in-order resume."""
        self.log.info("=== backpressure: hold, fill the tag FIFO, resume ===")
        self.stall_results()

        # Issue three copies with the consumer stalled from the start.
        sent = [pack_bf16_line(0x3F80 + i, 0x4000 + i) for i in range(3)]
        for a in sent:
            await self.issue(OP_COPY, a=a)

        # The first result is offered and must hold while the consumer stalls.
        for _ in range(64):
            await ReadOnly()
            if self._result_offered():
                break
            await RisingEdge(self.dut.clk)
        assert self._result_offered(), "first result never offered"
        assert int(self.dut.result_line.value) == sent[0]
        await RisingEdge(self.dut.clk)
        await self.wait_clocks('clk', 5)
        await ReadOnly()
        assert self._result_offered(), "stalled result was dropped"
        assert int(self.dut.result_line.value) == sent[0], "stalled result changed"

        # Drain the three in order.
        self.drain_results()
        got = await self.recv_results(3)
        for i in range(3):
            assert got[i] == (sent[i], 0), \
                f"result {i} mismatch: got 0x{got[i][0]:08X}, exp 0x{sent[i]:08X}"

        # Fill the tag FIFO: with the consumer stalled, exactly PIPE_DEPTH
        # invocations are accepted and then ready must fall.
        self.stall_results()
        await self.wait_clocks('clk', 2)
        fill = [pack_bf16_line(0x5000 + i, 0x6000 + i) for i in range(self.pipe_depth)]
        for a in fill:
            await self.issue(OP_COPY, a=a)
        await ReadOnly()
        assert not self._issue_ready(), "ready still high with the tag FIFO full"

        # Release the consumer; the FIFO drains in issue order and ready recovers.
        self.drain_results()
        got = await self.recv_results(self.pipe_depth,
                                      timeout_cycles=self.pipe_depth + 64)
        for i in range(self.pipe_depth):
            assert got[i] == (fill[i], 0), \
                f"fill {i} mismatch: got 0x{got[i][0]:08X}, exp 0x{fill[i]:08X}"
        for _ in range(32):
            await ReadOnly()
            if self._issue_ready():
                break
            await RisingEdge(self.dut.clk)
        assert self._issue_ready(), "ready did not recover after the drain"

        self.log.info("backpressure PASSED")

    def illegal_func_sels(self):
        """(opcode, sub_op, fmt) triples this build must reject: unassigned
        opcodes, formats a row does not define, unsupported conversion
        pairs, and every family an EN_* parameter built out."""
        ill = [(op, 0, FMT_BF16) for op in range(23, 32)]
        ill += [(op, 0, FMT_INT8) for op in ACT_OPS + BF16_ONLY_OPS]
        ill += [(op, 0, f) for op in BF16_ONLY_OPS for f in (FMT_FP32, FMT_FP8)]
        ill += [(op, 0, f) for op in (OP_PWL, OP_PWL_LUT) for f in (FMT_INT8, FMT_FP32, FMT_FP8)]
        ill += [(OP_ALTFMT, 0, f) for f in (FMT_INT8, FMT_FP32, FMT_FP8)]
        ill += [(OP_CVT, dst, src) for src, dst in CVT_ILLEGAL]
        fam = {'EN_REDUCE': [(OP_REDUCE, 0, FMT_BF16)],
               'EN_PWL': [(OP_PWL, 0, FMT_BF16), (OP_PWL_LUT, 0, FMT_BF16)],
               'EN_ACT': [(OP_LEAKY, 0, FMT_BF16), (OP_RECIP, 0, FMT_BF16)],
               'EN_CVT': [(OP_CVT, FMT_FP32, FMT_BF16), (OP_ALTFMT, 0, FMT_BF16)],
               'EN_INT8': [(OP_ADD, 0, FMT_INT8), (OP_MAC, 0, FMT_INT8)],
               'EN_FP32': [(OP_ADD, 0, FMT_FP32), (OP_MUL, 0, FMT_FP32)],
               'EN_FP8': [(OP_ADD, 0, FMT_FP8), (OP_COPY, 0, FMT_FP8)]}
        for k, ops in fam.items():
            if not self.en[k]:
                ill += ops
        return ill

    async def test_error_opcode(self):
        """Illegal func_sel: retires in order with a zero line and zero
        flags, and pulses err_opcode exactly once at its issue edge."""
        self.log.info("=== error_opcode: illegal classes retire in order, err_opcode ===")
        self.drain_results()
        illegal = self.illegal_func_sels()
        if self.level == 'gate':
            illegal = illegal[::3]

        cases, expected = [], []
        for k, (op, sub, fmt) in enumerate(illegal):
            copy_a = pack_bf16_line(0x3F80 + k, 0x4000 + k)
            cases.append((OP_COPY, 0, 0, copy_a))
            expected.append(copy_a)
            cases.append((op, sub, fmt, 0x3F803F80))
            expected.append(0)

        start_pulses = self.err_pulses
        pkts = [self._make_packet(op, a=a, sub_op=sub, fmt=fmt) for op, sub, fmt, a in cases]
        await self.issue_burst(pkts)
        got = await self.recv_results(len(pkts), timeout_cycles=len(pkts) + 128)
        for i, exp in enumerate(expected):
            line, flags = got[i]
            assert line == exp, f"result {i} {cases[i][:3]}: got 0x{line:08X}, exp 0x{exp:08X}"
            assert flags == 0, f"result {i} flags mismatch: got 0x{flags:08X}"
        await self.wait_clocks('clk', 2)
        pulses = self.err_pulses - start_pulses
        assert pulses == len(illegal), \
            f"err_opcode pulsed {pulses} times for {len(illegal)} illegal issues"

        self.log.info(f"error_opcode PASSED ({len(illegal)} illegal func_sels, "
                      f"{pulses} err_opcode pulses)")

    async def test_special_grid(self):
        """Special-value grid for add/sub/mul/minmax/compare/relu."""
        self.log.info("=== special_grid ===")
        self.drain_results()

        grid = BF16_SPECIAL_GRID

        # Gate: small deterministic cross-section; func/full: exhaustive grid.
        if self.level == 'gate':
            pairs = self.GRID_PAIRS_GATE
        else:
            pairs = [(i, j) for i in range(len(grid)) for j in range(len(grid))]

        def grid_value(idx):
            return grid[idx][1]

        for i, j in pairs:
            a0 = grid_value(i)
            b0 = grid_value(j)
            a1 = grid_value(j)
            b1 = grid_value(i)
            a = pack_bf16_line(a0, a1)
            b = pack_bf16_line(b0, b1)

            any_subnormal = (is_subnormal_bf16(a0) or is_subnormal_bf16(b0)
                             or is_subnormal_bf16(a1) or is_subnormal_bf16(b1))

            # add/sub: math_bf16_adder flushes subnormal inputs/outputs (FTZ).
            if not any_subnormal:
                exp = pack_bf16_line(expected_add(a0, b0), expected_add(a1, b1))
                await self.issue(OP_ADD, a=a, b=b)
                line, flags = await self.recv_result()
                assert bf16_addsub_match(line & 0xFFFF, exp & 0xFFFF, a0, b0) and \
                       bf16_addsub_match((line >> 16) & 0xFFFF, (exp >> 16) & 0xFFFF, a1, b1), \
                    f"add grid ({i},{j}) mismatch: got 0x{line:08X}, exp 0x{exp:08X}"
                assert flags == 0

                exp = pack_bf16_line(expected_sub(a0, b0), expected_sub(a1, b1))
                await self.issue(OP_SUB, a=a, b=b)
                line, flags = await self.recv_result()
                assert bf16_addsub_match(line & 0xFFFF, exp & 0xFFFF, a0, b0) and \
                       bf16_addsub_match((line >> 16) & 0xFFFF, (exp >> 16) & 0xFFFF, a1, b1), \
                    f"sub grid ({i},{j}) mismatch: got 0x{line:08X}, exp 0x{exp:08X}"
                assert flags == 0

                # mul: math_bf16_multiplier flushes subnormal inputs (FTZ).
                exp = pack_bf16_line(expected_mul(a0, b0), expected_mul(a1, b1))
                await self.issue(OP_MUL, a=a, b=b)
                line, flags = await self.recv_result()
                assert bf16_mul_match(line & 0xFFFF, exp & 0xFFFF) and \
                       bf16_mul_match((line >> 16) & 0xFFFF, (exp >> 16) & 0xFFFF), \
                    f"mul grid ({i},{j}) mismatch: got 0x{line:08X}, exp 0x{exp:08X}"
                assert flags == 0

            # min
            exp = pack_bf16_line(expected_min(a0, b0), expected_min(a1, b1))
            await self.issue(OP_MINMAX, sub_op=0, a=a, b=b)
            line, flags = await self.recv_result()
            assert line == exp, f"min grid ({i},{j}) mismatch: got 0x{line:08X}, exp 0x{exp:08X}"
            assert flags == 0

            # max
            exp = pack_bf16_line(expected_max(a0, b0), expected_max(a1, b1))
            await self.issue(OP_MINMAX, sub_op=1, a=a, b=b)
            line, flags = await self.recv_result()
            assert line == exp, f"max grid ({i},{j}) mismatch: got 0x{line:08X}, exp 0x{exp:08X}"
            assert flags == 0

            # relu on operand A
            exp = pack_bf16_line(expected_relu(a0), expected_relu(a1))
            await self.issue(OP_RELU, a=a)
            line, flags = await self.recv_result()
            assert line == exp, f"relu grid ({i},{j}) mismatch: got 0x{line:08X}, exp 0x{exp:08X}"
            assert flags == 0

            # compare vs B: flags packed low, NaN unordered -> False.
            exp_flags = ((1 if bf16_to_float(a1) < bf16_to_float(b1) else 0) << 1) | \
                        (1 if bf16_to_float(a0) < bf16_to_float(b0) else 0)
            await self.issue(OP_CMP, sub_op=0, a=a, b=b)
            line, flags = await self.recv_result()
            assert line == 0, f"compare grid ({i},{j}) result_line must be zero"
            assert (flags & 0x3) == exp_flags, \
                f"compare grid ({i},{j}) flags mismatch: got 0x{flags:08X}, exp 0x{exp_flags:08X}"

        self.log.info("special_grid PASSED")

    async def test_mixed_soak(self):
        """Random mixed-opcode sequence retires in-order with golden check.

        Under a non-default GAXI_TIMING_PROFILE the master's valid and the
        slave's ready delays randomize per beat, which exercises the elastic
        pipeline against the same golden sequence.
        """
        count = self.SOAK_COUNT.get(self.level, 32)
        seeds = self.SEEDS.get(self.level, [0xA1])
        self.log.info(f"=== mixed_soak: {count} ops x {len(seeds)} seeds "
                      f"(level={self.level}) ===")
        self.drain_results()

        def rand_bf16():
            # Random 16-bit pattern excluding subnormals, which the BF16 rows
            # flush to zero (FTZ).
            while True:
                v = random.randint(0, 0xFFFF)
                if not is_subnormal_bf16(v):
                    return v

        for seed in seeds:
            random.seed(seed)

            # Per-lane FP32 accumulator state for MAC ops; reset each seed.  The
            # DUT's accumulator is architectural state and survives across the
            # seed loop (it clears only on acc_ctrl CLEAR or reset), so align the
            # hardware with the golden model by issuing one CLEAR mac before each
            # seed's sequence and draining its don't-care result.
            acc = [0, 0]
            await self.issue(OP_MAC, a=0, b=0, acc_ctrl=2)
            await self.recv_result()

            def expected(opcode, sub_op, a, b, imm, acc_ctrl_):
                a0, a1 = unpack_bf16_line(a)
                b0, b1 = unpack_bf16_line(b)
                nonlocal acc
                if opcode == OP_COPY:
                    return a, 0
                elif opcode == OP_ADD:
                    return pack_bf16_line(expected_add(a0, b0), expected_add(a1, b1)), 0
                elif opcode == OP_SUB:
                    return pack_bf16_line(expected_sub(a0, b0), expected_sub(a1, b1)), 0
                elif opcode == OP_MUL:
                    return pack_bf16_line(expected_mul(a0, b0), expected_mul(a1, b1)), 0
                elif opcode == OP_MAC:
                    # MAC: update accumulator and return BF16 view.
                    for lane in range(2):
                        if acc_ctrl_ == 2:
                            acc[lane] = 0
                        elif acc_ctrl_ == 1:
                            acc[lane] = fp32_fma(a0 if lane == 0 else a1,
                                                 b0 if lane == 0 else b1,
                                                 acc[lane])
                        # HOLD/DRAIN: acc unchanged
                    return pack_bf16_line(bf16_from_fp32(acc[0]), bf16_from_fp32(acc[1])), 0
                elif opcode == OP_MINMAX:
                    if sub_op == 0:
                        return pack_bf16_line(expected_min(a0, b0), expected_min(a1, b1)), 0
                    else:
                        return pack_bf16_line(expected_max(a0, b0), expected_max(a1, b1)), 0
                elif opcode == OP_CMP:
                    exp_flags = ((1 if bf16_to_float(a1) < bf16_to_float(b1 if sub_op == 0 else imm) else 0) << 1) | \
                                (1 if bf16_to_float(a0) < bf16_to_float(b0 if sub_op == 0 else imm) else 0)
                    return 0, exp_flags
                elif opcode == OP_RELU:
                    return pack_bf16_line(expected_relu(a0), expected_relu(a1)), 0
                else:
                    return 0, 0

            issued = []
            results = []

            # Issue/drain mixed opcodes in order.  Each issue is followed by its
            # result receive, so the test is a functional soak; copy_timing
            # already proves the pipeline sustains II=1.
            for idx in range(count):
                a = rand_bf16()
                b = rand_bf16()
                imm = rand_bf16() & 0xFFFF
                opcode = random.choice([0, 1, 2, 3, 4, 5, 6, 7, 23])
                sub_op = random.choice([0, 1])
                acc_ctrl = random.choice([0, 1, 2, 3])

                exp_line, exp_flags = expected(opcode, sub_op, a, b, imm, acc_ctrl)
                issued.append((opcode, sub_op, a, b, imm, acc_ctrl, exp_line, exp_flags))

                await self.issue(opcode, sub_op=sub_op, a=a, b=b, imm=imm, acc_ctrl=acc_ctrl)
                line, flags = await self.recv_result()
                results.append((line, flags))

            assert len(results) == count
            for i, (opcode, sub_op, a, b, imm, acc_ctrl, exp_line, exp_flags) in enumerate(issued):
                line, flags = results[i]
                a0, a1 = unpack_bf16_line(a)
                b0, b1 = unpack_bf16_line(b)
                if opcode in [OP_ADD, OP_SUB]:
                    assert bf16_addsub_match(line & 0xFFFF, exp_line & 0xFFFF, a0, b0) and \
                           bf16_addsub_match((line >> 16) & 0xFFFF, (exp_line >> 16) & 0xFFFF, a1, b1), \
                        f"seed={seed} soak {i} opcode={opcode} mismatch: got 0x{line:08X}, exp 0x{exp_line:08X}"
                elif opcode == OP_MUL:
                    assert bf16_mul_match(line & 0xFFFF, exp_line & 0xFFFF) and \
                           bf16_mul_match((line >> 16) & 0xFFFF, (exp_line >> 16) & 0xFFFF), \
                        f"seed={seed} soak {i} opcode={opcode} mismatch: got 0x{line:08X}, exp 0x{exp_line:08X}"
                else:
                    if line != exp_line:
                        self.log.error(f"MAC mismatch soak {i} seed={seed}: got 0x{line:08X}, exp 0x{exp_line:08X}")
                        self.log.error(f"  operands a=0x{a:08X} b=0x{b:08X} acc_ctrl={acc_ctrl}")
                        self.log.error(f"  acc_bank[0]=0x{int(self.dut.u_rows.u_acc.acc_bank[0].value):08X} acc_bank[1]=0x{int(self.dut.u_rows.u_acc.acc_bank[1].value):08X}")
                        self.log.error(f"  next_acc_bank[0]=0x{int(self.dut.u_rows.u_acc.next_acc_bank[0].value):08X} next_acc_bank[1]=0x{int(self.dut.u_rows.u_acc.next_acc_bank[1].value):08X}")
                        self.log.error(f"  fma_result[0]=0x{int(self.dut.u_rows.u_acc.fma_result[0].value):08X} fma_result[1]=0x{int(self.dut.u_rows.u_acc.fma_result[1].value):08X}")
                    assert line == exp_line, \
                        f"seed={seed} soak {i} opcode={opcode} mismatch: got 0x{line:08X}, exp 0x{exp_line:08X}"
                assert (flags & 0x3) == (exp_flags & 0x3), \
                    f"seed={seed} soak {i} opcode={opcode} flags mismatch: got 0x{flags:08X}, exp 0x{exp_flags:08X}"

        self.log.info(f"mixed_soak PASSED ({len(seeds)} seeds)")

    async def test_sub_ulp_corner(self):
        """Directed SUB corner that exposes the library adder's 1-ULP tolerance.

        a = 0x78E5, b = 0x7611: exponent delta is |0xF1 - 0xEC| = 5 (>3), so the
        library adder's 11-bit alignment can lose the tie-break bit.  Exact IEEE
        RNE for the subtraction is 0x78E0; the library-accepted hardware result is
        0x78E1 (1 ULP high).  This test documents that the ALU-INFER DV contract
        matches the library adder's proven contract, not a strict bit-exact RNE
        reference.
        """
        self.log.info("=== sub_ulp_corner: large exponent delta ===")
        self.drain_results()

        a_lane0, b_lane0 = 0x78E5, 0x7611
        a = pack_bf16_line(a_lane0, a_lane0)
        b = pack_bf16_line(b_lane0, b_lane0)
        exact_rne = expected_sub(a_lane0, b_lane0)  # 0x78E0
        library_accepted = 0x78E1

        self.log.info(f"  exact RNE = 0x{exact_rne:04X}; library-accepted = 0x{library_accepted:04X}")

        await self.issue(OP_SUB, a=a, b=b)
        line, flags = await self.recv_result()
        got_lane0 = line & 0xFFFF
        got_lane1 = (line >> 16) & 0xFFFF

        # The DUT must be within the 1-ULP tolerance for large exponent-delta SUB.
        assert bf16_addsub_match(got_lane0, exact_rne, a_lane0, b_lane0), \
            f"SUB corner lane0 mismatch: got 0x{got_lane0:04X}, exact RNE 0x{exact_rne:04X}"
        assert bf16_addsub_match(got_lane1, exact_rne, a_lane0, b_lane0), \
            f"SUB corner lane1 mismatch: got 0x{got_lane1:04X}, exact RNE 0x{exact_rne:04X}"
        assert flags == 0

        self.log.info(f"sub_ulp_corner PASSED (got 0x{got_lane0:04X})")

    async def test_tag_join(self):
        """Tag-FIFO join: fast rows wait behind an earlier slow row.

        The tag FIFO retires strictly in issue order at natural per-row latency:
        combinational rows (copy/relu/mul/mac/minmax/cmp) are offered the cycle
        after their issue edge; add/sub are offered ADDER_LATENCY cycles after.
        A fast result issued behind a slow one must wait at the head of the FIFO
        until the slow result retires (owner ruling 2026-10-18: following ops
        align with or after the earlier slower operation).
        """
        self.log.info("=== tag_join: mixed natural latencies ===")

        one = pack_bf16_line(0x3F80, 0x3F80)
        two = pack_bf16_line(0x4000, 0x4000)

        n_copy = await self.measure_latency(OP_COPY, one, 0)
        n_relu = await self.measure_latency(OP_RELU, one, 0)
        n_mul = await self.measure_latency(OP_MUL, one, two)
        n_add = await self.measure_latency(OP_ADD, one, two)

        assert n_copy == 0, f"copy latency {n_copy}, expected 0 (combinational row)"
        assert n_relu == 0, f"relu latency {n_relu}, expected 0 (combinational row)"
        assert n_mul == self.mul_latency, \
            f"mul latency {n_mul}, expected MUL_LATENCY={self.mul_latency}"
        assert n_add == self.adder_latency, \
            f"add latency {n_add}, expected ADDER_LATENCY={self.adder_latency}"
        self.log.info(f"  natural latencies: copy/relu/mul = 1 cycle, add = {n_add + 1} cycles")

        # Join: add (slow) then relu then copy (fast), streamed back-to-back
        # with the consumer stalled.  The head must not appear before the
        # add's natural-latency deadline, and the drain order must be add,
        # relu, copy.
        self.stall_results()
        a_add = pack_bf16_line(0x3F80, 0x4000)   # 1.0, 2.0
        b_add = pack_bf16_line(0x4000, 0x3F80)   # 2.0, 1.0
        exp_add = pack_bf16_line(expected_add(0x3F80, 0x4000), expected_add(0x4000, 0x3F80))
        a_relu = pack_bf16_line(0xBF80, 0x3F80)  # -1.0 -> 0, 1.0
        exp_relu = pack_bf16_line(0x0000, 0x3F80)
        a_copy = pack_bf16_line(0x4040, 0x4080)  # 3.0, 4.0

        # The watcher passively records the first offered result and asserts
        # the issue side stays ready every cycle until then (the consumer is
        # stalled and the FIFO has room -- issue must stay open).
        watcher = cocotb.start_soon(self._watch_first_offer())
        pkts = [self._make_packet(OP_ADD, a=a_add, b=b_add),
                self._make_packet(OP_RELU, a=a_relu),
                self._make_packet(OP_COPY, a=a_copy)]
        await self.issue_burst(pkts)
        t_offer, offer_line = await watcher
        t_add = int(pkts[0].end_time)

        # Nothing may be offered before the add's natural latency, and at the
        # deadline the head is the add result, not the (long-computed) relu or
        # copy that landed behind it.
        join_delta = (t_offer - t_add) // self.CLK_NS
        assert join_delta == self.adder_latency, \
            f"first offer {join_delta} cycles after the add issue; " \
            f"expected ADDER_LATENCY={self.adder_latency} " \
            "(early = a fast row jumped the join; late = padded stages)"
        assert offer_line == exp_add, \
            f"head is not the add result: got 0x{offer_line:08X}, exp 0x{exp_add:08X}"

        self.drain_results()
        got = await self.recv_results(3)
        for i, exp in enumerate([exp_add, exp_relu, a_copy]):
            assert got[i][0] == exp, \
                f"join order {i} mismatch: got 0x{got[i][0]:08X}, exp 0x{exp:08X}"
            assert got[i][1] == 0

        self.log.info("tag_join PASSED")

    # ------------------------------------------------------------------
    # Monitor reporting
    # ------------------------------------------------------------------

    def log_monitor_stats(self):
        """Completed-transfer counts observed by the passive monitors."""
        issue_seen = len(self.mon_issue.get_completed_packets())
        result_seen = len(self.mon_result.get_completed_packets())
        self.log.info(f"monitors: issue transfers={issue_seen}, result transfers={result_seen}, "
                      f"slave-received={len(self.result_slave.get_observed_packets())}")

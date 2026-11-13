# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_ref_cache_rw
# Purpose: Read-after-write check of the two reference L1 wrappers (cache-ip
#   common-ip TASK-003) through the house GAXI BFMs: random strobed writes over
#   a span twice the cache, every word read back and compared with a software
#   image (memory starts zero), then a pipelined burst (many requests in flight)
#   read back the same way. The rig's cycle injector cannot make this check --
#   its read addresses never coincide with its write addresses (both derive from
#   the same LFSR bits) -- so this is where a wrong read path would show.

import os
import random
import sys

import pytest
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb_test.simulator import run

repo_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(
        os.path.abspath(__file__)))))))))
sys.path.insert(0, repo_root)

from TBClasses.shared.utilities import create_view_cmd, sim_build_path  # noqa: E402
from TBClasses.shared.filelist_utils import get_sources_from_filelist  # noqa: E402
from TBClasses.shared.test_levels import reg_level_grid, level_env  # noqa: E402
from TBClasses.shared.tbbase import TBBase  # noqa: E402
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer  # noqa: E402
from CocoTBFramework.components.shared.field_config import FieldConfig  # noqa: E402
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster  # noqa: E402
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave  # noqa: E402

REF_FRAMEWORK_ROOT = os.path.join(
    repo_root, "projects", "fpga-systems", "Genesys2", "cache-ip", "ref")

ADDR_WIDTH, BUS_WIDTH = 32, 64
STRB_W = BUS_WIDTH // 8
CPU_REQ_W = ADDR_WIDTH + 1 + STRB_W + BUS_WIDTH
CACHE_BYTES = 32768
WORDS = {"gate": 2048, "func": 8192, "full": 16384}      # words touched (span = 2x cache / 8 B = 8192)
RSP_TIMEOUT = 20000


class RefCacheRWTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.level = os.environ.get("TEST_LEVEL", "gate")
        self.seed = int(os.environ.get("SEED", "1"))
        self.rng = random.Random(self.seed)
        self.rsp = []
        self.mem = {}
        req_fields = FieldConfig.from_dict(
            field_dict={'data': {'bits': CPU_REQ_W, 'default': 0}}, lsb_first=True)
        rsp_fields = FieldConfig.from_dict(
            field_dict={'data': {'bits': BUS_WIDTH, 'default': 0}}, lsb_first=True)
        self.master = GAXIMaster(
            dut=dut, title='cpu_req', prefix='', clock=dut.clk, field_config=req_fields,
            timeout_cycles=RSP_TIMEOUT, mode='skid', bus_name='cpu_req_wr', pkt_prefix='',
            multi_sig=False, randomizer=FlexRandomizer({'valid_delay': ([(0, 0)], [1])}),
            log=self.log)
        self.slave = GAXISlave(
            dut=dut, title='cpu_rsp', prefix='', clock=dut.clk, field_config=rsp_fields,
            timeout_cycles=RSP_TIMEOUT, mode='skid', bus_name='cpu_rsp_rd', pkt_prefix='',
            multi_sig=False, randomizer=FlexRandomizer({'ready_delay': ([(0, 0)], [1])}),
            log=self.log)
        self.slave.add_callback(self._on_rsp)
        self.slave.set_ready_policy('always')

    def _on_rsp(self, packet):
        self.rsp.append(int(getattr(packet, 'fields', {}).get('data', 0)))

    async def reset(self):
        self.dut.rst_n.value = 0
        await self.wait_clocks('clk', 10)
        self.dut.rst_n.value = 1
        await self.wait_clocks('clk', 5)

    @staticmethod
    def pack(addr, we, be, wdata):
        return ((addr & ((1 << ADDR_WIDTH) - 1)) << (1 + STRB_W + BUS_WIDTH)) \
            | ((we & 1) << (STRB_W + BUS_WIDTH)) | ((be & ((1 << STRB_W) - 1)) << BUS_WIDTH) \
            | (wdata & ((1 << BUS_WIDTH) - 1))

    def model_write(self, word, be, wdata):
        cur = self.mem.get(word, 0)
        for b in range(STRB_W):
            if (be >> b) & 1:
                cur = (cur & ~(0xFF << (8 * b))) | (wdata & (0xFF << (8 * b)))
        self.mem[word] = cur

    async def send(self, addr, we, be=0xFF, wdata=0):
        pkt = self.master.create_packet(data=self.pack(addr, we, be, wdata))
        await self.master.send(pkt)

    async def wait_rsp(self, n):
        for _ in range(RSP_TIMEOUT):
            if len(self.rsp) >= n:
                return
            await RisingEdge(self.dut.clk)
        raise AssertionError(f"only {len(self.rsp)} of {n} responses arrived")

    async def write_then_read(self, words, label):
        """Strobed random writes to `words`, then read every word back."""
        n0 = len(self.rsp)
        for w in words:
            be = self.rng.randrange(1, 1 << STRB_W)
            wd = self.rng.getrandbits(BUS_WIDTH)
            self.model_write(w, be, wd)
            await self.send(w * 8, 1, be, wd)
        await self.wait_rsp(n0 + len(words))
        n1 = len(self.rsp)
        for w in words:
            await self.send(w * 8, 0)
        await self.wait_rsp(n1 + len(words))
        bad = 0
        for i, w in enumerate(words):
            got = self.rsp[n1 + i]
            if got != self.mem[w]:
                bad += 1
                if bad <= 10:
                    self.log.error(f"{label}: word 0x{w:x} got 0x{got:016x} exp 0x{self.mem[w]:016x}")
        self.log.info(f"{label}: {len(words)} words written and read back, {bad} mismatches")
        return bad

    async def run(self):
        bad = 0
        n = WORDS[self.level]
        span_words = 2 * CACHE_BYTES // 8
        # 1. sequential sweep over twice the cache: fills, evictions, write-backs
        seq = list(range(0, min(n, span_words)))
        bad += await self.write_then_read(seq, "sequential x2-cache")
        # 2. random words across the span, repeats included (read-modify-write of
        #    partial strobes on words already dirty in the cache or in memory)
        rnd = [self.rng.randrange(span_words) for _ in range(n)]
        bad += await self.write_then_read(rnd, "random strobed")
        # 3. the pipelined posture: all writes back-to-back, then all reads
        #    back-to-back (the BFM holds valid high; the cache paces it)
        pipe = [self.rng.randrange(span_words) for _ in range(n)]
        bad += await self.write_then_read(pipe, "pipelined")
        assert int(self.dut.o_rsp_error.value) == 0, "a response carried an error flag"
        return bad


@cocotb.test(timeout_time=20000, timeout_unit="ms")
async def cocotb_test_ref_cache_rw(dut):
    tb = RefCacheRWTB(dut)
    await tb.start_clock('clk', freq=10, units='ns')
    await tb.reset()
    bad = await tb.run()
    assert bad == 0, f"{bad} read-after-write mismatches"


REF_CACHES = {"hpd": 0, "cva6": 1, "jetp": 2}   # jetp: jet-prime straight onto memory


@pytest.mark.parametrize("ref_cache", list(REF_CACHES), ids=list(REF_CACHES))
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_ref_cache_rw(request, test_level, ref_cache):
    module = "test_ref_cache_rw"
    dut_name = "ref_cache_tb"
    log_dir = os.path.join(REF_FRAMEWORK_ROOT, "dv", "tests", "log")
    tests_dir = os.path.join(REF_FRAMEWORK_ROOT, "dv", "tests")
    test_name = f"{module}_{ref_cache}_{test_level}"
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")
    os.environ['REF_FRAMEWORK_ROOT'] = REF_FRAMEWORK_ROOT
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/fpga-systems/Genesys2/cache-ip/ref/dv/filelists/ref_cache_tb.f')
    extra_env = {
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path, 'COCOTB_TEST_TIMEOUT': '600000',
        'REF_FRAMEWORK_ROOT': REF_FRAMEWORK_ROOT,
        **level_env(test_level),
    }
    create_view_cmd(log_dir, log_path, sim_build, module, test_name)
    compile_args = [
        FIELD_COMBO_VLT, "--timescale", "1ns/1ps", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME", "-Wno-UNUSEDSIGNAL",
        "-Wno-VARHIDDEN", "-Wno-IMPLICIT", "-Wno-CASEOVERLAP", "-Wno-MODDUP", "-Wno-PINMISSING",
    ]
    run(
        python_search=[tests_dir, repo_root], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, sim_build=sim_build, extra_env=extra_env,
        waves=True, keep_files=True, compile_args=compile_args,
        parameters={"REF_CACHE_SEL": REF_CACHES[ref_cache]},
    )

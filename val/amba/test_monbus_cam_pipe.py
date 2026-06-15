# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Equivalence test: monbus_cam_pipe (2-cycle, forwarded) must produce the
# SAME (hit, idx, old_data, old_ts) result sequence as the single-cycle
# monbus_cam for any access stream -- including same-key back-to-back (the
# move-to-front RAW hazard the forwarding exists to cover), bursts, evictions,
# and idle bubbles.

import os
import random
from typing import List

import cocotb
from cocotb.triggers import RisingEdge, ReadOnly
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd


class CamPipeTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = int(os.environ.get('SEED', '0'))
        random.seed(self.SEED)

    async def reset(self):
        self.dut.en.value = 0
        self.dut.key.value = 0
        self.dut.new_data.value = 0
        self.dut.new_ts.value = 0
        self.dut.rst_n.value = 0
        await self.wait_clocks('clk', 5)
        self.dut.rst_n.value = 1
        await self.wait_clocks('clk', 2)

    async def run_stream(self, accesses: List[tuple]):
        """accesses = list of (en, key, new_data, new_ts).
        Captures the reference result on each en=1 cycle and the pipelined
        result on each pipe_valid cycle, then asserts the two sequences match."""
        ref_seq = []
        pipe_seq = []
        # Drive, plus a few trailing idle cycles to flush the pipe.
        seq = list(accesses) + [(0, 0, 0, 0)] * 4
        for (en, key, nd, nts) in seq:
            self.dut.en.value = en
            self.dut.key.value = key
            self.dut.new_data.value = nd
            self.dut.new_ts.value = nts
            await ReadOnly()
            if en:
                ref_seq.append((int(self.dut.ref_hit.value), int(self.dut.ref_idx.value),
                                int(self.dut.ref_old_data.value), int(self.dut.ref_old_ts.value)))
            if int(self.dut.pipe_valid.value) == 1:
                pipe_seq.append((int(self.dut.pipe_hit.value), int(self.dut.pipe_idx.value),
                                 int(self.dut.pipe_old_data.value), int(self.dut.pipe_old_ts.value)))
            await RisingEdge(self.dut.clk)

        assert len(ref_seq) == len(pipe_seq), \
            f"count mismatch: ref={len(ref_seq)} pipe={len(pipe_seq)}"
        for i, (r, p) in enumerate(zip(ref_seq, pipe_seq)):
            assert r == p, f"access {i}: ref={r} pipe={p}"
        return len(ref_seq)


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def monbus_cam_pipe_test(dut):
    tb = CamPipeTB(dut)
    await tb.start_clock('clk', 10, 'ns')
    await tb.reset()

    # Phase 1: directed — same-key back-to-back (the forwarding hazard).
    seq = []
    for k in (5, 5, 5, 7, 7, 5, 5, 9, 5, 7):       # repeats + interleave
        seq.append((1, k, 0xD000 + k, 0x100 + k))
    n = await tb.run_stream(seq)
    tb.log.info(f"=== Phase 1 (directed same-key) PASS, {n} accesses ===")
    await tb.reset()

    # Phase 2: bursts with idle bubbles between groups.
    seq = []
    for grp in range(8):
        for _ in range(random.randint(1, 4)):
            k = random.choice([3, 3, 3, 4, 5])      # bias to repeats
            seq.append((1, k, random.randrange(1 << 20), random.randrange(1 << 16)))
        for _ in range(random.randint(0, 2)):
            seq.append((0, 0, 0, 0))                 # bubbles
    n = await tb.run_stream(seq)
    tb.log.info(f"=== Phase 2 (bursts+bubbles) PASS, {n} accesses ===")
    await tb.reset()

    # Phase 3: long random stream over a key space > DEPTH (forces evictions),
    # action implied (TOUCH on hit / INSTALL on miss) -- exercises shift,
    # eviction, and same-key-after-evict adjustments.
    seq = []
    ts = 1
    for _ in range(800):
        en = 1 if random.random() < 0.85 else 0     # ~15% bubbles
        k = random.randrange(0, 40)                  # > DEPTH=32 -> evictions
        ts += random.randint(1, 7)
        seq.append((en, k, random.randrange(1 << 30), ts & 0xFFFFFF))
    n = await tb.run_stream(seq)
    tb.log.info(f"=== Phase 3 (random+evict) PASS, {n} accesses ===")
    tb.log.info("=== ALL PHASES PASSED ===")


def test_monbus_cam_pipe(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_shared':   'rtl/amba/shared',
        'rtl_includes': 'rtl/amba/includes',
        'val_amba':     'val/amba',
    })
    dut_name = "monbus_cam_pipe_dut"
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name = f"test_{worker_id}_{dut_name}_{reg_level}"
    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)

    verilog_sources = [
        os.path.join(rtl_dict['rtl_shared'],   "monbus_cam.sv"),
        os.path.join(rtl_dict['rtl_shared'],   "monbus_cam_pipe.sv"),
        os.path.join(rtl_dict['val_amba'],     f"{dut_name}.sv"),
    ]
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    extra_env = {
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_CLK_PERIOD': '10',
    }
    compile_args = ['+define+SIMULATION', '--trace-fst', '--trace-structs',
                    '-Wno-DECLFILENAME', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC',
                    '-Wno-UNUSEDPARAM', '-Wno-TIMESCALEMOD']
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)
    try:
        run(python_search=[tests_dir], verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_includes'], rtl_dict['rtl_shared'], sim_build],
            toplevel=dut_name, module=module, sim_build=sim_build,
            extra_env=extra_env, waves=bool(int(os.environ.get('WAVES', '0'))),
            keep_files=True, compile_args=compile_args)
    except Exception as e:
        print(f"Test failed: {e}\nLogs: {log_path}\nWaveforms: {cmd_filename}")
        raise

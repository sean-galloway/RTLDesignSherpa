# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi_monitor_trans_mgr_equiv
# Purpose: Differential equivalence test for the AXI monitor transaction
#          manager. Two pytest entries:
#            * test_axi_monitor_trans_mgr_prod  -- compiles the production
#              rtl/amba/shared/axi_monitor_trans_mgr.sv, runs random
#              stimulus with a fixed seed, dumps a cycle-by-cycle JSON
#              capture of trans_table + active_count + state_change.
#            * test_axi_monitor_trans_mgr_stage -- compiles the staging
#              rtl/amba/shared/mon_temp/axi_monitor_trans_mgr.sv (which
#              uses monitor_trans_cam for keying + payload storage), runs
#              the same stimulus, compares bit-exact against the prod
#              capture.
#
# Author: sean galloway
# Created: 2026-06-08

"""
Differential equivalence test for the AXI monitor transaction manager.

Goal: prove that the staging trans_mgr (rtl/amba/shared/mon_temp/,
backed by monitor_trans_cam) produces identical outputs to the
production trans_mgr (rtl/amba/shared/) under the same stimulus.

How: each pytest function runs the same cocotb test against a different
set of verilog sources. The shared cocotb test:
  - seeds Python's random with a fixed value so both runs see the same
    stimulus sequence
  - drives MAX_STIM_CYCLES cycles of randomized cmd/data/resp handshakes
    plus randomized i_event_reported_flags
  - samples trans_table[N] (decoded into a dict per slot), active_count,
    and state_change on every cycle after the rising edge
  - in MODE=capture, dumps the sequence to a JSON file
  - in MODE=compare, loads the JSON and asserts every cycle's snapshot
    matches bit-exact

If both tests pass, the two RTLs are functionally equivalent on the
generated stimulus. No Python golden model is needed -- the prod RTL
itself is the reference.

The bus_transaction_t struct is decoded by bit-slicing the packed int
representation, sidestepping any simulator-specific quirks with packed
structs inside unpacked array ports.
"""

import json
import os
import random
from pathlib import Path
from typing import Dict, List

import pytest
import cocotb
from cocotb.triggers import RisingEdge, ReadOnly
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd


# ----------------------------------------------------------------------------
# Capture path -- both pytest entries agree on a deterministic file path
# under val/amba/logs/ so capture survives between runs.
# ----------------------------------------------------------------------------
REPO_ROOT     = Path(__file__).resolve().parents[2]
CAPTURE_DIR   = REPO_ROOT / "val/amba/logs/trans_mgr_equiv"
CAPTURE_DIR.mkdir(parents=True, exist_ok=True)


def _capture_filename(is_read: int, is_axi: int, max_trans: int, id_width: int,
                      stim_cycles: int, seed: int) -> str:
    flavor = ("rd" if is_read else "wr") + ("_axi4" if is_axi else "_axil")
    return (f"capture_{flavor}_mt{max_trans:02d}_iw{id_width:02d}"
            f"_sc{stim_cycles:04d}_seed{seed}.json")


# ----------------------------------------------------------------------------
# bus_transaction_t decoder
#
# Layout from rtl/amba/includes/monitor_amba4_pkg.sv (MSB-first packed
# struct). Total 285 bits.
# ----------------------------------------------------------------------------
def decode_bus_transaction(value: int) -> Dict[str, int]:
    """Decode a packed bus_transaction_t (as an int) into a field dict."""
    return {
        'valid':           (value >> 284) & 0x1,
        'cmd_received':    (value >> 283) & 0x1,
        'data_started':    (value >> 282) & 0x1,
        'data_completed':  (value >> 281) & 0x1,
        'resp_received':   (value >> 280) & 0x1,
        'event_reported':  (value >> 279) & 0x1,
        'eos_seen':        (value >> 278) & 0x1,
        'state':           (value >> 275) & 0x7,
        'addr':            (value >> 243) & 0xFFFFFFFF,
        'id':              (value >> 235) & 0xFF,
        'len':             (value >> 227) & 0xFF,
        'size':            (value >> 224) & 0x7,
        'burst':           (value >> 222) & 0x3,
        'channel':         (value >> 216) & 0x3F,
        'addr_timer':      (value >> 184) & 0xFFFFFFFF,
        'data_timer':      (value >> 152) & 0xFFFFFFFF,
        'resp_timer':      (value >> 120) & 0xFFFFFFFF,
        'addr_timestamp':  (value >> 88)  & 0xFFFFFFFF,
        'data_timestamp':  (value >> 56)  & 0xFFFFFFFF,
        'resp_timestamp':  (value >> 24)  & 0xFFFFFFFF,
        'expected_beats':  (value >> 16)  & 0xFF,
        'data_beat_count': (value >> 8)   & 0xFF,
        'event_code':      (value >> 0)   & 0xFF,
    }


# ----------------------------------------------------------------------------
# Stimulus generator -- deterministic given a fixed seed
# ----------------------------------------------------------------------------
def generate_inputs(rng: random.Random,
                    is_read: int,
                    is_axi: int,
                    id_space: int,
                    max_trans: int,
                    timestamp: int) -> Dict[str, int]:
    """One cycle of randomized inputs. Constrained ID space so collisions
    happen often enough to exercise the match logic; biased probabilities
    so all phases see fire on a typical cycle."""
    return {
        'cmd_valid':            int(rng.random() < 0.45),
        'cmd_ready':            int(rng.random() < 0.75),
        'cmd_id':               rng.randrange(0, id_space),
        'cmd_addr':             rng.randrange(0, 1 << 32),
        'cmd_len':              rng.randrange(0, 16),
        'cmd_size':             rng.randrange(0, 4),
        'cmd_burst':            rng.randrange(0, 3),
        'data_valid':           int(rng.random() < 0.55),
        'data_ready':           int(rng.random() < 0.75),
        'data_id':              rng.randrange(0, id_space),
        'data_last':            int(rng.random() < 0.20),
        'data_resp':            rng.randrange(0, 4),
        'resp_valid':           int((not is_read) and (rng.random() < 0.35)),
        'resp_ready':           int(rng.random() < 0.75),
        'resp_id':              rng.randrange(0, id_space),
        'resp_code':            rng.randrange(0, 4),
        'timestamp':            timestamp,
        'event_reported_flags': rng.randrange(0, 1 << max_trans),
    }


# ----------------------------------------------------------------------------
# Testbench
# ----------------------------------------------------------------------------
class TransMgrEquivTB(TBBase):
    """Drives the trans_mgr with deterministic random stimulus and either
    captures or compares per-cycle output snapshots."""

    def __init__(self, dut):
        super().__init__(dut)

        self.MODE          = os.environ.get('TRANS_MGR_MODE', 'capture')
        self.CAPTURE_PATH  = os.environ['TRANS_MGR_CAPTURE_PATH']
        self.MAX_TRANS     = int(os.environ.get('PARAM_MAX_TRANS', '16'))
        self.ID_WIDTH      = int(os.environ.get('PARAM_ID_WIDTH',  '8'))
        self.IS_READ       = int(os.environ.get('PARAM_IS_READ',   '1'))
        self.IS_AXI        = int(os.environ.get('PARAM_IS_AXI',    '1'))
        self.STIM_CYCLES   = int(os.environ.get('STIM_CYCLES',     '500'))
        self.STIM_SEED     = int(os.environ.get('STIM_SEED',       '42'))
        self.ID_SPACE      = min(8, 1 << self.ID_WIDTH)

        self.snapshots: List[dict] = []
        if self.MODE == 'compare':
            with open(self.CAPTURE_PATH, 'r') as f:
                self.expected = json.load(f)
            self.log.info(
                f"compare mode: loaded {len(self.expected)} cycles from "
                f"{self.CAPTURE_PATH}"
            )

        self.log.info(
            f"TransMgrEquivTB: MODE={self.MODE}, IS_READ={self.IS_READ}, "
            f"IS_AXI={self.IS_AXI}, MAX_TRANS={self.MAX_TRANS}, "
            f"ID_WIDTH={self.ID_WIDTH}, STIM_CYCLES={self.STIM_CYCLES}, "
            f"STIM_SEED={self.STIM_SEED}, ID_SPACE={self.ID_SPACE}"
        )

    # ------------------------------------------------------------------

    def _drive_idle(self):
        self.dut.cmd_valid.value             = 0
        self.dut.cmd_ready.value             = 0
        self.dut.cmd_id.value                = 0
        self.dut.cmd_addr.value              = 0
        self.dut.cmd_len.value               = 0
        self.dut.cmd_size.value              = 0
        self.dut.cmd_burst.value             = 0
        self.dut.data_valid.value            = 0
        self.dut.data_ready.value            = 0
        self.dut.data_id.value               = 0
        self.dut.data_last.value             = 0
        self.dut.data_resp.value             = 0
        self.dut.resp_valid.value            = 0
        self.dut.resp_ready.value            = 0
        self.dut.resp_id.value               = 0
        self.dut.resp_code.value             = 0
        self.dut.timestamp.value             = 0
        self.dut.i_event_reported_flags.value = 0

    def _drive_inputs(self, inp: Dict[str, int]):
        self.dut.cmd_valid.value             = inp['cmd_valid']
        self.dut.cmd_ready.value             = inp['cmd_ready']
        self.dut.cmd_id.value                = inp['cmd_id']
        self.dut.cmd_addr.value              = inp['cmd_addr']
        self.dut.cmd_len.value               = inp['cmd_len']
        self.dut.cmd_size.value              = inp['cmd_size']
        self.dut.cmd_burst.value             = inp['cmd_burst']
        self.dut.data_valid.value            = inp['data_valid']
        self.dut.data_ready.value            = inp['data_ready']
        self.dut.data_id.value               = inp['data_id']
        self.dut.data_last.value             = inp['data_last']
        self.dut.data_resp.value             = inp['data_resp']
        self.dut.resp_valid.value            = inp['resp_valid']
        self.dut.resp_ready.value            = inp['resp_ready']
        self.dut.resp_id.value               = inp['resp_id']
        self.dut.resp_code.value             = inp['resp_code']
        self.dut.timestamp.value             = inp['timestamp']
        self.dut.i_event_reported_flags.value = inp['event_reported_flags']

    async def reset_dut(self):
        self._drive_idle()
        self.dut.aresetn.value = 0
        await self.wait_clocks('aclk', 6)
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 2)

    # ------------------------------------------------------------------

    def _snapshot_trans_table(self) -> List[Dict[str, int]]:
        """Read trans_table[i] for every slot, decode the packed bus_
        transaction_t into a field dict. Must be called inside ReadOnly."""
        snap = []
        for i in range(self.MAX_TRANS):
            raw = int(self.dut.trans_table[i].value)
            snap.append(decode_bus_transaction(raw))
        return snap

    def _snapshot(self, cycle: int) -> dict:
        return {
            'cycle':        cycle,
            'trans_table':  self._snapshot_trans_table(),
            'active_count': int(self.dut.active_count.value),
            'state_change': int(self.dut.state_change.value),
        }

    def _check_against_expected(self, cycle: int, snap: dict):
        if cycle >= len(self.expected):
            raise AssertionError(
                f"compare mode: ran past end of capture at cycle {cycle} "
                f"(capture has {len(self.expected)} cycles)"
            )
        exp = self.expected[cycle]
        if snap == exp:
            return
        # Detailed mismatch report
        diffs = []
        if snap['active_count'] != exp['active_count']:
            diffs.append(
                f"  active_count: stage={snap['active_count']} "
                f"prod={exp['active_count']}"
            )
        if snap['state_change'] != exp['state_change']:
            diffs.append(
                f"  state_change: stage=0x{snap['state_change']:0x} "
                f"prod=0x{exp['state_change']:0x}"
            )
        for i, (s_e, p_e) in enumerate(zip(snap['trans_table'], exp['trans_table'])):
            if s_e == p_e:
                continue
            field_diffs = [
                f"{k}: stage=0x{s_e[k]:x} prod=0x{p_e[k]:x}"
                for k in s_e
                if s_e[k] != p_e[k]
            ]
            diffs.append(f"  trans_table[{i}]: " + ", ".join(field_diffs))
        msg = (f"trans_mgr mismatch at cycle {cycle}:\n"
               + "\n".join(diffs[:10]))
        if len(diffs) > 10:
            msg += f"\n  ... and {len(diffs)-10} more"
        raise AssertionError(msg)

    # ------------------------------------------------------------------

    async def run_random_stress(self):
        rng = random.Random(self.STIM_SEED)
        timestamp = 0

        for cycle in range(self.STIM_CYCLES):
            inp = generate_inputs(
                rng,
                is_read   = self.IS_READ,
                is_axi    = self.IS_AXI,
                id_space  = self.ID_SPACE,
                max_trans = self.MAX_TRANS,
                timestamp = timestamp,
            )
            self._drive_inputs(inp)
            # Sample at ReadOnly BEFORE the next rising edge -- this is
            # the trans_table state AFTER the previous cycle's edge.
            await ReadOnly()
            snap = self._snapshot(cycle)
            if self.MODE == 'compare':
                self._check_against_expected(cycle, snap)
            self.snapshots.append(snap)

            # Advance the clock so the just-driven inputs latch.
            await RisingEdge(self.dut.aclk)
            timestamp = (timestamp + 1) & 0xFFFFFFFF

        self._drive_idle()

        if self.MODE == 'capture':
            with open(self.CAPTURE_PATH, 'w') as f:
                json.dump(self.snapshots, f)
            self.log.info(
                f"capture mode: wrote {len(self.snapshots)} cycles to "
                f"{self.CAPTURE_PATH}"
            )
        else:
            self.log.info(
                f"compare mode: {len(self.snapshots)} cycles all matched"
            )


# ----------------------------------------------------------------------------
# Cocotb test entry
# ----------------------------------------------------------------------------
@cocotb.test(timeout_time=60, timeout_unit="ms")
async def axi_monitor_trans_mgr_equiv_test(dut):
    tb = TransMgrEquivTB(dut)
    await tb.start_clock('aclk', 10, 'ns')
    await tb.reset_dut()
    await tb.run_random_stress()
    tb.log.info("=== ALL CYCLES PASSED ===")


# ----------------------------------------------------------------------------
# RTL source lists -- the only difference between prod and stage
# ----------------------------------------------------------------------------
def _common_sources():
    """Sources required by every trans_mgr build (packages, includes)."""
    return [
        "rtl/amba/includes/monitor_common_pkg.sv",
        "rtl/amba/includes/monitor_arbiter_pkg.sv",
        "rtl/amba/includes/monitor_amba4_pkg.sv",
        "rtl/amba/includes/monitor_amba5_pkg.sv",
        "rtl/amba/includes/monitor_pkg.sv",
    ]


def _prod_sources():
    return _common_sources() + [
        "rtl/amba/shared/axi_monitor_trans_mgr.sv",
    ]


def _stage_sources():
    return _common_sources() + [
        "rtl/amba/shared/monitor_trans_cam.sv",
        "rtl/amba/shared/mon_temp/axi_monitor_trans_mgr.sv",
    ]


# ----------------------------------------------------------------------------
# Shared pytest helper
# ----------------------------------------------------------------------------
def _run_trans_mgr(*,
                   variant: str,             # 'prod' or 'stage'
                   mode: str,                # 'capture' or 'compare'
                   is_read: int,
                   is_axi: int,
                   max_trans: int,
                   id_width: int,
                   stim_cycles: int,
                   stim_seed: int):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_shared':   'rtl/amba/shared',
        'rtl_includes': 'rtl/amba/includes',
    })

    dut_name = "axi_monitor_trans_mgr"
    flavor = f"{variant}_{'rd' if is_read else 'wr'}_{'axi4' if is_axi else 'axil'}"
    test_name = (f"test_{dut_name}_equiv_{flavor}_mt{max_trans:02d}"
                 f"_iw{id_width:02d}_sc{stim_cycles:04d}_seed{stim_seed}")
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    log_path  = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    sources_rel = _prod_sources() if variant == 'prod' else _stage_sources()
    verilog_sources = [os.path.join(repo_root, s) for s in sources_rel]
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    capture_path = CAPTURE_DIR / _capture_filename(
        is_read=is_read, is_axi=is_axi, max_trans=max_trans,
        id_width=id_width, stim_cycles=stim_cycles, seed=stim_seed,
    )

    rtl_parameters = {
        'MAX_TRANSACTIONS': str(max_trans),
        'ID_WIDTH':         str(id_width),
        'IS_READ':          str(is_read),
        'IS_AXI':           str(is_axi),
    }

    extra_env = {
        'DUT':                    dut_name,
        'LOG_PATH':               log_path,
        'COCOTB_LOG_LEVEL':       'INFO',
        'COCOTB_RESULTS_FILE':    os.path.join(log_dir, f'results_{test_name}.xml'),
        'TRANS_MGR_MODE':         mode,
        'TRANS_MGR_CAPTURE_PATH': str(capture_path),
        'PARAM_MAX_TRANS':        str(max_trans),
        'PARAM_ID_WIDTH':         str(id_width),
        'PARAM_IS_READ':          str(is_read),
        'PARAM_IS_AXI':           str(is_axi),
        'STIM_CYCLES':            str(stim_cycles),
        'STIM_SEED':              str(stim_seed),
    }

    compile_args = [
        '+define+SIMULATION',
        '--trace-fst', '--trace-structs',
        '-Wno-DECLFILENAME', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC',
        '-Wno-UNUSEDPARAM',  '-Wno-UNUSEDSIGNAL', '-Wno-TIMESCALEMOD',
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_includes'], rtl_dict['rtl_shared'], sim_build],
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
        )
    except Exception as e:
        print(f"Test failed: {e}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise


# ----------------------------------------------------------------------------
# Parameter sweep
# ----------------------------------------------------------------------------
def get_equiv_params():
    """REG_LEVEL gates the (IS_READ, IS_AXI, MAX_TRANS, ID_WIDTH) sweep.

    The two key real-world configurations:
      * AXI4 read   (IS_READ=1, IS_AXI=1) -- the most common monitor
      * AXI4 write  (IS_READ=0, IS_AXI=1) -- exercises the WID-less
        write data-channel match (the only behavior the staging file
        cannot get from the CAM directly, so the most interesting
        differential coverage)

    FUNC sweeps both; FULL adds the AXI-Lite variants.
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [(1, 1, 16, 8)]
    elif reg_level == 'FUNC':
        return [
            (1, 1, 16, 8),
            (0, 1, 16, 8),
        ]
    else:  # FULL
        return [
            (1, 1, 16, 8),
            (0, 1, 16, 8),
            (1, 0, 16, 8),
            (0, 0, 16, 8),
            (1, 1,  8, 4),
            (0, 1,  8, 4),
        ]


# ----------------------------------------------------------------------------
# Pytest entries -- alphabetical order ensures prod runs before stage.
# ----------------------------------------------------------------------------
@pytest.mark.parametrize("is_read, is_axi, max_trans, id_width", get_equiv_params())
def test_a_axi_monitor_trans_mgr_prod(request, is_read, is_axi, max_trans, id_width):
    """Run the random stress against the production trans_mgr, capture
    cycle-by-cycle outputs to JSON for the stage test to compare against."""
    stim_cycles = int(os.environ.get('STIM_CYCLES', '500'))
    stim_seed   = int(os.environ.get('STIM_SEED',   '42'))
    _run_trans_mgr(
        variant     = 'prod',
        mode        = 'capture',
        is_read     = is_read,
        is_axi      = is_axi,
        max_trans   = max_trans,
        id_width    = id_width,
        stim_cycles = stim_cycles,
        stim_seed   = stim_seed,
    )


@pytest.mark.parametrize("is_read, is_axi, max_trans, id_width", get_equiv_params())
def test_b_axi_monitor_trans_mgr_stage(request, is_read, is_axi, max_trans, id_width):
    """Run the same stimulus against the CAM-backed staging trans_mgr,
    asserting every cycle's snapshot is bit-identical to the production
    capture. Requires test_a_axi_monitor_trans_mgr_prod to have run first
    (pytest collects in source order by default, and the alphabetical
    a/b prefix makes that explicit)."""
    stim_cycles = int(os.environ.get('STIM_CYCLES', '500'))
    stim_seed   = int(os.environ.get('STIM_SEED',   '42'))
    _run_trans_mgr(
        variant     = 'stage',
        mode        = 'compare',
        is_read     = is_read,
        is_axi      = is_axi,
        max_trans   = max_trans,
        id_width    = id_width,
        stim_cycles = stim_cycles,
        stim_seed   = stim_seed,
    )

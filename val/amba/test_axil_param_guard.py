# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axil_param_guard
# Purpose: AXI-Lite elaboration-time parameter guards (issue #102 item 6)
#
# Subsystem: tests

"""AXI4-Lite / AXI5-Lite parameter guards: illegal widths must not build.

Every ``rtl/amba/axil4`` and ``rtl/amba/axil5`` module carries an
elaboration-time ``param_check`` (the one sanctioned in-RTL check form, see
``vault/handbook/design/no-assertions-in-rtl.md``):

* AXI4-Lite ``AXIL_DATA_WIDTH`` must be 32 or 64 (IHI 0022H B1.1.2).
* AXI5-Lite ``AXIL_DATA_WIDTH`` must be an AXI data width, 8..1024 and a power
  of two (IHI 0022L Table A3.19; Table B2.4 adds no AXI5-Lite restriction).
* AXI5-Lite ``ID_WIDTH`` is 0..32 (Table A5.2), and at least 1 on the
  slave-side (Subordinate) modules, where Table B2.2 makes the ID mandatory.

Before issue #102 the width accepted any value and a 48-bit AXI4-Lite bus
built and simulated silently. Each NEGATIVE case below builds a module with an
illegal value and requires the simulation to stop at time 0 with that
module's own ``param_check`` message -- the message names the module, so a
wrapper whose own guard was missing would not be rescued by the guard of the
module it instantiates. Each POSITIVE case builds a legal-but-unusual value
(AXI5-Lite at 8 and 128 bits, a Manager-side AXI5-Lite module with no ID) and
requires the smoke test to pass, so the guard is not simply rejecting
everything.

Levels: GATE checks the four base modules of each family; FUNC adds the
clock-gated wrappers and one monitor and one monitor-lite wrapper per family;
FULL checks all 48 modules.
"""

import os

import cocotb
import pytest
from cocotb.triggers import Timer
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def axil_param_guard_smoke(dut):
    """Reached only when elaboration passed: let time advance and stop."""
    await Timer(100, unit="ns")


_KINDS_GATE = ['master_rd', 'master_wr', 'slave_rd', 'slave_wr']
_KINDS_FUNC = _KINDS_GATE + [k + '_cg' for k in _KINDS_GATE] + \
    ['slave_rd_mon', 'master_wr_monlite']
_KINDS_FULL = [f"{k}{sfx}" for k in _KINDS_GATE
               for sfx in ('', '_cg', '_mon', '_mon_cg', '_monlite',
                           '_monlite_cg')]


def _modules():
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    kinds = {'GATE': _KINDS_GATE, 'FUNC': _KINDS_FUNC}.get(reg_level,
                                                           _KINDS_FULL)
    return [f"{fam}_{k}" for fam in ('axil4', 'axil5') for k in kinds]


def generate_guard_params():
    """(module, overrides, expect_fatal_substring or None)."""
    params = []
    for mod in _modules():
        params.append((mod, {'AXIL_DATA_WIDTH': 48},
                       f"{mod}: AXIL_DATA_WIDTH=48"))
        if mod.startswith('axil4_'):
            # 128 is a legal AXI DATA_WIDTH but not a legal AXI4-Lite one.
            params.append((mod, {'AXIL_DATA_WIDTH': 128},
                           f"{mod}: AXIL_DATA_WIDTH=128"))
        else:
            params.append((mod, {'ID_WIDTH': 33}, f"{mod}: ID_WIDTH=33"))
            if '_slave_' in mod:
                params.append((mod, {'ID_WIDTH': 0}, f"{mod}: ID_WIDTH=0"))
    # Legal corner values must still build and run.
    params += [
        ('axil5_slave_rd', {'AXIL_DATA_WIDTH': 8}, None),
        ('axil5_slave_wr', {'AXIL_DATA_WIDTH': 128}, None),
        ('axil5_master_rd', {'ID_WIDTH': 0}, None),
        ('axil5_master_wr', {'ID_WIDTH': 0}, None),
        ('axil4_slave_rd', {'AXIL_DATA_WIDTH': 64}, None),
        # amba #104: the full monitor now sees the AXI5-Lite ID and keys on at
        # most 8 bits, so a wider ID is refused on _mon and still fine on the
        # lite; ID_WIDTH=0 on a Manager-side monitor must still build.
        ('axil5_master_wr_mon', {'ID_WIDTH': 12},
         "axil5_master_wr_mon: ID_WIDTH=12 -- the full ocelus tracks at most 8 ID bits"),
        ('axil5_slave_rd_mon', {'ID_WIDTH': 9},
         "axil5_slave_rd_mon: ID_WIDTH=9 -- the full ocelus tracks at most 8 ID bits"),
        ('axil5_master_rd_mon', {'ID_WIDTH': 0}, None),
        ('axil5_slave_wr_monlite', {'ID_WIDTH': 12}, None),
    ]
    return params


def _param_id(p):
    mod, over, want = p
    tag = '_'.join(f"{k.lower()}{v}" for k, v in over.items())
    return f"{mod}-{tag}-{'fatal' if want else 'ok'}"


_PARAMS = generate_guard_params()


@pytest.mark.parametrize("dut_name, overrides, expect_fatal", _PARAMS,
                         ids=[_param_id(p) for p in _PARAMS])
def test_axil_param_guard(request, caplog, dut_name, overrides, expect_fatal):
    """Build ``dut_name`` with ``overrides``; check the guard's verdict."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, _ = get_paths({
        'rtl_amba_includes': 'rtl/amba/includes'})

    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    tag = '_'.join(f"{k.lower()}{v}" for k, v in overrides.items())
    name = f"test_{worker_id}_guard_{dut_name}_{tag}_{reg_level}"
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, module=dut_name)

    extra_env = {
        'LOG_PATH': os.path.join(log_dir, f'{name}.log'),
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
        'DUT': dut_name,
    }
    kwargs = dict(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="axil_param_guard_smoke",
        parameters={k: str(v) for k, v in overrides.items()},
        sim_build=sim_build,
        extra_env=extra_env,
        waves=False,
        keep_files=True,
        compile_args=["-Wno-fatal", "-Werror-MULTIDRIVEN", FIELD_COMBO_VLT, "-DUSE_ASYNC_RESET"],
    )

    if expect_fatal is None:
        run(**kwargs)
        return

    # cocotb_test relays the simulator's output through the 'cocotb' logger.
    caplog.set_level('INFO')
    with pytest.raises(BaseException):
        run(**kwargs)
    text = caplog.text
    # Verilator runs the TOP module's initial block first, so a wrapper's own
    # guard is the one that reports; were the wrapper's guard missing, the
    # inner module's message (naming the inner module) would appear instead
    # and this check would fail.
    assert 'param_check' in text and expect_fatal in text, (
        f"{dut_name} with {overrides} failed, but not with its own "
        f"param_check message '{expect_fatal}'. Output tail:\n{text[-2000:]}")


def test_every_axil_module_carries_its_own_guard():
    """Static sweep over all 48 modules: each has a ``param_check`` naming
    itself, checking AXIL_DATA_WIDTH (and ID_WIDTH on AXI5-Lite), under
    ``ifndef SYNTHESIS``. The simulated cases above cover a subset per level;
    this makes sure the mechanical edit reached every file."""
    import glob
    import re
    repo = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
    files = sorted(glob.glob(os.path.join(repo, 'rtl/amba/axil4/*.sv')) +
                   glob.glob(os.path.join(repo, 'rtl/amba/axil5/*.sv')))
    assert len(files) == 48, f"expected 48 axil4/axil5 modules, found {len(files)}"
    missing = []
    for f in files:
        src = open(f).read()
        mod = re.search(r'^module\s+(\w+)', src, re.M).group(1)
        block = re.search(r'`ifndef SYNTHESIS\s*\n\s*initial begin : param_check(.*?)\n\s*end\s*\n`endif',
                          src, re.S)
        ok = (block is not None and f'"{mod}: AXIL_DATA_WIDTH=' in block.group(1)
              and (mod.startswith('axil4_') or f'"{mod}: ID_WIDTH=' in block.group(1)))
        if not ok:
            missing.append(mod)
    assert not missing, f"modules without their own param_check: {missing}"

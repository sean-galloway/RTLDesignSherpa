# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_dma_slave_monitors
# Purpose: FUB validation of dma_slave_monitors — drive the wrapper's AXI4 slave
#          interface with an AXI4 master BFM and confirm the slave monitors
#          observe the traffic and emit decodable monbus packets on the group's
#          bulk-trace master-write port.
#
# NOT a tally test: the tally memories live one level up in stream_harness
# (they moved out of this wrapper), so the contract checked here is the one this
# module actually owns -- packets on m_axil_*. The tally itself is covered by
# val/amba/test_monbus_pkt_tally.py and the harness cosim.
#
# Pattern B (projects/): cocotb_test_* + pytest wrapper.

import os
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_dma_slave_monitors(dut):
    """Drive AXI reads+writes through the wrapper; the monitors must emit."""
    # Load the TB by explicit FILE PATH, not "import tbclasses.*".
    #
    # TWO directories in this area are named `tbclasses`: the COMPONENT one
    # (<area>/dv/tbclasses, holding the shared StreamHarnessTB) and this build's
    # own (<area>/build-mon/dv/tbclasses, holding only this file's TB). Both end
    # up on sys.path -- the area conftest adds the first, the build conftest the
    # second -- so a plain `import tbclasses.dma_slave_monitors_tb` resolves to
    # whichever landed first and this module vanishes.
    #
    # That is not hypothetical: the same shape, when the competing `tbclasses`
    # was the pre-migration perf flow's, made this test PASS when run alone and
    # FAIL in a directory run, because pytest imports the sibling test during
    # collection and that import reordered sys.path. A file path cannot be
    # shadowed.
    import importlib.util as _ilu
    _tb_py = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                          '..', 'tbclasses', 'dma_slave_monitors_tb.py')
    _spec = _ilu.spec_from_file_location('dma_slave_monitors_tb',
                                         os.path.abspath(_tb_py))
    _m = _ilu.module_from_spec(_spec)
    _spec.loader.exec_module(_m)
    DmaSlaveMonitorsTB, PKT_COMPLETION = _m.DmaSlaveMonitorsTB, _m.PKT_COMPLETION

    N_WR, N_RD, BLEN = 8, 8, 4
    tb = DmaSlaveMonitorsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_traffic(n_writes=N_WR, n_reads=N_RD, burst_len=BLEN)

    # 1. The traffic really reached the slaves (DUT's own beat counters).
    rd_beats, wr_beats = tb.beat_counts()
    tb.log.info(f"[dma_slave_monitors] beats observed: rd={rd_beats} wr={wr_beats}")
    assert rd_beats >= N_RD * BLEN, (
        f"read beat count {rd_beats} < the {N_RD * BLEN} beats driven — traffic "
        f"never reached the monitored slaves")
    assert wr_beats >= N_WR * BLEN, (
        f"write beat count {wr_beats} < the {N_WR * BLEN} beats driven — traffic "
        f"never reached the monitored slaves")

    # 2. The monitors turned that traffic into monbus packets on m_axil_*.
    pkts = tb.packets()
    kinds = {}
    for p in pkts:
        kinds[getattr(p, 'packet_type', None)] = kinds.get(getattr(p, 'packet_type', None), 0) + 1
    tb.log.info(f"[dma_slave_monitors] {len(pkts)} packets decoded, by type: {kinds}")
    assert pkts, (
        "no monbus packets on the bulk-trace port — the slave-monitor -> "
        "monbus_arbiter -> monbus_axil_axil_group -> m_axil_* path emitted nothing")

    # 3. Completions specifically: every burst that retires should report one.
    n_compl = sum(n for k, n in kinds.items()
                  if k is not None and int(k) == PKT_COMPLETION)
    assert n_compl > 0, (
        f"packets emitted ({len(pkts)}) but none were COMPLETION (type "
        f"{PKT_COMPLETION}); saw types {sorted(k for k in kinds if k is not None)}")


# ----------------------------------------------------------------------------
def test_dma_slave_monitors(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba_shared':  'rtl/amba/shared',
        'rtl_amba_monitor': 'rtl/amba/monitor',
        'rtl_amba_inc':     'rtl/amba/includes',
    })
    dut_name = "dma_slave_monitors"
    dv_dir = os.path.abspath(os.path.join(tests_dir, '..'))  # flows-stream-monitor/dv
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name = f"test_{worker_id}_{dut_name}"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/misc/rtl/filelists/dma_slave_monitors.f")
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # Small config: 1 channel, 64-bit data (axi4_dma_slaves default).
    # NOTE: no TALLY_* overrides here -- dma_slave_monitors wraps the DMA slaves
    # and their monbus group only. The tally memories live one level up in
    # stream_harness, so passing TALLY_* here is a hard Verilator error
    # ("Parameters from the command line were not found in the design").
    rtl_parameters = {
        'NUM_CHANNELS': '1', 'AXI_ID_WIDTH': '8', 'AXI_ADDR_WIDTH': '32',
        'AXI_DATA_WIDTH': '64', 'AXI_USER_WIDTH': '1', 'MAX_TRANSACTIONS': '16',
    }
    extra_env = {
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'PARAM_AXI_ID_WIDTH': '8', 'PARAM_AXI_ADDR_WIDTH': '32',
        'PARAM_AXI_DATA_WIDTH': '64', 'PARAM_AXI_USER_WIDTH': '1',
    }
    compile_args = [
        '+define+SIMULATION', '-Wno-DECLFILENAME', '-Wno-WIDTHEXPAND',
        '-Wno-WIDTHTRUNC', '-Wno-UNUSEDPARAM', '-Wno-TIMESCALEMOD',
        '-Wno-UNUSEDSIGNAL', '-Wno-PINCONNECTEMPTY',
        # The monbus group's optional status outputs (fifo counts/full,
        # compressor tier stats) are deliberately left open in
        # dma_slave_monitors -- same suppression the sibling flow tests use.
        '-Wno-PINMISSING',
    ]
    create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    run(
        python_search=[tests_dir, dv_dir],
        verilog_sources=verilog_sources,
        includes=includes + [rtl_dict['rtl_amba_shared'], sim_build],
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_dma_slave_monitors",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        keep_files=True,
        compile_args=compile_args,
    )

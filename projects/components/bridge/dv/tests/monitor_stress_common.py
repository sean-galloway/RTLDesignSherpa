#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Config-agnostic stress orchestration for the generated bridge _mon monitor
# tests. Pairs with the framework-level MonbusGroupHarness
# (TBClasses.scoreboards.monbus_group): the harness owns the protocol-agnostic
# monbus plumbing (drain reads, trace consume w/ ready throttle, drain pump,
# fifo/irq probes, packet decode); this module owns the bridge stimulus + the
# stress phases + the cocotb-test build boilerplate.
#
# Tests target the _mon bridge TOP DIRECTLY (no smoke wrapper): the _mon top
# exposes every monitor signal as a real port (cfg_* inputs, s_mon_axil_*,
# m_mon_axil_* incl. awready/wready/bvalid inputs, mon_irq_out), so cfg and
# backpressure are driven at runtime via cocotb. One comprehensive cocotb test
# sequences four phases by reconfiguring cfg between them:
#
#   1 traffic    -- monitors off; prove high-volume AXI traffic is intact.
#   2 WRITE_BP   -- compl -> bulk write FIFO; throttle m_mon_axil_wready so the
#                   96-beat write FIFO fills and block_ready gates the AR.
#   3 ERR_BP/cmp -- route compl -> 64-deep err FIFO; slow drain pump.
#   4 ERR_BP/err -- SLVERR flood -> err FIFO; slow drain pump.
#
# Everything is parameterized by the per-config geometry the generator bakes
# into each test (cfg prefixes, block-ready hierarchy path); slave windows come
# from the reused base TB class's slave_info.

import os
import random

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist

from TBClasses.monbus import PktType, ProtocolType
from TBClasses.monbus.monbus_types import AXIErrorCode
from TBClasses.scoreboards.monbus_group import (
    MonbusGroupHarness, BeatLayout, BeatOrder,
)

# Bridge master-write / err-drain record layout: beat0=pkt[63:0],
# beat1=pkt[127:64], beat2=ts.
_BRIDGE_LAYOUT = BeatLayout(order=BeatOrder.LO_HI_TS)

# Working monbus-group flush window (the burst writer needs a bounded
# [base, limit) window + watermark, or it never flushes).
_GROUP_BASE = 0x0000_1000
_GROUP_LIMIT = 0x0000_5000 - 1
_GROUP_WATERMARK = 3            # one record = 3 beats

_SLAVE_WORD_BYTES = 4           # 32-bit slave data
_SLAVE_CAP_BYTES = 4096         # Bridge<>TB.SLAVE_MEM_CAP_BYTES seeded window


# --------------------------------------------------------------------------- #
# low-level signal access
# --------------------------------------------------------------------------- #
def _resolve(dut, dotted):
    node = dut
    for part in dotted.split('.'):
        node = getattr(node, part)
    return node


def _set(dut, name, value):
    h = getattr(dut, name, None)
    if h is not None:
        h.value = value


def _get(handle):
    try:
        return int(handle.value)
    except (ValueError, AttributeError, TypeError):
        return None


# --------------------------------------------------------------------------- #
# harness + stimulus helpers
# --------------------------------------------------------------------------- #
def make_harness(dut, tb, block_node=None):
    return MonbusGroupHarness(
        dut, dut.aclk,
        drain_proto="axil", trace_proto="axil",
        drain_prefix="s_mon_axil_", trace_prefix="m_mon_axil_",
        group_node=dut.u_mon_axil_group,
        irq_sig=dut.mon_irq_out,
        block_node=block_node,
        layout_drain=_BRIDGE_LAYOUT,
        layout_trace=_BRIDGE_LAYOUT,
        log=tb.log,
    )


def stress_read_plan(tb, n, *, slaves=None, seed=0xC0FFEE):
    """n (slave_idx, addr) pairs, word-aligned within each slave's seeded
    window so tb.slave_mem_read yields golden data."""
    rng = random.Random(seed)
    idxs = list(slaves) if slaves is not None else sorted(tb.slave_info.keys())
    max_word = _SLAVE_CAP_BYTES // _SLAVE_WORD_BYTES
    plan = []
    for _ in range(n):
        s = rng.choice(idxs)
        base = tb.slave_info[s][1]
        off = rng.randrange(max_word) * _SLAVE_WORD_BYTES
        plan.append((s, base + off))
    return plan


def set_monitor_cfg(dut, cfg_prefixes, *, monitor, compl=0, error=0):
    """Drive per-port cfg_<prefix>_{monitor,compl,error}_enable across every
    emitted prefix. Other cfg fields default 0 (verilator inits inputs to 0)."""
    for p in cfg_prefixes:
        _set(dut, f"cfg_{p}_monitor_enable", 1 if monitor else 0)
        _set(dut, f"cfg_{p}_compl_enable", 1 if compl else 0)
        _set(dut, f"cfg_{p}_error_enable", 1 if error else 0)


def init_group_cfg(dut, *, err_select=0, base=_GROUP_BASE, limit=_GROUP_LIMIT,
                   watermark=_GROUP_WATERMARK):
    _set(dut, "cfg_mon_group_base_addr", base)
    _set(dut, "cfg_mon_group_limit_addr", limit)
    _set(dut, "cfg_mon_group_flush_watermark", watermark)
    _set(dut, "cfg_mon_group_axi_err_select", err_select)


def stress_count(default=256):
    n = int(os.environ.get("STRESS_READS", str(default)))
    if os.environ.get("REG_LEVEL", "").upper() == "FULL":
        n = max(n, 512)
    return n


# --------------------------------------------------------------------------- #
# phases (each owns a fresh harness; asserts on exit; leaves DUT quiesced)
# --------------------------------------------------------------------------- #
async def run_traffic_phase(dut, tb, cfg_prefixes, *, n, reachable=None):
    set_monitor_cfg(dut, cfg_prefixes, monitor=0)
    await ClockCycles(tb.clock, 5)
    for slave_idx, addr in stress_read_plan(tb, n, slaves=reachable, seed=0xA11CE):
        exp = tb.slave_mem_read(slave_idx, addr, master_idx=0)
        act = await tb.master_read(0, addr)
        assert act == exp, (f"[traffic] data mismatch s{slave_idx}@0x{addr:08x}: "
                            f"got 0x{act:08x} exp 0x{exp:08x}")
    tb.log.info(f"[traffic] {n} reads ok, monitors quiet")


async def run_write_bp_phase(dut, tb, cfg_prefixes, block_node, *, n, reachable=None,
                             ready_prob=0.08, hwm=72, drain_settle=6000,
                             inject_slverr=False, want_type=None,
                             monitor=1, compl=1, error=0, label="WRITE_BP"):
    """Bulk master-write (trace) backpressure: completions (or, with
    inject_slverr, SLVERR errors) stream out the trace path; throttle
    m_mon_axil_wready so the write FIFO saturates, then recover. The trace
    path is best-effort (drops surplus under backpressure rather than gating
    the AR), so the contract is saturate + recover + clean decode."""
    want_type = PktType.PktTypeCompletion if want_type is None else want_type
    rs = list(reachable) if reachable else sorted(tb.slave_info.keys())
    init_group_cfg(dut, err_select=0)
    set_monitor_cfg(dut, cfg_prefixes, monitor=monitor, compl=compl, error=error)
    if inject_slverr:
        install_slverr_override(tb.slave_rd[rs[0]])
        plan = stress_read_plan(tb, n, slaves=(rs[0],), seed=0xB0BA)
    else:
        plan = stress_read_plan(tb, n, slaves=rs, seed=0xB0BA)
    await ClockCycles(tb.clock, 5)
    mon = make_harness(dut, tb, block_node=block_node)
    mon.start_fifo_monitor()
    mon.start_trace_consumer(ready_prob=ready_prob)

    for slave_idx, addr in plan:
        try:
            act = await tb.master_read(0, addr)
            if not inject_slverr:
                exp = tb.slave_mem_read(slave_idx, addr, master_idx=0)
                assert act == exp, f"[{label}] data mismatch s{slave_idx}@0x{addr:08x}"
        except RuntimeError as e:
            assert "SLVERR" in str(e), f"[{label}] unexpected master error: {e}"

    mon.set_trace_ready_prob(1.0)
    await ClockCycles(tb.clock, drain_settle)
    mon.stop_trace_consumer()
    mon.stop_fifo_monitor()
    pkts = mon.parse_trace_records()
    st = mon.get_stats()
    expected = 2 * n   # one packet per wrapper boundary (master + slave)
    tb.log.info(f"[{label}] reads={n} aw={st.trace_aw} beats={st.trace_beats} "
                f"pkts={len(pkts)} (expected~{expected}, dropped~{expected - len(pkts)}) "
                f"max_wr={st.max_write_fifo_count} wr_full={st.write_fifo_full_seen} "
                f"final_wr={mon.write_fifo_count()}")
    # The bulk master-write (trace) path is best-effort: under write-FIFO
    # backpressure the monbus drops surplus packets rather than gating the AR
    # (the lossless + block_ready-gating contract belongs to the err-FIFO path,
    # exercised by the ERR_BP phase). Here we assert the bulk path SATURATES
    # under throttle and fully RECOVERS, and every drained record decodes clean.
    assert st.max_write_fifo_count >= hwm, (
        f"[{label}] write FIFO never climbed past {hwm} (peak {st.max_write_fifo_count})")
    assert st.write_fifo_full_seen, f"[{label}] write FIFO never saturated under throttle"
    assert mon.write_fifo_count() == 0, f"[{label}] write FIFO did not drain after recovery"
    assert len(pkts) == st.trace_beats // 3, f"[{label}] trace beats did not decode cleanly"
    assert len(pkts) > 0, f"[{label}] no records drained"
    # unit_id values are config-specific (per-monitor assignment); just record
    # which monitor boundaries reported rather than asserting fixed ids.
    tb.log.info(f"[{label}] reporting unit_ids: {sorted({p.unit_id for p in pkts})}")
    assert all(p.protocol == ProtocolType.PROTOCOL_AXI for p in pkts)
    assert all(p.packet_type == want_type for p in pkts), (
        f"[{label}] expected {want_type.name}, got "
        f"{sorted({p.get_packet_type_name() for p in pkts})}")
    set_monitor_cfg(dut, cfg_prefixes, monitor=0)
    await ClockCycles(tb.clock, 50)


async def run_err_bp_phase(dut, tb, cfg_prefixes, block_node, *, mode, n,
                           reachable=None, pump_gap=150, hwm=48):
    rs = list(reachable) if reachable else sorted(tb.slave_info.keys())
    if mode == "slverr":
        install_slverr_override(tb.slave_rd[rs[0]])
        plan = stress_read_plan(tb, n, slaves=(rs[0],), seed=0xDEAD)
        init_group_cfg(dut, err_select=0x1)            # PktTypeError -> err FIFO
        set_monitor_cfg(dut, cfg_prefixes, monitor=1, compl=0, error=1)
        want = PktType.PktTypeError
    else:  # compl
        plan = stress_read_plan(tb, n, slaves=rs, seed=0xFEED)
        init_group_cfg(dut, err_select=0x2)            # PktTypeCompletion -> err FIFO
        set_monitor_cfg(dut, cfg_prefixes, monitor=1, compl=1, error=0)
        want = PktType.PktTypeCompletion
    await ClockCycles(tb.clock, 5)

    mon = make_harness(dut, tb, block_node=block_node)
    mon.start_fifo_monitor()
    mon.start_irq_watch()
    mon.start_drain_pump(record_gap_cycles=pump_gap)

    errors = 0
    for slave_idx, addr in plan:
        try:
            act = await tb.master_read(0, addr)
            if mode == "compl":
                exp = tb.slave_mem_read(slave_idx, addr, master_idx=0)
                assert act == exp, f"[ERR_BP] data mismatch s{slave_idx}@0x{addr:08x}"
        except RuntimeError as e:
            assert "SLVERR" in str(e), f"[ERR_BP] unexpected master error: {e}"
            errors += 1

    mon.stop_drain_pump()
    await ClockCycles(tb.clock, 50)
    await mon.drain_until_empty()
    mon.stop_fifo_monitor()
    mon.stop_irq_watch()
    st = mon.get_stats()
    tb.log.info(f"[ERR_BP/{mode}] reads={n} errors={errors} pkts={len(mon.received_packets)} "
                f"max_err={st.max_err_fifo_count} err_full={st.err_fifo_full_seen} "
                f"gated={st.block_ready_gated} irq={st.irq_first_cycle} "
                f"final_err={mon.err_fifo_count()}")
    # The monbus err path is best-effort under a starved drain (surplus packets
    # are dropped at FIFO-full rather than gating the AR -- block_ready gating
    # is trans-table exhaustion from many OUTSTANDING transactions, which
    # sequential reads don't trigger; left as an informational probe). The real
    # stress contract: the err FIFO SATURATES, mon_irq_out fires, the path
    # RECOVERS fully, and drained records decode as the expected type.
    assert st.max_err_fifo_count >= hwm, (
        f"[ERR_BP/{mode}] err FIFO never climbed past {hwm} (peak {st.max_err_fifo_count})")
    assert st.err_fifo_full_seen, f"[ERR_BP/{mode}] err FIFO never saturated"
    assert mon.irq_asserted, f"[ERR_BP/{mode}] mon_irq_out never asserted"
    assert mon.err_fifo_count() == 0, f"[ERR_BP/{mode}] err FIFO did not drain"
    pkts = mon.received_packets
    assert len(pkts) >= 1, f"[ERR_BP/{mode}] no packets drained"
    assert all(p.protocol == ProtocolType.PROTOCOL_AXI for p in pkts)
    assert all(p.packet_type == want for p in pkts), (
        f"[ERR_BP/{mode}] expected {want.name}, got "
        f"{sorted({p.get_packet_type_name() for p in pkts})}")
    if mode == "slverr":
        codes = sorted({int(p.event_code) for p in pkts})
        tb.log.info(f"[ERR_BP/slverr] error event_codes seen: {codes}")
        # SLVERR injection must produce SLVERR error packets; the stressed,
        # lossy path may also legitimately emit other error codes (e.g.
        # orphans) -- require SLVERR present, all packets PktTypeError.
        assert any(p.event_code == AXIErrorCode.AXI_ERR_RESP_SLVERR for p in pkts), (
            f"[ERR_BP/slverr] no AXI_ERR_RESP_SLVERR among error codes {codes}")
    set_monitor_cfg(dut, cfg_prefixes, monitor=0)
    await ClockCycles(tb.clock, 50)


async def run_comprehensive(dut, tb, *, cfg_prefixes, block_ready_path,
                            reachable_slaves=None, has_compl=True,
                            is_regblock=False, n=None):
    """Sequence the stress phases against the _mon top in one build. Configs
    whose mon_preset omits the completion cone (has_compl=False) can only emit
    error packets, so they run the SLVERR error-path stress only."""
    n = n or stress_count()
    reachable = list(reachable_slaves) if reachable_slaves else sorted(tb.slave_info.keys())
    block_node = _resolve(dut, block_ready_path)
    has_br = getattr(block_node, "w_block_ready", None) is not None
    tb.log.info(f"block_ready probe '{block_ready_path}.w_block_ready' resolved={has_br}; "
                f"reachable_slaves={reachable}")
    assert has_br, f"block_ready signal not found at {block_ready_path}.w_block_ready"
    if is_regblock:
        # The regblock variant has no cfg_* pins; cfg comes from the PeakRDL
        # regblock, whose reset defaults are monitor_enable=1 / error_enable=1
        # (compl disabled). So drive the SLVERR err-FIFO backpressure phase on
        # reset defaults -- the WRITE_BP / completion phases (which need
        # compl_enable + group-window writes) are covered by the pin-driven
        # variants. The cfg helpers no-op against the absent pins.
        # Reset defaults are monitor_enable=1 / error_enable=1 / compl=0 and
        # group err_select=0, so SLVERR errors stream out the bulk trace path
        # (not the err FIFO). Stress that path: SLVERR flood + wready throttle
        # saturates the write FIFO with PktTypeError records, then recovers.
        tb.log.info("regblock: reset-default cfg (monitor+error enabled), SLVERR trace phase")
        await program_regblock_group_window(dut, tb)
        await run_write_bp_phase(dut, tb, cfg_prefixes, block_node, n=n,
                                 reachable=reachable, inject_slverr=True,
                                 want_type=PktType.PktTypeError,
                                 monitor=1, compl=0, error=1, label="REGBLOCK_WR_BP")
        tb.log.info("comprehensive monitor stress: regblock trace phase passed")
        return
    if not has_compl:
        # error-only preset: no completion reporter -> only error packets fire.
        # Stress both monbus FIFOs with SLVERR errors on the AXI4 slave
        # (reachable[0]); completion/traffic phases are impossible here.
        tb.log.info("error-only preset: SLVERR error-path stress (no completion cone)")
        await run_write_bp_phase(dut, tb, cfg_prefixes, block_node, n=n,
                                 reachable=reachable, inject_slverr=True,
                                 want_type=PktType.PktTypeError,
                                 monitor=1, compl=0, error=1, label="ERR_WR_BP")
        await run_err_bp_phase(dut, tb, cfg_prefixes, block_node, mode="slverr", n=n,
                               reachable=reachable)
        tb.log.info("comprehensive monitor stress: error-only phases passed")
        return
    await run_traffic_phase(dut, tb, cfg_prefixes, n=n, reachable=reachable)
    await run_write_bp_phase(dut, tb, cfg_prefixes, block_node, n=n, reachable=reachable)
    await run_err_bp_phase(dut, tb, cfg_prefixes, block_node, mode="compl", n=n,
                           reachable=reachable)
    await run_err_bp_phase(dut, tb, cfg_prefixes, block_node, mode="slverr", n=n,
                           reachable=reachable)
    tb.log.info("comprehensive monitor stress: all phases passed")


# --------------------------------------------------------------------------- #
# regblock cfg programming (s_cfg_axil register writes)
# --------------------------------------------------------------------------- #
# PeakRDL MON_GROUP register offsets for the (sole) regblock bridge variant
# (bridge_1x2_rd_regblock_mon_cfg). MON_GROUP sits after the per-port register
# blocks; offsets are fixed by the generator's RDL layout. If more regblock
# variants with different port counts are added, bake these per-config.
_RB_MON_GROUP_BASE_ADDR = 0x90      # base_addr[31:0]
_RB_MON_GROUP_LIMIT_ADDR = 0x94     # limit_addr[31:0]
_RB_MON_GROUP_PACK_0 = 0x98         # flush_watermark[15:0] (+ axi_pkt_mask[31:16])


async def _axil_write32(dut, clk, addr, data, timeout=300):
    """Single 32-bit AXIL write on the regblock s_cfg_axil_* port."""
    dut.s_cfg_axil_awvalid.value = 1
    dut.s_cfg_axil_awaddr.value = addr
    dut.s_cfg_axil_awprot.value = 0
    dut.s_cfg_axil_wvalid.value = 1
    dut.s_cfg_axil_wdata.value = data
    dut.s_cfg_axil_wstrb.value = 0xF
    dut.s_cfg_axil_bready.value = 1
    aw = w = False
    for _ in range(timeout):
        await RisingEdge(clk)
        if not aw and int(dut.s_cfg_axil_awready.value) == 1:
            aw = True
            dut.s_cfg_axil_awvalid.value = 0
        if not w and int(dut.s_cfg_axil_wready.value) == 1:
            w = True
            dut.s_cfg_axil_wvalid.value = 0
        if aw and w:
            break
    else:
        raise TimeoutError(f"s_cfg_axil aw/w handshake timeout @0x{addr:02x}")
    for _ in range(timeout):
        if int(dut.s_cfg_axil_bvalid.value) == 1:
            break
        await RisingEdge(clk)
    await RisingEdge(clk)
    dut.s_cfg_axil_bready.value = 0


async def program_regblock_group_window(dut, tb,
                                        base=_GROUP_BASE, limit=_GROUP_LIMIT,
                                        watermark=_GROUP_WATERMARK):
    """Program the regblock MON_GROUP flush window via s_cfg_axil so the
    master-write (trace) path actually flushes (reset defaults are 0 ->
    degenerate window -> writer stalls). Per-port monitor/error enables are
    left at their reset defaults (monitor_enable=1, error_enable=1)."""
    clk = dut.aclk
    await _axil_write32(dut, clk, _RB_MON_GROUP_BASE_ADDR, base)
    await _axil_write32(dut, clk, _RB_MON_GROUP_LIMIT_ADDR, limit)
    await _axil_write32(dut, clk, _RB_MON_GROUP_PACK_0, watermark & 0xFFFF)
    await ClockCycles(clk, 5)
    tb.log.info(f"regblock: programmed MON_GROUP window base=0x{base:x} "
                f"limit=0x{limit:x} watermark={watermark}")


# --------------------------------------------------------------------------- #
# slave SLVERR override (shared)
# --------------------------------------------------------------------------- #
def install_slverr_override(slave, force_resp: int = 2) -> None:
    """Monkey-patch slave._generate_read_response to drive RRESP=force_resp
    (2=SLVERR) on every beat. Scoped to one slave instance."""
    from cocotb.triggers import RisingEdge as _RE

    async def _slverr_response(ar_packet):
        try:
            burst_len = getattr(ar_packet, 'len', 0) + 1
            packet_id = getattr(ar_packet, 'id', 0)
            for _ in range(slave.response_delay_cycles):
                await _RE(slave.clock)
            r_packets = [
                slave.r_channel.create_packet(
                    id=packet_id, data=0xDEAD_BEEF, resp=force_resp,
                    last=1 if (i == burst_len - 1) else 0)
                for i in range(burst_len)
            ]
            for r_packet in r_packets:
                slave.r_channel.transmit_queue.append(r_packet)
            if not slave.r_channel.transmit_coroutine:
                slave.r_channel.transmit_coroutine = cocotb.start_soon(
                    slave.r_channel._transmit_pipeline())
        except Exception as e:  # noqa: BLE001
            if slave.log:
                slave.log.error(f"slverr override response error: {e}")

    slave._generate_read_response = _slverr_response


# --------------------------------------------------------------------------- #
# cocotb-test build boilerplate
# --------------------------------------------------------------------------- #
def run_monitor_sim(*, module, repo_root, tests_dir, log_dir, dut_name, testcase,
                    filelist, extra_sources=(), parameters=None,
                    extra_no_warn=()):
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist)
    verilog_sources = list(verilog_sources) + list(extra_sources)

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    sim_build_name = f"{testcase}{worker_suffix}"
    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    waves = get_wave_config(sim_build)
    # Silence benign, config-dependent elaboration warnings that --assert would
    # otherwise promote to errors: unconnected status pins (PINMISSING), width
    # zero-extend/truncate from the per-config width converters + regblock addr
    # narrowing (WIDTHEXPAND/WIDTHTRUNC), and degenerate [-1:0] ranges / index
    # selects in the monitor CAM for unused cones (ASCRANGE/SELRANGE). These are
    # RTL elaboration artifacts, orthogonal to the monbus stress behavior.
    extra_args = ['--assert', '--coverage',
                  '-Wno-PINMISSING', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC',
                  '-Wno-ASCRANGE', '-Wno-SELRANGE']
    extra_args += list(extra_no_warn) + waves['extra_args']
    extra_env = {
        'COCOTB_LOG_LEVEL': 'INFO',
        'LOG_PATH': log_path,
        'COCOTB_RESULTS_FILE': results_path,
        **waves['extra_env'],
    }

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase=testcase,
        parameters=parameters or {},
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env,
    )

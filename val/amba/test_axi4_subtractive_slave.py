"""axi4_subtractive_slave: an unroutable access must COMPLETE, with an error.

BRIDGE-009: a bridge address matching no slave range left the one-hot select
all-zero, so no slave ever saw AWVALID/ARVALID, READY never rose, and the
master waited forever. Every check here is written so a regression appears as
a timeout or a missing beat rather than a tolerated stall.
"""

import os
import random

import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.axi4.axi4_subtractive_slave_tb import AXI4SubtractiveSlaveTB


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def subtractive_slave_test(dut):
    tb = AXI4SubtractiveSlaveTB(dut)
    await tb.setup_clocks_and_reset()

    level = os.environ.get('TEST_LEVEL', 'func')
    n_rand = {'gate': 4, 'func': 16, 'full': 64}.get(level, 16)

    # ---- 1. single-beat write completes with DECERR -------------------
    bid, bresp = await tb.write_burst(addr=0xDEAD_0000, wid=3, beats=1)
    assert bresp == tb.DECERR, f"single write: expected DECERR, got {bresp:#04b}"
    assert bid == 3, f"BID must echo AWID: expected 3, got {bid}"
    tb.log.info("single-beat write completed with DECERR")

    # ---- 2. burst write completes, W beats all sunk --------------------
    bid, bresp = await tb.write_burst(addr=0xBAD0_1000, wid=7, beats=8)
    assert bresp == tb.DECERR, f"burst write: expected DECERR, got {bresp:#04b}"
    assert bid == 7, f"BID must echo AWID: expected 7, got {bid}"
    tb.log.info("8-beat write completed with DECERR")

    # ---- 3. W BEFORE AW must not deadlock ------------------------------
    # A slave that gates WREADY on having seen AW hangs here, reintroducing
    # the very failure this module removes -- on its own error path.
    bid, bresp = await tb.write_burst(addr=0xBAD0_2000, wid=5, beats=4,
                                      w_before_aw=True)
    assert bresp == tb.DECERR, f"W-before-AW: expected DECERR, got {bresp:#04b}"
    assert bid == 5, f"BID must echo AWID: expected 5, got {bid}"
    tb.log.info("W-before-AW completed with DECERR (no deadlock)")

    # ---- 4. reads return AxLEN+1 beats, DEADBEEF, DECERR, RLAST --------
    for beats in (1, 2, 16):
        rid = (beats * 3) % (1 << tb.IW)
        got = await tb.read_burst(addr=0xBAD0_3000, rid=rid, beats=beats)
        assert len(got) == beats, \
            f"read of {beats}: got {len(got)} beat(s); a short burst hangs the master"
        for i, (gid, gdata, gresp, glast) in enumerate(got):
            assert gid == rid, f"beat {i}: RID must echo ARID ({rid}), got {gid}"
            assert gresp == tb.DECERR, f"beat {i}: expected DECERR, got {gresp:#04b}"
            assert gdata == tb.fill, \
                f"beat {i}: expected fill {tb.fill:#x}, got {gdata:#x}"
            assert glast == (i == beats - 1), \
                f"beat {i}: RLAST must be set only on the final beat"
        tb.log.info(f"{beats}-beat read returned DEADBEEF/DECERR with correct RLAST")

    # ---- 5. back-to-back traffic keeps completing ----------------------
    rnd = random.Random(int(os.environ.get('SEED', '0')))
    for _ in range(n_rand):
        if rnd.random() < 0.5:
            n = rnd.choice([1, 2, 4, 16])
            wid = rnd.randrange(1 << tb.IW)
            _, bresp = await tb.write_burst(addr=rnd.randrange(0, 1 << 20) << 4,
                                            wid=wid, beats=n)
            assert bresp == tb.DECERR
        else:
            n = rnd.choice([1, 2, 4, 16])
            rid = rnd.randrange(1 << tb.IW)
            got = await tb.read_burst(addr=rnd.randrange(0, 1 << 20) << 4,
                                      rid=rid, beats=n)
            assert len(got) == n and got[-1][3] == 1
    tb.log.info(f"{n_rand} randomised accesses all completed with DECERR")

    # ---- 6. sticky status, first-address capture, saturation, clear ----
    d = dut
    assert int(d.o_hit_irq.value) == 1, \
        "o_hit_irq must be SET after unmapped traffic -- an interrupt that " \
        "never asserts is the hang in a different costume"
    first_addr = int(d.o_hit_addr.value)
    count_before = int(d.o_hit_count.value)
    assert count_before > 0, "hit counter never incremented"
    tb.log.info(f"sticky: irq=1 addr=0x{first_addr:x} count={count_before}")

    # A later hit must NOT overwrite the first address.
    await tb.read_burst(addr=0x7777_0000, rid=1, beats=1)
    assert int(d.o_hit_addr.value) == first_addr, \
        "a later fault overwrote the first address; the first one is the " \
        "evidence that usually explains the rest"

    # Clear, and confirm it actually clears.
    d.i_hit_clear.value = 1
    await RisingEdge(tb.aclk)
    await RisingEdge(tb.aclk)
    d.i_hit_clear.value = 0
    await RisingEdge(tb.aclk)
    assert int(d.o_hit_irq.value) == 0, "i_hit_clear did not clear o_hit_irq"
    assert int(d.o_hit_count.value) == 0, "i_hit_clear did not reset the count"
    assert int(d.o_hit_addr.value) == first_addr, \
        "clearing the flag must leave the address readable"
    tb.log.info("clear works; address survives the clear")

    # And it re-arms.
    await tb.read_burst(addr=0x8888_0000, rid=2, beats=1)
    assert int(d.o_hit_irq.value) == 1, "status did not re-arm after a clear"
    tb.log.info("status re-arms after clear")


def generate_params():
    return [(8, 32, 32), (4, 32, 64), (8, 40, 32)]


@pytest.mark.parametrize("id_width, addr_width, data_width", generate_params())
def test_axi4_subtractive_slave(request, id_width, addr_width, data_width):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi4': 'rtl/amba/axi4',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "axi4_subtractive_slave"
    test_level = os.environ.get('TEST_LEVEL', 'func')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    tag = f"id{id_width:03d}_aw{addr_width:03d}_dw{data_width:03d}_{test_level}"
    test_name_plus_params = f"test_{worker_id}_{dut_name}_{tag}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axi4_subtractive_slave.f")

    rtl_parameters = {
        'AXI_ID_WIDTH': id_width,
        'AXI_ADDR_WIDTH': addr_width,
        'AXI_DATA_WIDTH': data_width,
        'AXI_USER_WIDTH': 1,
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_LEVEL': test_level,
        'TEST_ID_WIDTH': str(id_width),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
    }

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=bool(int(os.environ.get('WAVES', '0'))),
        keep_files=True,
        compile_args=["-Wall", "-Wno-DECLFILENAME", "-Wno-UNUSEDPARAM",
                      "-Wno-UNUSEDSIGNAL"],
    )

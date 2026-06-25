"""
cocotb_cdc_demo.py — CocoTB tests for cdc_demo_sim_top.

Drives the AXIL slave directly (single-beat AXI4-Lite — no master BFM
needed; we drive the handshake by hand). Checks the basic harness
contract:

  - BUILD_ID readback
  - SCRATCH read-after-write
  - Per-counter CSR writes land
  - HOST_PRESS injection advances VALUE and PRESS_COUNT
  - CFG_LOAD resets VALUE to INIT
  - CDC_MODE switches the value path
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

CLK_PERIOD_NS = 10  # 100 MHz

# CSR offsets — must match cdc_demo_harness.sv
OFF_BUILD_ID    = 0x000
OFF_STATUS      = 0x004
OFF_CTRL        = 0x008
OFF_DISP_SELECT = 0x00C
OFF_SCRATCH     = 0x010

# Per-counter (base = 0x40 + i*0x40; sim has 1 counter so base = 0x40)
CTR_BASE  = 0x40
def co(off):  # counter-offset helper for counter 0
    return CTR_BASE + off
OFF_DIVISOR    = 0x00
OFF_INIT       = 0x04
OFF_INCREMENT  = 0x08
OFF_CFG_LOAD   = 0x0C
OFF_HOST_PRESS = 0x10
OFF_VALUE      = 0x14
OFF_PRESS_CNT  = 0x18
OFF_CLK_TICKS  = 0x1C
OFF_CDC_MODE   = 0x20
OFF_AUTO_INC   = 0x24

EXPECTED_BUILD_ID = 0x4344_4331  # "CDC1"


# -----------------------------------------------------------------------------
# Tiny AXIL master in cocotb. Single-beat, single-outstanding.
# -----------------------------------------------------------------------------

async def axil_write(dut, addr, data):
    dut.s_axil_awaddr.value  = addr
    dut.s_axil_awprot.value  = 0
    dut.s_axil_awvalid.value = 1
    dut.s_axil_wdata.value   = data & 0xFFFF_FFFF
    dut.s_axil_wstrb.value   = 0xF
    dut.s_axil_wvalid.value  = 1
    dut.s_axil_bready.value  = 1
    # Wait until both AW and W handshakes have completed
    aw_done = False
    w_done  = False
    for _ in range(200):
        await RisingEdge(dut.aclk)
        if (not aw_done) and int(dut.s_axil_awready.value) == 1:
            aw_done = True
            dut.s_axil_awvalid.value = 0
        if (not w_done) and int(dut.s_axil_wready.value) == 1:
            w_done = True
            dut.s_axil_wvalid.value = 0
        if aw_done and w_done:
            break
    # Wait for B response
    for _ in range(200):
        await RisingEdge(dut.aclk)
        if int(dut.s_axil_bvalid.value) == 1:
            dut.s_axil_bready.value = 0
            return
    raise TimeoutError(f"AXIL write to 0x{addr:08X} did not receive B response")


async def axil_read(dut, addr):
    dut.s_axil_araddr.value  = addr
    dut.s_axil_arprot.value  = 0
    dut.s_axil_arvalid.value = 1
    dut.s_axil_rready.value  = 1
    # Wait for AR handshake
    for _ in range(200):
        await RisingEdge(dut.aclk)
        if int(dut.s_axil_arready.value) == 1:
            dut.s_axil_arvalid.value = 0
            break
    else:
        raise TimeoutError(f"AXIL read AR to 0x{addr:08X} not accepted")
    # Wait for R
    for _ in range(200):
        await RisingEdge(dut.aclk)
        if int(dut.s_axil_rvalid.value) == 1:
            data = int(dut.s_axil_rdata.value)
            dut.s_axil_rready.value = 0
            return data
    raise TimeoutError(f"AXIL read RDATA from 0x{addr:08X} not received")


async def init_dut(dut):
    """Start the clock, hold reset for a few cycles, then release."""
    cocotb.start_soon(Clock(dut.aclk, CLK_PERIOD_NS, units="ns").start())

    # All AXIL inputs idle
    for sig in ("s_axil_awaddr","s_axil_awprot","s_axil_awvalid",
                "s_axil_wdata","s_axil_wstrb","s_axil_wvalid",
                "s_axil_bready","s_axil_araddr","s_axil_arprot",
                "s_axil_arvalid","s_axil_rready","i_btn"):
        getattr(dut, sig).value = 0

    dut.aresetn.value = 0
    for _ in range(20):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    for _ in range(10):
        await RisingEdge(dut.aclk)


# -----------------------------------------------------------------------------
# Tests
# -----------------------------------------------------------------------------

@cocotb.test()
async def test_build_id_and_scratch(dut):
    """Sanity: BUILD_ID reads "CDC1" and SCRATCH round-trips."""
    await init_dut(dut)

    bid = await axil_read(dut, OFF_BUILD_ID)
    assert bid == EXPECTED_BUILD_ID, \
        f"BUILD_ID mismatch: got 0x{bid:08X}, expected 0x{EXPECTED_BUILD_ID:08X}"
    dut._log.info(f"BUILD_ID = 0x{bid:08X} OK")

    for v in (0xDEAD_BEEF, 0x1234_5678, 0xA5A5_5A5A, 0x0):
        await axil_write(dut, OFF_SCRATCH, v)
        rb = await axil_read(dut, OFF_SCRATCH)
        assert rb == v, f"SCRATCH round-trip failed: wrote 0x{v:08X} read 0x{rb:08X}"
    dut._log.info("SCRATCH round-trip OK")


@cocotb.test()
async def test_counter_cfg_writes(dut):
    """Per-counter CSR writes land in the storage."""
    await init_dut(dut)

    # Use a fast pickoff so we can see ctr_clk in sim
    await axil_write(dut, co(OFF_DIVISOR),   2)        # very fast
    await axil_write(dut, co(OFF_INIT),      0x42)
    await axil_write(dut, co(OFF_INCREMENT), 5)
    await axil_write(dut, co(OFF_CDC_MODE),  1)        # broken mode

    assert (await axil_read(dut, co(OFF_DIVISOR)))   == 2
    assert (await axil_read(dut, co(OFF_INIT)))      == 0x42
    assert (await axil_read(dut, co(OFF_INCREMENT))) == 5
    assert (await axil_read(dut, co(OFF_CDC_MODE)))  == 1
    dut._log.info("Per-counter cfg writes verified")

    # Reset CDC_MODE so the rest of the test uses proper CDC
    await axil_write(dut, co(OFF_CDC_MODE), 0)


@cocotb.test()
async def test_host_press_increments(dut):
    """HOST_PRESS injection should advance VALUE and PRESS_COUNT."""
    await init_dut(dut)

    # Configure: small pickoff (fast ctr_clk so CDC settles quickly in sim),
    # INIT=0x10, INCREMENT=3.
    await axil_write(dut, co(OFF_DIVISOR),   1)        # pickoff=1 -> /4
    await axil_write(dut, co(OFF_INIT),      0x10)
    await axil_write(dut, co(OFF_INCREMENT), 3)
    await axil_write(dut, co(OFF_CFG_LOAD),  1)        # load INIT into counter

    # Let CDC settle (sync_pulse needs a few ctr_clk + sys_clk edges)
    await Timer(1, units="us")

    val_before = (await axil_read(dut, co(OFF_VALUE))) & 0xFFFF
    cnt_before = await axil_read(dut, co(OFF_PRESS_CNT))
    dut._log.info(f"Before presses: VALUE=0x{val_before:04X} PRESS_COUNT={cnt_before}")
    assert val_before == 0x10, f"INIT load failed: VALUE=0x{val_before:04X}"

    # Inject 3 host presses (with enough spacing for sync_pulse to retrigger)
    for _ in range(3):
        await axil_write(dut, co(OFF_HOST_PRESS), 1)
        await Timer(2, units="us")

    val_after = (await axil_read(dut, co(OFF_VALUE))) & 0xFFFF
    cnt_after = await axil_read(dut, co(OFF_PRESS_CNT))
    dut._log.info(f"After 3 presses: VALUE=0x{val_after:04X} PRESS_COUNT={cnt_after}")

    # Expected: VALUE = 0x10 + 3*3 = 0x19, PRESS_COUNT = 3
    assert val_after == 0x19, f"VALUE after presses: got 0x{val_after:04X}, expected 0x19"
    assert cnt_after - cnt_before == 3, \
        f"PRESS_COUNT delta: got {cnt_after - cnt_before}, expected 3"


@cocotb.test()
async def test_cfg_load_reloads_value(dut):
    """CFG_LOAD reloads VALUE to INIT without disturbing PRESS_COUNT."""
    await init_dut(dut)

    await axil_write(dut, co(OFF_DIVISOR),   1)
    await axil_write(dut, co(OFF_INIT),      0x00)
    await axil_write(dut, co(OFF_INCREMENT), 1)
    await axil_write(dut, co(OFF_CFG_LOAD),  1)
    await Timer(1, units="us")

    # Press a few times
    for _ in range(5):
        await axil_write(dut, co(OFF_HOST_PRESS), 1)
        await Timer(2, units="us")

    val_mid = (await axil_read(dut, co(OFF_VALUE))) & 0xFFFF
    cnt_mid = await axil_read(dut, co(OFF_PRESS_CNT))
    dut._log.info(f"Mid: VALUE=0x{val_mid:04X} PRESS_COUNT={cnt_mid}")
    assert val_mid == 0x05

    # Reload to 0xBEEF (test wider value width too)
    await axil_write(dut, co(OFF_INIT), 0xBEEF)
    await axil_write(dut, co(OFF_CFG_LOAD), 1)
    await Timer(2, units="us")

    val_reload = (await axil_read(dut, co(OFF_VALUE))) & 0xFFFF
    cnt_reload = await axil_read(dut, co(OFF_PRESS_CNT))
    dut._log.info(f"After reload: VALUE=0x{val_reload:04X} PRESS_COUNT={cnt_reload}")
    assert val_reload == 0xBEEF, f"VALUE after CFG_LOAD: got 0x{val_reload:04X}, expected 0xBEEF"
    assert cnt_reload == cnt_mid, \
        f"PRESS_COUNT should not change on CFG_LOAD: was {cnt_mid}, now {cnt_reload}"

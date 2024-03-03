import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, RisingEdge, Timer
from cocotb.regression import TestFactory


@cocotb.coroutine
async def reset_dut(dut):
    """Reset the DUT"""
    dut.i_block_arb.value = 0
    dut.i_rst_n.value = 0
    await FallingEdge(dut.i_clk)
    await FallingEdge(dut.i_clk)
    dut.i_rst_n.value = 1
    await FallingEdge(dut.i_clk)

@cocotb.coroutine
async def run_test(dut):
    """Run the test on the DUT"""

    num_clients = len(dut.i_req)
    print(f"Detected {num_clients} clients based on the i_req width.")

    # Reset the DUT
    await reset_dut(dut)

    # Basic tests
    for i in range(num_clients):
        dut.i_req.value = (1 << i)
        await FallingEdge(dut.i_clk)
        assert dut.o_gnt.value.integer == (1 << i), f"Expected o_gnt[{i}] to be high"

    # Test when multiple requests are made
    for i in range(num_clients - 1):
        dut.i_req.value = (1 << i) | (1 << (i + 1))
        await FallingEdge(dut.i_clk)
        assert dut.o_gnt.value.integer in [
            1 << i,
            1 << (i + 1),
        ], f"Expected either o_gnt[{i}] or o_gnt[{i + 1}] to be high"

    # Test with all clients requesting
    dut.i_req <= (1 << num_clients) - 1  # All bits set
    await FallingEdge(dut.i_clk)

    # Here, one of the requests should be granted, but we're not specific about which. It will depend on the internal logic of your arbiter and the state it's currently in.

@cocotb.test()
async def arbiter_round_robin_test(dut):
    """Test the round-robin arbiter"""

    cocotb.start_soon(Clock(dut.i_clk, 10, units="ns").start())  # Start the clock

    await run_test(dut)

tf = TestFactory(arbiter_round_robin_test)
tf.generate_tests()

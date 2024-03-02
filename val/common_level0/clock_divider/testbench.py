import cocotb
from cocotb.triggers import Timer
from cocotb.clock import Clock

async def reset_dut(rst_n, duration, clk_period):
    rst_n.value = 0
    await Timer(duration * clk_period)
    rst_n.value = 1

@cocotb.test()
async def test_clock_divider(dut):
    clk_period = 10  # ns for 100MHz
    pickoff_points = 0x08060402

    # Start the clock
    clock = Clock(dut.i_clk, clk_period, units='ns')
    cocotb.start_soon(clock.start())

    # Reset the DUT
    cocotb.start_soon(reset_dut(dut.i_rst_n, 20, clk_period))

    # Set i_pickoff_points
    dut.i_pickoff_points.value = pickoff_points

    # Calculate the period of o_divided_clk[3] and wait for 4 toggles
    # Assuming you know the toggle rate, for example, if it toggles every 400ns
    toggle_period = 1200  # Replace with the correct period in ns
    await Timer(4 * toggle_period, units='ns')

    dut._log.info("Waited for sufficient time for 4 toggles of o_divided_clk[3].")

from cocotb.regression import TestFactory
tf = TestFactory(test_clock_divider)
tf.generate_tests()
import cocotb
import itertools
from cocotb.triggers import RisingEdge, ReadOnly, Timer, NextTimeStep
from cocotb.regression import TestFactory
from cocotb.decorators import coroutine
from cocotb.clock import Clock

@cocotb.coroutine
async def test_divider(dut, dividend, divisor):
    """ Test the divider with specific dividend and divisor values. """

    # Reset
    dut.i_rst_b <= 0
    dut.i_start <= 0
    cocotb.start_soon(Clock(dut.i_clk, 10, units="ns").start())
    await cocotb.triggers.Timer(5, units='ns')
    dut.i_rst_b <= 1
    await cocotb.triggers.Timer(40, units='ns')

    # Check for divide by zero
    dbz = (divisor == 0)

    # Start the division
    dut.i_dividend <= dividend
    dut.i_divisor <= divisor
    dut.i_start <= 1
    await cocotb.triggers.Timer(10, units='ns')
    dut.i_start <= 0
    loop_counter = 0

    # Wait for division to complete using a while loop
    while True:
        # await ReadOnly()  # Wait for read-only phase to read signal values
        # await NextTimeStep()  # Move to the next time step where writes are allowed
        loop_counter += 1
        if loop_counter > 500:
            print("Reached 500 iterations, ending simulation")
            cocotb.simulator.finish()  # End the simulation
        if dut.o_done.value:
            break
        #print(f'{dut.o_busy} {dut.o_done} {dut.o_valid} {dut.o_dbz}')
        await Timer(10, units='ns')  # Wait for a specified time
    # print('Done...')

    # Check results
    if not dbz:
        assert dut.o_valid.value, "Result is not valid"
        expected_quotient = dividend // divisor
        expected_remainder = dividend % divisor
        assert dut.o_quotient.value == expected_quotient, f"Incorrect quotient: {dut.o_quotient.value} != {expected_quotient}"
        assert dut.o_remainder.value == expected_remainder, f"Incorrect remainder: {dut.o_remainder.value} != {expected_remainder}"
    else:
        assert dut.o_dbz.value, "Divide by zero not detected"

@cocotb.coroutine
async def run_test(dut):
    """ Run tests with different dividend and divisor pairs. """
    DATA_WIDTH = len(dut.i_dividend)
    max_value = 2**DATA_WIDTH - 1

    for dividend, divisor in itertools.product(range(max_value + 1), range(max_value + 1)):
        await test_divider(dut, dividend, divisor)
        if divisor % 5 == 0:
            print(f'{dividend=} {divisor=}')


factory = TestFactory(run_test)
factory.generate_tests()

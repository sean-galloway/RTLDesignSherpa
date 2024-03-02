import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test_count_leading_zeros(dut):
    width = len(dut.i_data)
    dut._log.info(f"Testing with WIDTH={width}")

    # Start with all zeros
    dut.i_data.value = 0
    # dut.i_enable.value = 0
    await Timer(100, units='ns')
    # dut.i_enable.value = 1
    await Timer(10, units='ns')
    assert dut.ow_count_leading_zeros.value == width, f"Expected {width} leading zeros, got {dut.ow_leading_zeros_count.value}"

    # Walk a '1' through the entire width
    for i in range(width):
        dut.i_data.value = 1 << (width - 1 - i)
        await Timer(10, units='ns')
        expected_leading_zeros = width - 1 - i
        assert dut.ow_count_leading_zeros.value == expected_leading_zeros, f"Expected {expected_leading_zeros} leading zeros, got {dut.ow_leading_zeros_count.value}"

    # End with all zeros again
    dut.i_data.value = 0
    await Timer(10, units='ns')
    assert dut.ow_count_leading_zeros.value == width, f"Expected {width} leading zeros, got {dut.ow_leading_zeros_count.value}"

    dut._log.info("Test completed successfully")

from cocotb.regression import TestFactory
tf = TestFactory(test_count_leading_zeros)
tf.generate_tests()
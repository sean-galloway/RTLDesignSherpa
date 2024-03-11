from TBBase import TBBase
import cocotb
import contextlib
import itertools
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles, Timer
from crc import Calculator, Configuration
import os
import random

class AdderTB(TBBase):

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        # Gather the settings from the Parameters to verify them
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '0'))
        self.max_val = (2**self.N)
        self.mask = self.max_val - 1


    async def main_loop(self, count=256):
        self.log.info("Main Test")
        c_list = [0, 1]
        if self.max_val < count:
            a_list = list(range(self.max_val))
            b_list = list(range(self.max_val))
        else:
            a_list = [random.randint(0, self.max_val) for _ in range(count)]
            b_list = [random.randint(0, self.max_val) for _ in range(count)]

        for a, b, c_in in itertools.product(a_list, b_list, c_list):
            self.log.info(f'Applying {a=} {b=} {c_in=}')
            try:
                self.dut.i_a.value = a
                self.dut.i_b.value = b
                self.dut.i_c.value = c_in
            except AttributeError:
                continue
            await self.wait_time(1, 'ns')
            ow_sum = int(self.dut.ow_sum.value)
            ow_carry = int(self.dut.ow_carry.value)
            expected_sum = (a + b + c_in) & self.mask
            expected_carry = int(a + b + c_in > self.mask)
            
            assert (ow_sum == expected_sum) and (ow_carry == expected_carry), f"Input: a={a}, b={b}, c_in={c_in}\nExpected: sum={expected_sum}, carry={expected_carry}\nGot: sum={ow_sum}, carry={ow_carry}"


    async def half_adder_test(self):
        # Define the expected results for all input combinations in the format:
        # (i_a, i_b) -> (ow_sum, ow_carry)
        expected_results = {
            (0, 0): (0, 0),
            (0, 1): (1, 0),
            (1, 0): (1, 0),
            (1, 1): (0, 1)
        }

        for inputs, expected_output in expected_results.items():
            self.dut.i_a.value = inputs[0]
            self.dut.i_b.value = inputs[1]

            await Timer(1, units='ns')  # wait for the combinatorial logic to settle

            assert (self.dut.ow_sum.value, self.dut.ow_carry.value) == expected_output,\
                f"For inputs {inputs}, expected output was {expected_output} but got {(self.dut.ow_sum.value, self.dut.ow_carry.value)}"


    async def main_loop_carry_save(self, count=256):
        self.log.info("Main Test")
        c_list = [0, 1]
        if self.max_val < count:
            a_list = list(range(self.max_val))
            b_list = list(range(self.max_val))
        else:
            a_list = [random.randint(0, self.max_val) for _ in range(count)]
            b_list = [random.randint(0, self.max_val) for _ in range(count)]

        for a, b, c_in in itertools.product(a_list, b_list, c_list):
            self.log.info(f'Applying {a=} {b=} {c_in=}')
            self.dut.i_a.value = a
            self.dut.i_b.value = b
            self.dut.i_c.value = c_in
            await self.wait_time(1, 'ns')

            # Python-based reference computation for sum and carry
            expected_sum = [0]*self.N
            expected_carry = [0]*self.N

            for i in range(self.N):
                a_bit = (a >> i) & 1
                b_bit = (b >> i) & 1
                c_bit = (c_in >> i) & 1
                expected_sum[i] = a_bit ^ b_bit ^ c_bit
                expected_carry[i] = (a_bit & b_bit) | (a_bit & c_bit) | (b_bit & c_bit)

            expected_sum = int("".join(str(bit) for bit in reversed(expected_sum)), 2)
            expected_carry = int("".join(str(bit) for bit in reversed(expected_carry)), 2)
            ow_sum = int(self.dut.ow_sum.value)
            ow_carry = int(self.dut.ow_carry.value)
            
            assert (ow_sum == expected_sum) and (ow_carry == expected_carry), f"Input: a={a}, b={b}, c_in={c_in}\nExpected: sum={expected_sum}, carry={expected_carry}\nGot: sum={ow_sum}, carry={ow_carry}"


    async def clear_interface(self):
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        with contextlib.suppress(AttributeError):
            self.dut.i_c.value = 0


    def print_settings(self):
        """self.log.info the settings of the CRCTesting class.

        This method self.log.infos out the settings related to data width, chunks, CRC width, polynomial, initial polynomial value, input reflection, output reflection, and XOR output for CRC testing.

        Args:
            None
        Returns:
            None
        """
        self.log.info('-------------------------------------------')
        self.log.info('Settings:')
        self.log.info(f'    N:     {self.N}')
        self.log.info('-------------------------------------------')

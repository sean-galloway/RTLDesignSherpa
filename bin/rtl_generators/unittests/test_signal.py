import sys
import os
import io

base_path = '/home/sean/github/RTL_Design_Projects/tools/rtl_generators/'

# Get the directory containing verilog_parser.py
module_dir = os.path.abspath(base_path)

# Add the directory to the sys.path
sys.path.append(module_dir)

import unittest
from verilog.signal import Signal
from unittests.data_str import tstSignal01, signal_add_port_string_01_gold, signal_create_port_string_01_gold, signal_create_wire_string_01_gold
from pprint import pprint


class SignalTest(unittest.TestCase):


    @classmethod
    def setUpClass(cls):
        os.makedirs('tools/rtl_generators/unittest_logs', exist_ok=True)
        cls.file = open('tools/rtl_generators/unittest_logs/test_signal.txt', 'w')


    @classmethod
    def tearDownClass(cls):
        cls.file.close()


    def write_log(self, test_name, output):
        self.file.write("# ==============================================================\n")
        self.file.write(f"# {test_name}\n")
        self.file.write("# --------------------------------------------------------------\n")
        self.file.write(f"{output}\n")
        self.file.write("# ==============================================================\n\n\n")


    def pprint_list(self, output) -> str:
        # Create a string buffer to capture the pprint output
        output_buffer = io.StringIO()
        # Pretty print to the buffer
        pprint(output, stream=output_buffer, indent=4)
        # Get the string from the buffer
        output_string = output_buffer.getvalue()
        # Close the buffer
        output_buffer.close()
        return output_string


    def test_signal_add_port_string_01(self):
        sig = Signal()
        tstList = sig.add_port_string(tstSignal01)
        tst_str = self.pprint_list(tstList)
        ans_str = signal_add_port_string_01_gold
        self.file.write(f'{len(tstList)=}')
        self.write_log('test_signal_add_port_string_01', tst_str)
        # pprint(tstList)
        self.assertEqual(tst_str, ans_str, 'Issue with test_signal_add_port_string_01: ')


    def test_signal_create_port_string_01(self):
        sig = Signal()
        sig.add_port_string(tstSignal01)
        tst_str = sig.create_port_string()
        ans_str = signal_create_port_string_01_gold
        self.write_log('test_signal_create_port_string_01', tst_str)
        # pprint(tstList)
        self.assertEqual(tst_str, ans_str, 'Issue with test_signal_create_port_string_01: ')


    def test_signal_create_wire_string_01(self):
        sig = Signal()
        sig.add_port_string(tstSignal01)
        tst_str = sig.create_wire_string()
        ans_str = signal_create_wire_string_01_gold
        self.write_log('test_signal_create_wire_string_01', tst_str)
        # pprint(tstList)
        self.assertEqual(tst_str, ans_str, 'Issue with test_signal_create_wire_string_01: ')

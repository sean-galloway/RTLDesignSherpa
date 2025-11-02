# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ParamTest
# Purpose: Test suite for Param
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

import sys
import os
import subprocess
import io

base_path = '/home/sean/github/RTL_Design_Projects/tools/rtl_generators/'

# Get the directory containing verilog_parser.py
module_dir = os.path.abspath(base_path)

# Add the directory to the sys.path
sys.path.append(module_dir)

import unittest
from verilog.param import Param
from unittests.data_str import tstParam01, param_add_param_string_01_gold, param_create_param_string_01_gold
from pprint import pprint


class ParamTest(unittest.TestCase):


    @classmethod
    def setUpClass(cls):
        os.makedirs('tools/rtl_generators/unittest_logs', exist_ok=True)
        cls.file = open('tools/rtl_generators/unittest_logs/test_param.txt', 'w')


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


    def test_param_add_param_string_01(self):
        sig = Param()
        tstList = sig.add_param_string(tstParam01)
        tst_str = self.pprint_list(tstList)
        ans_str = param_add_param_string_01_gold
        self.file.write(f'{len(tstList)=}')
        self.write_log('test_param_add_param_string_01', tst_str)
        # pprint(tstList)
        self.assertEqual(tst_str, ans_str, 'Issue with test_signal_add_param_string_01: ')


    def test_param_create_param_string_01(self):
        sig = Param()
        sig.add_param_string(tstParam01)
        tst_str = sig.create_param_string()
        ans_str = param_create_param_string_01_gold
        self.write_log('test_param_create_param_string_01', tst_str)
        # pprint(tstList)
        self.assertEqual(tst_str, ans_str, 'Issue with test_signal_create_port_string_01: ')



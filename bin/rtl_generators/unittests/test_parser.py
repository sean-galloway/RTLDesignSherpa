import sys
import os

# Get the directory containing verilog_parser.py
module_dir = os.path.abspath("/home/sean/github/RTL_Design_Projects/tools/rtl_generators/")

# Add the directory to the sys.path
sys.path.append(module_dir)

import unittest
from verilog.verilog_parser import Parser, ParserHelper
from data_str import tstSimpleModule, tstSimpleModuleName, \
    tstSimpleParams, tstSimplePorts, tstCompilerDirectiveModule, \
    tstCompilerDirectiveModuleName, tstCompilerDirectiveParams, \
    tstCompilerDirectivePorts,\
    tstProcessSig1, tstProcessSig2, tstProcessSig3, \
    tstProcessSigFree1, tstProcessSigFree2, tstProcessSigFree3, \
    tstProcessSigFree4
import pprint


class ParserTest(unittest.TestCase):
    def test_parserhelper_processSignalFreeform0(self):
        tstStr = "1'b1"
        tstList = ParserHelper.processSignalFreeform(tstStr, 'input', 'logic')
        # pprint.pprint(tstList)
        self.assertEqual(tstList, [],
                         'Issue with processSignalFreeform: ' + tstStr)

    def test_parserhelper_processSignalFreeform1(self):
        tstStr = 'MMT_Legacy_En ? MMT0_Int00 : dcr_irq[0]'
        tstList = ParserHelper.processSignalFreeform(tstStr, 'input', 'logic')
        # pprint.pprint(tstList)
        self.assertEqual(tstList, tstProcessSigFree1,
                         'Issue with processSignalFreeform: ' + tstStr)

    def test_parserhelper_processSignalFreeform2(self):
        tstStr = 'dcr_irq[20] | MMT0_Int20 | MMT1_Int20 | MMT2_Int20'
        tstList = ParserHelper.processSignalFreeform(tstStr, 'input', 'logic')
        # pprint.pprint(tstList)
        self.assertEqual(tstList, tstProcessSigFree2,
                         'Issue with processSignalFreeform: ' + tstStr)

    def test_parserhelper_processSignalFreeform3(self):
        tstStr = 'dcr_ahb_dyncgdis | !ahb_idle | ahb_busy | ahb_inprogress ' + \
                    '| dcr_pm_sw_req | dcr_pm_hvm_req'
        tstList = ParserHelper.processSignalFreeform(tstStr, 'input', 'logic')
        # pprint.pprint(tstList)
        self.assertEqual(tstList, tstProcessSigFree3,
                         'Issue with processSignalFreeform: ' + tstStr)

    def test_parserhelper_processSignalFreeform4(self):
        tstStr = "muxSel ? { 4'b000, sigA } : { 4'hF, sigB}"
        tstList = ParserHelper.processSignalFreeform(tstStr, 'input', 'logic')
#        pprint.pprint(tstList)
        self.assertEqual(tstList, tstProcessSigFree4,
                         'Issue with processSignalFreeform: ' + tstStr)

    def test_parserhelper_processSignal1(self):
        tstStr = 'strVal'
        tstRec = ParserHelper.processSignal(tstStr, 'input', 'logic')
        # print "processSignal1:"
        # pprint.pprint(tstRec)
        self.assertEqual(tstRec, tstProcessSig1,
                         'Issue with processSignal: ' + tstStr)

    def test_parserhelper_processSignal2(self):
        tstStr = 'strVal[15]'
        tstRec = ParserHelper.processSignal(tstStr, 'input', 'logic')
        self.assertEqual(tstRec, tstProcessSig2,
                         'Issue with processSignal: ' + tstStr)

    def test_parserhelper_processSignal3(self):
        tstStr = 'strVal2[15:0][7:4]'
        tstRec = ParserHelper.processSignal(tstStr, 'output', 'logic')
        self.assertEqual(tstRec, tstProcessSig3,
                         'Issue with processSignal: ' + tstStr)

    def test_parserhelper_get_remove_arrays(self):
        tstStr = 'strval[(D/8-1):0]'
        tstNameStr = ParserHelper.removeArrays(tstStr)
        tstArrayStr = ParserHelper.getArrays(tstStr)
        self.assertEqual('strval', tstNameStr, 'Remove Array did not work')
        self.assertEqual('[(D/8-1):0]', tstArrayStr, 'Get Array did not work')

    def test_parserhelper_array_merge1_advanced(self):
        arrA = '[15:0][7:0]'
        arrB = '[31:16][15:8]'
        mrgVal = '[31:0][15:0]'
        arrMerge = ParserHelper.arrayMerge(arrA, arrB)
        print("Advanced Array Merge 1: " + arrMerge)
        self.assertEqual(arrMerge, mrgVal, 'Array Merge issue, expected: ' +
                         mrgVal + ' received: ' + arrMerge)
        arrA = '[(DW-1):0][7:0]'
        arrB = '[(DW-1):0][15:8]'
        mrgVal = '[(DW-1):0][15:0]'
        arrMerge = ParserHelper.arrayMerge(arrA, arrB)
        print("Advanced Array Merge 2: " + arrMerge)
        self.assertEqual(arrMerge, mrgVal, 'Array Merge issue, expected: ' +
                         mrgVal + ' received: ' + arrMerge)
        arrA = '[DFI_NUMB_PHASES-1:0][DFI_ADDRESS_WIDTH-1:0]'
        arrB = '[DFI_NUMB_PHASES-1:0][DFI_ADDRESS_WIDTH-1:0]'
        mrgVal = '[DFI_NUMB_PHASES-1:0][DFI_ADDRESS_WIDTH-1:0]'
        arrMerge = ParserHelper.arrayMerge(arrA, arrB)
        print("Advanced Array Merge 3: " + arrMerge)
        self.assertEqual(arrMerge, mrgVal, 'Array Merge issue, expected: ' +
                         mrgVal + ' received: ' + arrMerge)

    def test_parserhelper_array_merge1(self):
        arrA = '[15:0]'
        arrB = '[31:16]'
        mrgVal = '[31:0]'
        arrMerge = ParserHelper.arrayMerge(arrA, arrB)
        self.assertEqual(arrMerge, mrgVal, 'Array Merge issue, expected: ' +
                         mrgVal + ' received: ' + arrMerge)
        arrA = '[15]'
        arrB = '[14]'
        mrgVal = '[15:14]'
        arrMerge = ParserHelper.arrayMerge(arrA, arrB)
        self.assertEqual(arrMerge, mrgVal, 'Array Merge issue, expected: ' +
                         mrgVal + ' received: ' + arrMerge)
        arrA = '[15]'
        arrB = '[16]'
        mrgVal = '[16:15]'
        arrMerge = ParserHelper.arrayMerge(arrA, arrB)
        self.assertEqual(arrMerge, mrgVal, 'Array Merge issue, expected: ' +
                         mrgVal + ' received: ' + arrMerge)
        arrA = '[15:15]'
        arrB = '[14]'
        mrgVal = '[15:14]'
        arrMerge = ParserHelper.arrayMerge(arrA, arrB)
        self.assertEqual(arrMerge, mrgVal, 'Array Merge issue, expected: ' +
                         mrgVal + ' received: ' + arrMerge)
        arrA = '[15:15]'
        arrB = '[0]'
        mrgVal = '[15:0]'
        arrMerge = ParserHelper.arrayMerge(arrA, arrB)
        self.assertEqual(arrMerge, mrgVal, 'Array Merge issue, expected: ' +
                         mrgVal + ' received: ' + arrMerge)
        arrA = '[15]'
        arrB = '[31]'
        mrgVal = '[31:15]'
        arrMerge = ParserHelper.arrayMerge(arrA, arrB)
        self.assertEqual(arrMerge, mrgVal, 'Array Merge issue, expected: ' +
                         mrgVal + ' received: ' + arrMerge)
        arrA = '[3:0]'
        arrB = '[15:12]'
        mrgVal = '[15:0]'
        arrMerge = ParserHelper.arrayMerge(arrA, arrB)
        self.assertEqual(arrMerge, mrgVal, 'Array Merge issue, expected: ' +
                         mrgVal + ' received: ' + arrMerge)
        arrA = ''
        arrB = ''
        mrgVal = ''
        arrMerge = ParserHelper.arrayMerge(arrA, arrB)
        self.assertEqual(arrMerge, mrgVal, 'Array Merge issue, expected: ' +
                         mrgVal + ' received: ' + arrMerge)
#         print 'arrA: ' + arrA + ' arrB: ' + arrB
#         print 'arrMerge: ' + arrMerge

    def test_parserhelper_array_merge2(self):
        arrA = '[15:0][3:0]'
        arrB = '[31:16][7:4]'
        mrgVal = '[31:0][7:0]'
        arrMerge = ParserHelper.arrayMerge(arrA, arrB)
        self.assertEqual(arrMerge, mrgVal, 'Array Merge issue, expected: ' +
                         mrgVal + ' received: ' + arrMerge)

    def test_parserhelper_array_merge3(self):
        arrA = '[15:0][3:0][2:0]'
        arrB = '[31:16][7:4]'
        # mrgVal = '[31:0][7:0][2:0]'
        # arrMerge = ParserHelper.arrayMerge(arrA, arrB)
        with self.assertRaises(ValueError):
            dummy = ParserHelper.arrayMerge(arrA, arrB)

    def test_parserhelper_array_merge4(self):
        arrA = '[15:0]'
        arrB = '[(DATA_WIDTH*4)-1:8]'
        mrgVal = '[(DATA_WIDTH*4)-1:0]'
        arrMerge = ParserHelper.arrayMerge(arrA, arrB)
        self.assertEqual(arrMerge, mrgVal, 'Array Merge issue, expected: ' +
                         mrgVal + ' received: ' + arrMerge)

    def test_simple_code(self):
        tstModule = tstSimpleModule
        tstModuleName = tstSimpleModuleName
        tstParams = tstSimpleParams
        tstPorts = tstSimplePorts
        x = Parser(tstModule)
#         print "Pretty Print Ports:"
#         pprint.pprint(x.portsList)

        self.assertEqual(x.moduleNameStr,  tstModuleName, 'Module Name mismatch')
        self.assertEqual(x.parametersList, tstParams, 'Parser Parameter mismatch')
        self.assertEqual(x.portsList,      tstPorts, 'Parser Port mismatch')

    def test_compiler_directive_code(self):
        tstModule = tstCompilerDirectiveModule
        tstModuleName = tstCompilerDirectiveModuleName
        tstParams = tstCompilerDirectiveParams
        tstPorts = tstCompilerDirectivePorts

        x = Parser(tstModule)
#         print "Pretty Print Parameters:"
#         pprint.pprint(x.parametersList)
#         print "Pretty Print Ports:"
#         pprint.pprint(x.portsList)
        self.assertEqual(x.moduleNameStr,  tstModuleName, 'Module Name mismatch')
        self.assertEqual(x.parametersList, tstParams, 'Parser Parameter mismatch')
        self.assertEqual(x.portsList,      tstPorts, 'Parser Port mismatch')


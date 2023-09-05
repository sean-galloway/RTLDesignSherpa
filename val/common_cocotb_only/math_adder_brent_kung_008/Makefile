CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(CWD)/../../../rtl/common
VERILOG_SOURCES = \
					$(CWD)/../../../rtl/common/math_adder_brent_kung_pg.sv \
					$(CWD)/../../../rtl/common/math_adder_brent_kung_black.sv \
					$(CWD)/../../../rtl/common/math_adder_brent_kung_gray.sv \
					$(CWD)/../../../rtl/common/math_adder_brent_kung_bitwisepg.sv \
					$(CWD)/../../../rtl/common/math_adder_brent_kung_grouppg_008.sv \
					$(CWD)/../../../rtl/common/math_adder_brent_kung_sum.sv \
					$(CWD)/../../../rtl/common/math_adder_brent_kung_008.sv

DUT = math_adder_brent_kung_008
MODULE = testbench
TOPLEVEL = $(DUT)


TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1
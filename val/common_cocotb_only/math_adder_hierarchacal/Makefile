CWD=$(shell pwd)
COCOTB_REDUCED_LOG_FMT = True
SIM ?= icarus
VERILOG_INCLUDE_DIRS = $(CWD)/../../../rtl/common
VERILOG_SOURCES = \
					$(CWD)/../../../rtl/common/math_adder_carry_lookahead.sv \
					$(CWD)/../../../rtl/common/math_adder_hierarchical.sv

DUT = math_adder_hierarchical
MODULE = testbench
TOPLEVEL = $(DUT)

COMPILE_ARGS += -P $(DUT).N=16
COMPILE_ARGS += -P $(DUT).C=6
#COMPILE_ARGS += -DDEBUG

TOPLEVEL_LANG := verilog
COCOTB_HDL_TIMEUNIT=1ns
COCOTB_HDL_TIMEPRECISION=1ps
include $(shell cocotb-config --makefiles)/Makefile.sim
include ../cleanall.mk
WAVES=1
